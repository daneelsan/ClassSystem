(* ::Package:: *)

BeginPackage["WolframCompiler`ClassSystem`"];


Class::usage =
	"Class[$$] represents a class object created with RegisterClass.";

RegisterClass::usage =
	"RegisterClass[cls, fields, methods] registers a class named cls used for creating object instances.";

$DemoClass::usage =
	"$DemoClass is a registered Class useful for demonstration purposes.";

$Classes::usage =
	"$Classes returns a list of names of all classes declared with RegisterClass.";

ClassInformation::usage =
	"ClassInformation[cls] returns a Class object associated with cls.";

ClassTrait::usage =
	"RegisterClass[\[Ellipsis], \"Extends\" -> ClassTrait[<|method1, \[Ellipsis]|>]] " <>
	"will use the methods found in the trait to expand the class methods.";

ObjectInstance::usage =
	"ObjectInstance[\[Ellipsis]] represents an object instance created with CreateObject.";

CreateObject::usage =
	"CreateObject[cls] creates an instance of a class cls.\n" <>
	"CreateObject[cls, st] creates an instance of a class cls with initial state st.";

ObjectInstanceQ::usage =
	"ObjectInstanceQ[obj] returns True if obj is a valid object instance, and False otherwise.";

SetData::usage =
	"SetData[obj[propName], val] sets the value of the property propName to val.";

ClassPropertiesTrait::usage =
	"ClassPropertiesTrait[<|\[Ellipsis]|>] is a ClassTrait containing methods for " <>
	"working with \"properties\", e.g. obj[\"setProperty\", propName -> val].";


Begin["`Private`"]


Needs["CompileUtilities`Error`Exceptions`"] (* for ThrowException *)
Needs["CompileUtilities`Error`Suggestions`"]
Needs["CompileUtilities`Format`"]
Needs["CompileUtilities`Reference`"]


(*******************************************************************************
	Messages
*******************************************************************************)

CreateObject::classnodef =
	"A definition for the class `1` cannot be found.";


Compile`Utilities`Class`Impl`CreateClass::def =
	"The class `1` has already been registered.";


(*******************************************************************************
	CreateObject
*******************************************************************************)

CreateObject[name_] :=
	CreateObject[name, {}];

CreateObject[name_, st_Association] :=
	CreateObject[name, Normal[st]];

CreateObject[name_, st_List] :=
	Compile`Utilities`Class`Impl`CreateObject[name, st];


(*******************************************************************************
	ObjectInstanceQ
*******************************************************************************)

ObjectInstanceQ[args__] :=
	Compile`Utilities`Class`Impl`ObjectInstanceQ[args];


(*******************************************************************************
	RegisterClass
*******************************************************************************)
(*
	The ClassBase system stores the raw data that was used to define the class.
	It might contain extra processing information, e.g. to allow compilation of 
	methods which might be stripped out to allow the class to be processed by 
	the evaluator.
*)

If[!AssociationQ[$ClassInformationAssociation],
	$ClassInformationAssociation = <||>
];


ClassInformation[name_] :=
	Lookup[
		$ClassInformationAssociation,
		name,
		Failure[
			"ClassInformation",
			<|
				"MessageTemplate" :> "The class `1` cannot be found.",
				"MessageParameters" -> {name}
			|>
		]
	];


$Classes :=
	Keys[$ClassInformationAssociation];


Options[RegisterClass] = {
	"Predicate" -> None,
	"Extends" -> None
};

RegisterClass[name_, fields_?AssociationQ, methodsIn_?AssociationQ, opts:OptionsPattern[]] :=
	RegisterClass[name, Normal[fields], methodsIn, opts];

RegisterClass[name_, fields0_?ListQ, methodsIn_?AssociationQ, opts:OptionsPattern[]] :=
	Module[{predicate, extends, fields, canonicalFields, accessors, fullMethods, class},
		(*
			Create the predicate, but only do this if Predicate is a non-system context symbol.
			This is done before checkDeclaredMethods because we need to give the predicate some
			down values, otherwise checkDeclaredMethods will throw an error.
		*)
		predicate = OptionValue[RegisterClass, {opts}, "Predicate"];
		If[predicate =!= None,
			If[!Developer`SymbolQ[predicate] || Context@@{predicate} === "System`",
				Return @ Failure[
					"RegisterClass",
					<|
						"MessageTemplate" -> "The predicate `1` must be a non-system symbol.",
						"MessageParameters" -> {predicate}
					|>
				]
			];
			definePredicate[predicate, name]
		];

		(* Statically analyze methods to see if they call down to valid functions *)
		CatchException[
			checkDeclaredMethods[name, methodsIn]
		] // If[FailureQ[#], Return[#]] &;

		If[!DuplicateFreeQ[fields0],
			Return @ Failure[
				"RegisterClass",
				<|
					"MessageTemplate" -> "Duplicate fields found in class `1`: `2`.",
					"MessageParameters" -> {name, Keys@Select[Counts[fields0], # > 1 &]}
				|>
			]
		];

		extends = OptionValue[RegisterClass, {opts}, "Extends"];
		If[None === extends,
			extends = ClassTrait[<||>]
		];
		If[MatchQ[extends, _ClassTrait | _Class],
			extends = {extends}
		];
		If[!AllTrue[extends, MatchQ[#, _ClassTrait | _Class] &],
			Return @ Failure[
				"RegisterClass",
				<|
					"MessageTemplate" -> "Invalid trait(s) passed in while creating class `1`: `2`.",
					"MessageParameters" -> {name, Select[extends, Not@*MatchQ[_ClassTrait|_Class]]}
				|>
			]
		];

		fields = Join[
			getExtendFields[extends],
			Association @ Replace[fields0, field:Except[_Rule] :> field -> Undefined, 1]
		];

		canonicalFields = canonicalizeFields[fields];
		accessors = Association @ Map[makeAccessor, Keys[canonicalFields]];

		fullMethods =
			Association[
				$baseMethods, (* <- Needs to be first, since the traits and methods override it *)
				accessors,
				getExtendMethods[extends],
				If[predicate =!= None,
					With[{predicate1 = predicate},
						"_predicate" -> Function[{}, predicate1]
					]
					,
					Nothing
				],
				methodsIn
			];

		class = Class[<|
			"name" -> name,
			"fields" -> fields,
			"methods" -> fullMethods,
			"predicate" -> predicate
		|>];
		AssociateTo[$ClassInformationAssociation, name -> class];

		Check[
			Compile`Utilities`Class`Impl`CreateClass[
				name,
				Normal @ canonicalizeMethods[fullMethods],
				Normal @ canonicalFields
			]
			,
			Return @ Failure[
				"RegisterClass",
				<|
					"MessageTemplate" :> Compile`Utilities`Class`Impl`CreateClass::def,
					"MessageParameters" -> {name}
				|>
			]
		];

		class
	];

RegisterClass[args___] :=
	Failure[
		"RegisterClass",
		<|
			"MessageTemplate" -> "Unrecognized call to RegisterClass.",
			"MessageParameters" -> {Hold[args]}
		|>
	];


$baseMethods = <|
	"toBoxes" -> Function[{self, fmt}, toBoxes[self, fmt]],
	"toString" -> Function[{self}, toString[self]],
	"fullform" -> Function[{self}, fullform[self]]
|>;


getExtendMethods[ClassTrait[x_]] :=
	x;

(* Don't include the predicate, these are not extensible *)
getExtendMethods[Class[assoc_]] :=
	Delete[assoc@"methods", Key["_predicate"]];

getExtendMethods[x_List] :=
	getExtendMethods /@ x;


getExtendFields[x_ClassTrait] :=
	<||>;

getExtendFields[Class[assoc_]] :=
	assoc@"fields";

getExtendFields[x_List] :=
	Apply[Join, getExtendFields /@ x];


makeAccessor[key_] :=
	If[StringQ[key],
		With[{camelCaseKey = ToUpperCase[StringTake[key, 1]] <> StringDrop[key, 1]},
			<|
				("get" <> camelCaseKey) -> Compile`Utilities`Class`Impl`GetData[key],
				("set" <> camelCaseKey) -> Compile`Utilities`Class`Impl`SetData[key]
			|>
		]
		,
		<||>
	];


 definePredicate[predicate_, className_] :=
	(
		predicate[obj_] :=
			ObjectInstanceQ[obj] && obj["_class"] === className;

		predicate[___] :=
			False;
	);


(*
	Check the methods and make sure that they are not calling undefined functions.
	Returns True if all checked methods are ok
*)
checkDeclaredMethods[name_, methods_] :=
	Module[{callees},
		callees =
			KeyValueMap[
				Replace[
					#2,
					{
						(*
							These are all just common patterns for methods
							More valid patterns may be used in the future, and this list would need to be updated.

							We inspect each method definition, taking care to not evaluate anything.
							If the definition is another function call, then we examine it further.
						*)

						(* get the more specific patterns out of the way first *)
						HoldPattern[Function][{___}|PatternSequence[], Verbatim[Slot][1][___]] -> Nothing,
						HoldPattern[Function][{___}|PatternSequence[], True|False|Null|None] -> Nothing,
						HoldPattern[Function][{___}|PatternSequence[], _String] -> Nothing,
						HoldPattern[Function][{___}|PatternSequence[], _Integer] -> Nothing,

						HoldPattern[Function][{self_, ___}, self_[__]] -> Nothing,
						HoldPattern[Function][{self_, ___}, self_[__][___]] -> Nothing,

						HoldPattern[Function][(x_[1] /; x===Slot)[__]] -> Nothing,
						HoldPattern[Function][(x_[1] /; x===Slot)[__][___]] -> Nothing,

						HoldPattern[Function][{Typed[self_, _], ___}, self_[__]] -> Nothing,
						HoldPattern[Function][{Typed[self_, _], ___}, self_[__][___]] -> Nothing,

						(* anything left with this structure is further examined *)
						HoldPattern[Function][{___}|PatternSequence[], callee_[___][___]] :> (#1 -> Hold[callee]),
						HoldPattern[Function][{___}|PatternSequence[], callee_[___]] :> (#1 -> Hold[callee]),

						x_ :> ThrowException[{"Unrecognized pattern `3` in the method \"`2`\" of class `1`.", name, #1, x}]
					}
				] &,
				canonicalizeMethods[methods]
			];
		AllTrue[callees, validateFunctionCall[name, #] &]
	];


canonicalizeMethods[methods_] :=
	Association @ KeyValueMap[
		#1 -> canonicalizeMethod[#2] &,
		methods
	];


canonicalizeMethod[TypeFramework`MetaData[_]@f_] :=
	canonicalizeMethod[f];

canonicalizeMethod[Typed[_]@f_] :=
	canonicalizeMethod[f];

canonicalizeMethod[f_] :=
	ReplaceAll[f, IfCompiled[comp_, eval_] :> eval];


canonicalizeFields[fields_] :=
	Association @ KeyValueMap[
		Replace[#1, Typed[field_, type_] :> field] -> #2 &,
		fields
	];


(*
	Examine whether this is valid function call.
	There are some cases recognized:
		1. A System` function call (we assume calling a System` function is correct)
		2. A call to a symbol that has DownValues (we assume calling a symbol with DownValues is correct)
		3. A call to a symbol that has OwnValues (we could dig down further to see if the OwnValues needs examining, etc.)
		4. A Internal`WithLocalSettings call or RuntimeTools`ProfileDataWrapper call (probably from static analysis tools)
*)
validateFunctionCall[className_, methodName_ -> heldCalleeIn_] :=
	Module[{heldCallee, heldHead},
		heldCallee = canonicalizeMethod[heldCalleeIn];
		heldHead = Extract[heldCallee, {1, 0}, Hold];
		Which[
			heldHead === Hold[Symbol] && (Context@@heldCallee === "System`"),
				True
			,
			heldHead === Hold[Symbol] && (DownValues@@heldCallee =!= {}),
				True
			,
			heldHead === Hold[Symbol] && (OwnValues@@heldCallee =!= {}),
				True
			,
			heldCallee === Hold[Internal`WithLocalSettings] || heldCallee === Hold[RuntimeTools`ProfileDataWrapper],
				True
			,
			True,
				ThrowException[{
					"Cannot find function definition for `3` in the method \"`2`\" of class `1`.",
					className,
					methodName,
					heldCallee
				}]
		]
	];


(*******************************************************************************
	ClassErrorHandler
*******************************************************************************)

Unprotect[Compile`Utilities`Class`Impl`ClassErrorHandler];

Compile`Utilities`Class`Impl`ClassErrorHandler["noname", key_, className_] :=
	ThrowException[{
		"Cannot access `1` for class `2`. Maybe you meant to use `3`",
		key,
		SymbolName[className],
		SuggestionsString[
			key,
			Keys @ Catenate @ Lookup[Compile`Utilities`Class`Impl`ClassInformation[className], {"Fields", "Methods"}],
			"FormattingFunction" -> formatSuggestion,
			"Prefix" -> "",
			"ConnectingWord" -> "or "
		]
	}];

Protect[Compile`Utilities`Class`Impl`ClassErrorHandler];


formatSuggestion[x_String] :=
	"\"" <> x <> "\"";

formatSuggestion[x_] :=
	formatSuggestion[ToString[x]];


(*******************************************************************************
	Class SubValues
*******************************************************************************)

Class[assoc_Association][key_] /; KeyExistsQ[assoc, key] :=
	assoc[key];


(*******************************************************************************
	Class Boxes
*******************************************************************************)

$classIcon :=
	Graphics[
		Text @ Style[
			"CLS",
			GrayLevel[0.7],
			Bold,
			1.1*GetFormattingValue["FontCapHeight"]/GetFormattingValue[Magnification]
		],
		$FormatingGraphicsOptions
	];


Class /: MakeBoxes[cls:Class[assoc_], fmt_] :=
	BoxForm`ArrangeSummaryBox[
		"Class",
		cls,
		$classIcon,
		{
			BoxForm`SummaryItem[{"name: ", ToString[assoc@"name"]}],
			If[assoc@"predicate" =!= None,
				BoxForm`SummaryItem[{"predicate: ", assoc@"predicate"}]
				,
				Nothing
			],
			BoxForm`SummaryItem[{"fields: ", Length[assoc@"fields"]}],
			BoxForm`SummaryItem[{"methods: ", Length[assoc@"methods"]}]
		},
		{
			BoxForm`SummaryItem[{"name: ", ToString[assoc@"name"]}],
			If[assoc@"predicate" =!= None,
				BoxForm`SummaryItem[{"predicate: ", assoc@"predicate"}]
				,
				Nothing
			],
			BoxForm`SummaryItem[{"fields: ", assoc@"fields"}],
			BoxForm`SummaryItem[{"methods: ", assoc@"methods"}]
		},
		fmt,
		"Interpretable" -> False
	];


(*******************************************************************************
	ObjectInstance Boxes
*******************************************************************************)

$objectInstanceIcon :=
	Graphics[
		Text @ Style[
			"OBJ",
			GrayLevel[0.7],
			Bold, 
			1.2*GetFormattingValue["FontCapHeight"]/GetFormattingValue[Magnification]
		],
		$FormatingGraphicsOptions
	];


Unprotect[ObjectInstance];

ObjectInstance /: MakeBoxes[obj_ObjectInstance, fmt_] :=
	If[ObjectInstanceQ[obj],
		obj["toBoxes", fmt]
		,
		With[{obj1 = Apply["ObjectInstance", obj]},
			MakeBoxes[obj1, fmt]
		]
	];

Protect[ObjectInstance];


toBoxes[inst_?ObjectInstanceQ, fmt_] :=
	BoxForm`ArrangeSummaryBox[
		"ObjectInstance",
		inst,
		$objectInstanceIcon,
		{
			CompileInformationPanel[inst["_class"], Normal[inst["_state"]]]
		},
		{
			BoxForm`SummaryItem[{"methods: ", inst["_methods"]}]
		},
		fmt,
		"Interpretable" -> False
	];


toString[inst_?ObjectInstanceQ] :=
	StringJoin[
		ToString[inst["_class"]],
		"[",
		ToString[inst["_state"]],
		"]"
	];


fullform[inst_?ObjectInstanceQ] :=
	inst["_class"][];


(*******************************************************************************
	$DemoClass
*******************************************************************************)

RegisterClass[
	$DemoClass,
	<|"_data" -> 0|>,
	<|
		"increment" -> Function[{self}, self["set_data", self["get_data"] + 1]],
		"decrement" -> Function[{self}, self["set_data", self["get_data"] - 1]]
	|>
];


(*******************************************************************************
	ClassPropertiesTrait
*******************************************************************************)

(*
	Slightly strange name to avoid a collision with a System` context symbol
	called getProperty introduced into the Cloud.
*)
getProperty1[self_, prop_] :=
	self["properties"]["lookup", prop];

getProperty1[self_, prop_, default_] :=
	self["properties"]["lookup", prop, default]


ClassPropertiesTrait =
	ClassTrait[<|
		"initializeProperties" ->
			Typed[
				{Compile`Self} -> "Null"
			] @
			Function[{self},
				self["setProperties", CreateReference[<||>]];
			],
		"getProperties" -> Function[{self},
			 (* overload the default accessor *)
			self["properties"]["get"]
		],
		"getProperty" -> (getProperty1[##]&),
		"removeProperty" -> Function[{self, prop},
			self["properties"]["keyDropFrom", prop]
		],
		"setProperty" -> Function[{self, kv},
			self["properties"]["associateTo", kv]
		],
		"joinProperties" -> Function[{self, other},
			self["setProperties", self["properties"]["join", other]]
		],
		"cloneProperties" ->
			Typed[
				{Compile`Self, Compile`Self} -> "Null"
			] @
			Function[{self, obj},
				self["setProperties", obj["properties"]["clone"]];
			],
		"hasProperty" -> Function[{self, key},
			self["properties"]["keyExistsQ", key]
		],
		"clonedProperties" -> Function[{self},
			CreateReference[
				Map[
					Function[{val},
						If[ReferenceQ[val],
							val["clone"]
							,
							val
						]
					],
					self["properties"]["get"]
				]
			]
		]
	|>];


End[];


EndPackage[];
