(* ::Package:: *)

ClearAll[DataCheck, $ImportData];
$ImportData = True;
DataCheck[cmd_, file_String] :=
  DataCheck[cmd, file, Automatic];
DataCheck[cmd_, file_String, False | None] :=
  DataCheck[cmd, file, "./"];
DataCheck[cmd_, file_String, Automatic] :=
  DataCheck[cmd, file,
    If[DirectoryQ@$DataDirectory, $DataDirectory, FileNameJoin[{
      If[$Notebooks, NotebookDirectory[], Directory[] ], "data"}]
    ]
  ];
DataCheck[cmd_, file_String, dir_String?DirectoryQ] :=
  Module[{data, loc},
    loc = FileNameJoin[{dir, file}];
    If[$ImportData && FileExistsQ[loc],
      data = Import@loc,
      data = cmd; Export[loc, data]
    ];
    Return[data]
  ];
SetAttributes[DataCheck, {HoldFirst}]


ClearAll[volumesTable];
volumesTable[comp0_,{kvI_,kvF_}] :=
  Module[{simplifyMesh, kvs, comp, replaceVols, polyPlot, ac},
    simplifyMesh[mesh_MeshRegion] :=
      Block[{coord, cells},
        coord = Map[First]@KeySort@KeyMap[Rationalize]@PositionIndex[MeshCoordinates@mesh];
        cells = Sort@Map[Sort, MeshCells[mesh, 2] /. Map[Reverse]@Normal[coord], {2}];
        MeshRegion[Keys@coord, cells /. Normal[First /@ PositionIndex@Keys@coord]]
      ];
    kvs = KeyMap[Apply[{simplifyMesh@#1, #2} &]]@
      Join[AssociationFlatten[kvI, 1], AssociationFlatten[kvF, 1]];
    comp = MapAt[simplifyMesh, SortBy[First] /@ comp0, {All, All, 1}];
    replaceVols[entries_] := Block[{vol,var,elim,newVar},
      vol = Values[entries];
      var= MapIndexed[Table[\[FormalA][i,First@#2], {i,Length[#1]}] &, vol];
      elim= First@Solve[Eliminate[var == vol, Variables@vol]];
      newVar= MapIndexed[ #1 -> FromLetterNumber[First@#2] &, Variables[var/.elim] ];
      Association /@ MapThread[Rule, {Keys[entries], var/.elim/.newVar}, 2]
    ];
    ac = GroupBy[comp, Map[First], 
      KeyValueMap[Thread[#1->#2]&]@*KeyMap[Map@Last]@*AssociationMap[
        replaceVols[#1/.Normal[kvs]] &]
    ];
    ac = KeyMap[Transpose]@Association[
      KeyValueMap[{#1,Map[Last]@First@MinimalBy[#2,LeafCount]} -> Sort[Map[Values] /@ Keys[#2] ] &,
      ac]
    ];
    ac = Map[KeyValueMap[
        MapThread[MapAt[Subscript[First@First[#],Row[Map[Last,#],","]]&,-1]@*Append,{#1,#2}]&
      ]@GroupBy[#1, Map[Most] -> Map[Last], Transpose] &,
      Map[DeleteCases[Subscript[$ExtremalPerfectMatchingVar, _]], ac, {3}]
    ]
]


ClearAll[exportRowsToPages];
exportRowsToPages[filename_String, vols_, n : _Integer?Positive : 32] :=
  Module[{strP, files},
    strP = StringDelete[filename, "." ~~ FileExtension[filename] ~~ EndOfString];
    files = If[Length[vols] <= n, 
      Export[filename, Column@vols],
      MapIndexed[
        Export[strP <> "_part" <> IntegerString[First@#2, 10, 2] <> ".pdf", Column@#1] &,
        Partition[vols, n, n, {1, 1}, {}]
      ]
    ];
    If[$OperatingSystem == "Unix" && Length[files] > 1,
      Run["pdftk " <> StringRiffle[files, " "] <> " cat output " <> filename];
      DeleteFile /@ files;
    ];
  ];


ClearAll[massiveFieldsFrom]
massiveFieldsFrom[x_] := FieldCases@Select[FieldProducts@x, Length[#]==2 &];


ClearAll[PolytopeMutation];
PolytopeMutation[pt_, vec_] :=
  Module[{monodromy, pqwebred, split, l, final},
    monodromy[{p_, q_}] := {{1 - p q, p^2}, {-q^2, 1 + p q}};
    pqwebred = RotationTransform[-Pi / 2][#2 - #1]& @@@ Partition[
      Last @ PolytopeVertices[pt], 2, 1, {1, 1}];
    split = GroupBy[NestWhile[RotateLeft, 
      AssociationMap[Mod[(ArcTan @@#) - ArcTan @@ (vec), 2 Pi, -Pi]&, pqwebred], 
      Not @* MatchQ[{___?Negative, ___?PossibleZeroQ, ___?Positive}] @* Values], 
      Sign, 
      Map[Splice@Table[#, Count[pqwebred,#] ] &] @* Keys];
    final = Join[{-l vec}, split[-1], 
      Delete[split[0], FirstPosition[split[0], vec] ], 
      (monodromy[vec] . # &) /@ split[1]
    ];
    DeleteCases[final /. First[Solve[Total[final] == {0, 0}, l], {}], {0, 0}]
  ];


ClearAll[ZigZagDataGrid];
ZigZagDataGrid[w_?ToricPotentialQ] := 
   Module[{td,zz,var,gb,red},
   var=FieldCases@w;
	gb=GroebnerBasis[Abelianize@FTerms@w,var];
	red=If[PossibleZeroQ@Last@PolynomialReduce[Abelianize@Total@#,gb,var],
		Style[#,Red],
		Simplify@Total@#
	] &;
	{td,zz}={PolytopePlot[ToricDiagram[w],"PolytopeCellLabel"->Automatic],ZigZagData[w]};
	Grid[Join[{{Item[td,Alignment->Center]},Splice@Table[{SpanFromAbove},Length@zz-1]},Values@MapAt[red,zz,{All,4}],2],Frame->All]
];

ClearAll[GeneratorMassRedefinitions];

GeneratorMassRedefinitions[
    w_?ToricPotentialQ, 
    gen : {$GeneratorVars[_]..}, 
    charge : {_Integer, _Integer}] :=
  Module[{gen0, chRules, latt, a, redefData},
    gen0 = ToGeneratorVariableRules@GaugeInvariantMesons[QuiverFromFields@w, 7];
    chRules = Association@MapAt[
      First@*Select[ Not@*FreeQ[Alternatives@@gen] ], 
      ReplaceAll[gen0]@Normal@GeneratorsLattice[w], {All, 2}
    ];
    latt = Keys @ chRules;
    redefData = MapIndexed[
      p |-> (Map[\[Mu]^a[#] chRules[#] /. Solve[(a[#] charge + # == p && a[#] >= 0), Integers]&, latt]), 
      Keys@chRules
    ];
    Normal@DeleteCases[_Times]@Association@MapIndexed[
      chRules[[First@#2]] -> #1 . Array[$RedefinitionVars[[First@#2]], Length@#1] &, 
      Map[Cases[l_List :> First @ l], redefData]
    ]
  ]
