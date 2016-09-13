(* ::Package:: *)

(* ::Code::Bold:: *)
Clear[INDefine,INOptions,IN,FE,SE,FEI,SEI];
(*
Defines an interval
*)
INDefine[options___]:=
	Block[{fe,se,fei,sei},
		{fe,se,fei,sei}={firstExtreme,secondExtreme,feIncluded,seIncluded}/.{options}/.INOptions[INDefine];
		IN[FE[fe],SE[se],FEI[fei],SEI[sei]]
	];

(*Options for Interval definition*)
(*DO NOT CHANGE THIS!, BECAUSE OTHER FUNCTIONS DEPENDS OF IT*)
INOptions[INDefine]={firstExtreme->0.0,secondExtreme->0.0,feIncluded->"[",seIncluded->"]"};

Clear[INDefineShort];
(*
Defines an interval in a short way
*)
INDefineShort[fei_,fe_,se_,sei_]:=IN[FE[fe],SE[se],FEI[fei],SEI[sei]]

(* It orders the stremes of the interval *)
Clear[INNormalize];
SetAttributes[INNormalize,HoldFirst];
INNormalize[in_]:=
	Block[{fe=INGetFE[in],se=INGetSE[in],fei=INGetFEI[in],sei=INGetSEI[in]},
		If[fe>se,
			INSetFE[in,se];
			INSetSE[in,fe];
			INSetFEI[in,If[sei=="]","[","("]];
			INSetSEI[in,If[fei=="[","]",")"]];
		]
	];

(*
Getters
*)
Clear[INGetFE,INGetSE,INGetFEI,INGetSEI];
INGetFE[IN[FE[fe_],se_,fei_,sei_]]:=fe;
INGetSE[IN[fe_,SE[se_],fei_,sei_]]:=se;
INGetFEI[IN[fe_,se_,FEI[fei_],sei_]]:=fei;
INGetSEI[IN[fe_,se_,fei_,SEI[sei_]]]:=sei;

(*
Setters
*)
Clear[INSetFE,INSetSE,INSetFEI,INSetSEI];
SetAttributes[{INSetFE,INSetSE,INSetFEI,INSetSEI},{HoldFirst}];
INSetFE[int_,newfe_]:=(int[[1,1]]=newfe;);
INSetSE[int_,newse_]:=(int[[2,1]]=newse;);
INSetFEI[int_,newfei_]:=(int[[3,1]]=newfei;);
INSetSEI[int_,newsei_]:=(int[[4,1]]=newsei;);

(* It multiplicates the interval by a constant *)
Clear[INByConstant];
SetAttributes[INByConstant,HoldFirst];
INByConstant[in_,k_]:=
	Block[{aux},
		If[k<0,
			aux=INGetFE[in];
			INSetFE[in,k*INGetSE[in]];
			INSetSE[in,k*aux];,
			INSetFE[in,k*INGetFE[in]];
			INSetSE[in,k*INGetSE[in]];
		]
	];

(* It verifies if the interval is empty *)
Clear[INEmptyQ];
INEmptyQ[IN[FE[fe_],SE[se_],FEI[fei_],SEI[sei_]]]:=If[fe==0&&se==0&&fei=="("&&sei==")",True,False];

(* It returns the union of two intervals *)
Clear[INUnion];
INUnion[IN[FE[a_],SE[b_],FEI[ai_],SEI[bi_]],IN[FE[c_],SE[d_],FEI[ci_],SEI[di_]]]:=
	Block[{fe,se,fei,sei},
		If[a<c,
			fe=a;
			fei=ai;,
			If[a>c,
				fe=c;
				fei=ci;,
				fe=a;
				fei=If[ai==ci,ai,"("];
			]
		];
		If[d<b,
			se=b;
			sei=bi;,
			If[d>b,
				se=d;
				sei=di;,
				se=b;
				sei=If[bi==di,bi,")"];
			]
		];
		INDefine[firstExtreme->fe,secondExtreme->se,feIncluded->fei,seIncluded->sei]
	];
(* It returns the intersection of two intervals *)
Clear[INIntersection];
INIntersection[in1_,in2_]:=
	Block[{fe,fei,se,sei,a=INGetFE[in1],b=INGetSE[in1],c=INGetFE[in2],d=INGetSE[in2],p1=INGetFEI[in1],p2=INGetSEI[in1],p3=INGetFEI[in2],p4=INGetSEI[in2]},
		Which[
			a==c&&b==d,
			Which[
				a==b,
				If[p1=="["&&p3=="["&&p2=="]"&&p4=="]",
					INDefine[firstExtreme->a,secondExtreme->a],
					INDefine[feIncluded->"(",seIncluded->")"]
				],
				p1=="["&&p3=="[",
				If[p2=="]"&&p4=="]",
					INDefine[firstExtreme->a,secondExtreme->b],
					INDefine[firstExtreme->a,secondExtreme->b,seIncluded->")"]
				],
				p2=="]"&&p4=="]",
				INDefine[firstExtreme->a,secondExtreme->b,feIncluded->"("],
				True,
				INDefine[firstExtreme->a,secondExtreme->b,feIncluded->"(",seIncluded->")"]
			],
			a<c&&b<=c,
			If[b==c,
				If[p2=="]"&&p3=="[",
					INDefine[firstExtreme->b,secondExtreme->b],
					INDefine[feIncluded->"(",seIncluded->")"]
				],
				INDefine[feIncluded->"(",seIncluded->")"]
			],
			a<=c&&b<d,
			If[a==c,
				If[p1=="["&&p3=="[",
					INDefine[firstExtreme->a,secondExtreme->b,seIncluded->p2],
					INDefine[firstExtreme->a,secondExtreme->b,feIncluded->"(",seIncluded->p2]
				],
				INDefine[firstExtreme->c,secondExtreme->b,feIncluded->p3,seIncluded->p2]
			],
			a<c&&b==d,
			INDefine[firstExtreme->c,secondExtreme->b,feIncluded->p3,seIncluded->If[p2==p4,p2,")"]],
			a<=c&&b>d,
			If[a==c,
				If[p1=="["&&p3=="[",
					INDefine[firstExtreme->a,secondExtreme->d,seIncluded->p4],
					INDefine[firstExtreme->a,secondExtreme->d,feIncluded->"(",seIncluded->p4]
				],
				INDefine[firstExtreme->c,secondExtreme->d,feIncluded->p3,seIncluded->p4]
			],
			a>c&&b<=d,
			If[b==d,
				If[p2=="]"&&p4=="]",
					INDefine[firstExtreme->a,secondExtreme->b,feIncluded->p1],
					INDefine[firstExtreme->a,secondExtreme->b,feIncluded->p1,seIncluded->")"]
				],
				INDefine[firstExtreme->a,secondExtreme->b,feIncluded->p1,seIncluded->p2]						
			],
			a<=d&&b>d,
			If[a==d,
				If[p1=="["&&p4=="]",
					INDefine[firstExtreme->a,secondExtreme->a],
					INDefine[feIncluded->"(",seIncluded->")"]
				],
				INDefine[firstExtreme->a,secondExtreme->d,feIncluded->p1,seIncluded->p4]										
			],
			True,
			INDefine[feIncluded->"(",seIncluded->")"]
		]
	];

(* It unies a list of magnitude intervals *)
Clear[INUnionList];
INUnionList[mis_]:=
	Block[{aux,res,rest,i,mi},
		If[Length[mis]==1,Return[mis[[1]]]];
		res=First[mis];
		rest=Rest[mis];
		While[True,
			For[i=1,i<=Length[rest],i++,
				mi=rest[[i]];
				If[!INEmptyQ[INIntersection[res,mi]],
					res=INUnion[res,mi];
					rest=Delete[rest,i];
					i=0;
				];
			];
			If[Length[rest]>0,
				aux=res;res=First[rest];
				rest=Rest[rest];
				rest=Append[rest,aux];,
				Break[];
			];
		];
		res
	];

(*
It negates the interval
*)
Clear[INNegation];
SetAttributes[{INNegation},{HoldFirst}];
INNegation[in_]:=
	Block[{fe=INGetFE[in],se=INGetSE[in],fei=INGetFEI[in],sei=INGetSEI[in]},
		IN[FE[-se],SE[-fe],FEI[If[sei=="]","[","("]],SEI[If[fei=="[","]",")"]]]
	];

(* Addition of two intervals *)
Clear[INAddition];
INAddition[IN[FE[fe1_],SE[se1_],FEI[fei1_],SEI[sei1_]],IN[FE[fe2_],SE[se2_],FEI[fei2_],SEI[sei2_]]]:=
	IN[FE[fe1+fe2],SE[se1+se2],FEI[If[fei1==fei2,fei1,"("]],SEI[If[sei1==sei2,sei1,")"]]];

(* Product of two intervals *)
Clear[INProduct];
INProduct[IN[FE[fe1_],SE[se1_],FEI[fei1_],SEI[sei1_]],IN[FE[fe2_],SE[se2_],FEI[fei2_],SEI[sei2_]]]:=
	IN[FE[fe1*fe2],SE[se1*se2],FEI[If[fei1==fei2,fei1,"("]],SEI[If[sei1==sei2,sei1,")"]]];

(* Subtraction of two intervals *)
Clear[INSubtraction];
INSubtraction[IN[FE[fe1_],SE[se1_],FEI[fei1_],SEI[sei1_]],IN[FE[fe2_],SE[se2_],FEI[fei2_],SEI[sei2_]]]:=
	IN[FE[fe1-se2],SE[se1-fe2],FEI[If[fei1=="["&&sei2=="]",fei1,"("]],SEI[If[sei1=="]"&&fei2=="[",sei1,")"]]];

(* Division of two intervals *)
Clear[INDivision];
INDivision[IN[FE[fe1_],SE[se1_],FEI[fei1_],SEI[sei1_]],IN[FE[fe2_],SE[se2_],FEI[fei2_],SEI[sei2_]]]:=
	If[se2==0||fe2==0,
		Print["Division por cero!"],
		IN[FE[fe1/se2],SE[se1/fe2],FEI[If[fei1=="["&&sei2=="]",fei1,"("]],SEI[If[sei1=="]"&&fei2=="[",sei1,")"]]]
	];

(* It prints the interval *)
Clear[INPrint];
INPrint[in_]:=Print[INStringForm[in]];

(* It returns the string representation of the interval *)
Clear[INStringForm];
INStringForm[IN[FE[fe_],SE[se_],FEI[fei_],SEI[sei_]]]:=StringJoin[fei,ToString[fe],",",ToString[se],sei];


(* ::Code::Bold:: *)
(*It normalizes an Angle Interval*)
Clear[AINormalize];
SetAttributes[AINormalize,HoldFirst];
AINormalize[ai_]:=
	Block[{fe=INGetFE[ai],se=INGetSE[ai]},
		If[fe>360||fe<0,INSetFE[ai,Mod[fe,360]];fe=INGetFE[ai]];
		If[se>360||se<0,INSetSE[ai,Mod[se,360]];se=INGetSE[ai]];
		If[fe==360&&se!=360,INSetFE[ai,0]];
		If[se==0&&fe!=0,INSetSE[ai,360]]
		(*ai*)
	];

(*It adds two angle intervals*)
Clear[AIAddition];
AIAddition[ai1_,ai2_]:=
	Block[{res=INAddition[ai1,ai2]},
		AINormalize[res];
		res
	];

(*It subtracts two angle intervals*)
Clear[AISubtraction];
AISubtraction[ai1_,ai2_]:=
	Block[{res=INSubtraction[ai1,ai2]},
		AINormalize[res];
		res
	];

Clear[AIAdd180];
(*It adds 180 degrees to an angle interval*)
AIAdd180[ai_]:=
	Block[{aux,res},
		aux=INDefine[firstExtreme->180,secondExtreme->180,feIncluded->INGetFEI[ai],seIncluded->INGetSEI[ai]];
		res=AIAddition[ai,aux];
		AINormalize[res];
		res
	];

(**It verifies if an angle interval ranges from 0 to 360 degrees*)
Clear[AIVerifyCase0360Q];
AIVerifyCase0360Q[ai_]:=
	If[INGetFE[ai]==0.0&&INGetSE[ai]==360.0&&INGetFEI[ai]=="["&&INGetSEI[ai]=="]",
		True,False
	];

(*It unies a list of angle intervals *)
Clear[AIUnionList];
AIUnionList[res_]:=
	Block[{aux,ai1,ai2,tres,rest,i,j},
		If[Length[res]==1,Return[res[[1]]]];
		If[AIVerifyCase0360ListQ[res],tres=INDefine[firstExtreme->0,secondExtreme->360];Return[tres]];
		tres=First[res];
		rest=Rest[res];
		While[True,
			For[i=1,i<=Length[rest],i++,
				ai1=tres;
				ai2=rest[[i]];
				If[(INGetSE[ai1]==INGetFE[ai2]&&INGetSEI[ai1]==")"&&INGetFEI[ai2]=="[")||(INGetSE[ai1]==360&&INGetFE[ai2]==0&&INGetSEI[ai1]=="]"&&INGetFEI[ai2]=="["),
					INSetSE[ai1,INGetSE[ai2]];
					INSetSEI[ai1,INGetSEI[ai2]];
					tres=ai1;
					rest=Delete[rest,i];i=0;
					Break[];
				];
			];
			If[Length[rest]==0,Break[]];
			For[j=1,j<=Length[rest],j++,
				ai1=tres;
				ai2=rest[[j]];
				If[(INGetFE[ai1]==INGetSE[ai2]&&INGetSEI[ai2]==")"&&INGetFEI[ai1]=="[")||(INGetFE[ai1]==0&&INGetSE[ai2]==360&&INGetSEI[ai2]=="]"&&INGetFEI[ai1]=="["),
					INSetFE[ai1,INGetFE[ai2]];
					INSetFEI[ai1,INGetFEI[ai2]];
					tres=ai1;
					rest=Delete[rest,j];j=0;
					Break[];
				];
			];
			If[Length[rest]>0,
				aux=tres;tres=First[rest];rest=Rest[rest];
				rest=Append[rest,aux];,
				Break[];
			];
		];
		tres
	];

(*It checks if a list of angle intervals range over the 360 degrees*)
Clear[AIVerifyCase0360ListQ];
AIVerifyCase0360ListQ[lais_]:=
	Block[{ais,i,c=0},
		ais=lais;
		For[i=1,i<=Length[ais],i++,
			If[INGetFE[ais[[i]]]==0.0&&INGetSE[ais[[i]]]==90.0&&INGetFEI[ais[[i]]]=="["&&INGetSEI[ais[[i]]]==")",
				c++;Break[];
			];
		];
		For[i=1,i<=Length[ais],i++,
			If[INGetFE[ais[[i]]]==90.0&&INGetSE[ais[[i]]]==180.0&&INGetFEI[ais[[i]]]=="["&&INGetSEI[ais[[i]]]==")",
				c++;Break[];
			];
		];
		For[i=1,i<=Length[ais],i++,
			If[INGetFE[ais[[i]]]==180.0&&INGetSE[ais[[i]]]==270.0&&INGetFEI[ais[[i]]]=="["&&INGetSEI[ais[[i]]]==")",
				c++;Break[];
			];
		];
		For[i=1,i<=Length[ais],i++,
			If[INGetFE[ais[[i]]]==270.0&&INGetSE[ais[[i]]]==360.0&&INGetFEI[ais[[i]]]=="["&&INGetSEI[ais[[i]]]=="]",
				c++;Break[];
			];
		];
		If[c==4,
			True,
			False
		]
	];


(* ::Code::Bold:: *)
Clear[CFDefine,CFOptions,CFGetMI,CFGetAI,CFSetMI,CFSetAI];
(*It defines a complex fan*)
CFDefine[options___]:=
	Block[{mi,ai},
		{mi,ai}={magnitudeInterval,angleInterval}/.{options}/.CFOptions[CFDefine];
		INNormalize[mi];
		AINormalize[ai];
		CF[mi,ai]
	];

(*Options for the complex fan definition*)
CFOptions[CFDefine]={magnitudeInterval->INDefine[],angleInterval->INDefine[]};

Clear[CFDefineShort,MI,AI];
(*It defines a complex fan in a short way*)
CFDefineShort[MI[fei1_,fe1_,se1_,sei1_],AI[fei2_,fe2_,se2_,sei2_]]:=
	Block[{mi=INDefineShort[fei1,fe1,se1,sei1],ai=INDefineShort[fei2,fe2,se2,sei2]},
		INNormalize[mi];
		AINormalize[ai];
		CF[mi,ai]
	];

(* Getters *)
CFGetMI[CF[mi_,ai_]]:=mi;
CFGetAI[CF[mi_,ai_]]:=ai;

(* Setters *)
SetAttributes[{CFSetMI,CFSetAI},HoldFirst];
CFSetMI[cf_,newmi_]:=(INNormalize[newmi];cf[[1]]=newmi;);
CFSetAI[cf_,newai_]:=(AINormalize[newai];cf[[2]]=newai;);

(* It negates a Complex Fan *)
Clear[CFNegation];
CFNegation[cf_]:=
	Block[{mi,ai,res},
		mi=CFGetMI[cf];
		ai=AIAdd180[CFGetAI[cf]];
		CFDefine[magnitudeInterval->mi,angleInterval->ai]
	];

(* It calculates the product of two complex fan *)
Clear[CFProduct];
CFProduct[cf1_,cf2_]:=
	Block[{mi1=CFGetMI[cf1],mi2=CFGetMI[cf2],ai1=CFGetAI[cf1],ai2=CFGetAI[cf2],newmi,newai,res},
		newmi=INProduct[mi1,mi2];
		newai=AIAddition[ai1,ai2];
		res=CFDefine[magnitudeInterval->newmi,angleInterval->newai];
		res
	];

(* It calculates the division of two complex fan *)
Clear[CFDivision];
CFDivision[cf1_,cf2_]:=
	Block[{mi1=CFGetMI[cf1],mi2=CFGetMI[cf2],ai1=CFGetAI[cf1],ai2=CFGetAI[cf2],newmi,newai,res},
		newmi=INDivision[mi1,mi2];
		newai=AISubtraction[ai1,ai2];
		res=CFDefine[magnitudeInterval->newmi,angleInterval->newai];
		res
	];

(* It calculates the division of two complex fan *)
Clear[CFSubtraction];
CFSubtraction[cf1_,cf2_]:=
	Block[{newcf2,res},
		newcf2=CFNegation[cf2];
		res=CFAddition[cf1,newcf2];
		res
	];

(* Addition of two complex fans *)
Clear[CFAddition];
CFAddition[cf1_,cf2_]:=
	Block[{inters,ptotal,paux,acf1,acf2,total,res,i,j,k,rot1,rot2,caso,aux,auxai,mi1,mi2,ai1,ai2,V1,V2,pcf1,pcf2,rotation},
		ai1=CFGetAI[cf1];
		ai2=CFGetAI[cf2];
		acf1=cf1;
		acf2=cf2;
		(* asegurar que alfa1 sea cero *)
		rotation = INGetFE[ai1];
		If[rotation!=0,
			INSetFE[ai1,INGetFE[ai1]-rotation];
			INSetSE[ai1,INGetSE[ai1]-rotation];
			INSetFE[ai2,INGetFE[ai2]-rotation];
			INSetSE[ai2,INGetSE[ai2]-rotation];
			AINormalize[ai1];
			AINormalize[ai2];
			CFSetAI[acf1,ai1];
			CFSetAI[acf2,ai2];
		];
		(* particionar ambos complex fan *)
		pcf1 = CFPart[acf1];
		pcf2 = CFPart[acf2];
		res = {};
		(* addition according the diferent cases *)
		
		k=1;
		For[i=1,i<=Length[pcf1],i++,
			For[j=1,j<=Length[pcf2],j++,
				V1=pcf1[[i]];
				V2=pcf2[[j]];
				mi1=CFGetMI[V1];
				mi2=CFGetMI[V2];
				ai1=CFGetAI[V1];
				ai2=CFGetAI[V2];
				(* ensuring that Va1 will be zero*)
				rot1=INGetFE[ai1];
				If[rot1!=0,
					INSetFE[ai1,INGetFE[ai1]-rot1];
					INSetSE[ai1,INGetSE[ai1]-rot1];
					INSetFE[ai2,INGetFE[ai2]-rot1];
					INSetSE[ai2,INGetSE[ai2]-rot1];
					AINormalize[ai1];
					AINormalize[ai2];
					CFSetAI[V1,ai1];
					CFSetAI[V2,ai2];
				];
				caso=CFVerifyCase[INGetFE[CFGetAI[V2]],INGetSE[CFGetAI[V2]]];	
				(*partial addition according to case*)
				Which[
					caso==1,
					aux=CFAdditionCase1[V1,V2],
					caso==2,
					aux=CFAdditionCase2[V1,V2],
					caso==3,
					aux=CFAdditionCase3[V1,V2],
					True,
					(* V1 esta en el 1er cuadrante y V2 en el 4to cuadrante *)
					ai1=CFGetAI[V1];
					ai2=CFGetAI[V2];
					rot2 = INGetFE[ai2];
					INSetFE[ai1,INGetFE[ai1]-rot2];
					INSetSE[ai1,INGetSE[ai1]-rot2];
					INSetFE[ai2,INGetFE[ai2]-rot2];
					INSetSE[ai2,INGetSE[ai2]-rot2];
					AINormalize[ai1];
					AINormalize[ai2];
					CFSetAI[V1,ai1];
					CFSetAI[V2,ai2];
					aux=CFAdditionCase2[V2,V1];
					auxai=CFGetAI[aux];
					If[!AIVerifyCase0360Q[auxai],
						INSetFE[auxai,INGetFE[auxai]+rot2];
						INSetSE[auxai,INGetSE[auxai]+rot2];
						AINormalize[auxai];
						CFSetAI[aux,auxai];
					];
				];
				auxai=CFGetAI[aux];
				If[rot1!=0&&!AIVerifyCase0360Q[auxai],
					INSetFE[auxai,INGetFE[auxai]+rot1];
					INSetSE[auxai,INGetSE[auxai]+rot1];
					AINormalize[auxai];
					CFSetAI[aux,auxai];
				];
				res=Append[res,aux];
				k++;
			];
		];
		total=CFUnionRes[res];
		ai1=CFGetAI[total];
		If[rotation!=0&&!AIVerifyCase0360Q[ai1],
			INSetFE[ai1,INGetFE[ai1]+rotation];
			INSetSE[ai1,INGetSE[ai1]+rotation];
			AINormalize[ai1];
			CFSetAI[total,ai1];
		];
		total
	];

(* It unies all the partial results *)
Clear[CFUnionRes];
CFUnionRes[acf_]:=
	Block[{mis,ais,mi,ai,aux1,aux2},
		mis=Table[acf[[i,1]],{i,1,Length[acf]}];
		(*ais=Table[acf[[i,2]],{i,1,Length[acf]}];*)
		mi=INUnionList[mis];
		ai=CFUnionAIs[acf];
		CFDefine[magnitudeInterval->mi,angleInterval->ai]
	];

(* It unies the angle intervals *)
Clear[CFUnionAIs];
CFUnionAIs[acf_]:=
	Block[{aux,aux2,aux3,i,j,k,l,c1,c2,c3,c4,cf1,cf2,rest,pcf1,pcf2,mi1,mi2,ai1,ai2,inters=False,union=False,res={}},
		If[Length[acf]==1,Return[CFGetAI[acf[[1]]]]];
		res=CFPart[First[acf]];
		rest=Map[CFPart,Rest[acf]];
		
		While[True,
		For[k=1,k<=Length[rest],k++,

		pcf1=res;
		pcf2=rest[[k]];
		c1=INDefine[firstExtreme->0,secondExtreme->90,feIncluded->"[",seIncluded->")"];
		c2=INDefine[firstExtreme->90,secondExtreme->180,feIncluded->"[",seIncluded->")"];
		c3=INDefine[firstExtreme->180,secondExtreme->270,feIncluded->"[",seIncluded->")"];
		c4=INDefine[firstExtreme->270,secondExtreme->360,feIncluded->"[",seIncluded->"]"];
		For[i=1,i<=Length[pcf1],i++,
			For[j=1,j<=Length[pcf2],j++,
				If[!INEmptyQ[INIntersection[CFGetAI[pcf1[[i]]],CFGetAI[pcf2[[j]]]]],
					inters=True;
					Break[];
				]
			];			
			If[inters,
				aux=INUnion[CFGetAI[pcf1[[i]]],CFGetAI[pcf2[[j]]]];
				pcf1=Delete[pcf1,i];pcf2=Delete[pcf2,j];
				i=0;union=True;inters=False;
				pcf2=Append[pcf2,CFDefine[angleInterval->aux]];
			];	
		];
		If[union,
			res=Join[pcf1,pcf2];
			rest=Delete[rest,k];
			k=0;union=False;
			If[AIVerifyCase0360ListQ[Table[res[[l,2]],{l,1,Length[res]}]],aux3=INDefine[firstExtreme->0,secondExtreme->360];Return[aux3]];
		];	
		If[Length[rest]==0,Break[];];

		];
		If[Length[rest]>0,
			aux2=First[rest];
			rest=Rest[rest];
			rest=Append[rest,res];
			res=aux2;
		];
		If[Length[rest]==0,Break[];];
		];
		res=Table[res[[i,2]],{i,1,Length[res]}];
		aux3=AIUnionList[res];
		aux3
	];


(* ::Code::Bold:: *)
(* It verifies in which case falls the addition of two complex fans *)
Clear[CFVerifyCase];
CFVerifyCase[alfa3_,alfa4_]:=
	Block[{},
		Which[
			alfa3>=0 && alfa4<=90,
			1,
			alfa3>=90 && alfa4<=180,
			2,
			alfa3>=180 && alfa4<=270,
			3,
			True,
			4
		]
	];

(* It parts a complex fans *)
Clear[CFPart];
CFPart[cf_]:=
	Block[{ai,mi,alfa1,alfa2,p1,p2,c1,c2,c3,c4,res={}},
		ai =CFGetAI[cf];
		mi =CFGetMI[cf];
		alfa1=INGetFE[ai];
		alfa2=INGetSE[ai];
		p1=INGetFEI[ai];
		p2=INGetSEI[ai];
		c1=CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->90,feIncluded->"[",seIncluded->")"]];
		c2=CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->90,secondExtreme->180,feIncluded->"[",seIncluded->")"]];
		c3=CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->180,secondExtreme->270,feIncluded->"[",seIncluded->")"]];
		c4=CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->270,secondExtreme->360,feIncluded->"[",seIncluded->"]"]];
		Which[
			alfa1<=90&&alfa2<=90&&alfa1>=0&&alfa2>=0,
			Which[
				alfa2<alfa1,
				If[alfa1==90,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->90,secondExtreme->180,feIncluded->p1,seIncluded->")"]],c3,c4,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->90,feIncluded->p1,seIncluded->")"]],c2,c3,c4,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
				],
				alfa2==alfa1,
				If[p1=="["&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->alfa1]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->0,feIncluded->"(",seIncluded->")"]]};
				],
				True,
				If[alfa2==90&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->90,feIncluded->p1,seIncluded->")"]],CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->90,secondExtreme->90,feIncluded->"[",seIncluded->"]"]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->alfa2,feIncluded->p1,seIncluded->p2]]};
				]
			],
			alfa1<=180&&alfa2<=180&&alfa1>=90&&alfa2>=90,
			Which[
				alfa2<alfa1,
				If[alfa1==180,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->180,secondExtreme->270,feIncluded->p1,seIncluded->")"]],c4,c1,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->90,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->180,feIncluded->p1,seIncluded->")"]],c3,c4,c1,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->90,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
				],
				alfa2==alfa1,
				If[p1=="["&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->alfa1]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->0,feIncluded->"(",seIncluded->")"]]};
				],
				True,
				If[alfa2==180&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->180,feIncluded->p1,seIncluded->")"]],CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->180,secondExtreme->180,feIncluded->"[",seIncluded->"]"]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->alfa2,feIncluded->p1,seIncluded->p2]]};
				]
			],
			alfa1<=270&&alfa2<=270&&alfa1>=180&&alfa2>=180,
			Which[
				alfa2<alfa1,
				If[alfa1==270,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->270,secondExtreme->360,feIncluded->p1,seIncluded->"]"]],c1,c2,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->180,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->270,feIncluded->p1,seIncluded->")"]],c4,c1,c2,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->180,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
				],
				alfa2==alfa1,
				If[p1=="["&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->alfa1]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->0,feIncluded->"(",seIncluded->")"]]};
				],
				True,
				If[alfa2==270&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->270,feIncluded->p1,seIncluded->")"]],CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->270,secondExtreme->270,feIncluded->"[",seIncluded->"]"]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->alfa2,feIncluded->p1,seIncluded->p2]]};
				]
			],
			alfa1<=360&&alfa2<=360&&alfa1>=270&&alfa2>=270,
			Which[
				alfa2<alfa1,
				If[alfa1==0,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->90,feIncluded->p1,seIncluded->")"]],c2,c3,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->270,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->360,feIncluded->p1,seIncluded->"]"]],c1,c2,c3,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->270,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
				],
				alfa2==alfa1,
				If[p1=="["&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->alfa1]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->0,feIncluded->"(",seIncluded->")"]]};
				],
				True,
				res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->alfa2,feIncluded->p1,seIncluded->p2]]};
			],
			alfa1>=0&&alfa1<90,
			Which[
				alfa2>90&&alfa2<=180,
				If[alfa2==180&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->90,feIncluded->p1,seIncluded->")"]],c2,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->180,secondExtreme->180,feIncluded->"[",seIncluded->"]"]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->90,feIncluded->p1,seIncluded->")"]],CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->90,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
				],
				alfa2>180&&alfa2<=270,
				If[alfa2==270&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->90,feIncluded->p1,seIncluded->")"]],c2,c3,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->270,secondExtreme->270,feIncluded->"[",seIncluded->"]"]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->90,feIncluded->p1,seIncluded->")"]],c2,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->180,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
				],
				alfa2>270&&alfa2<=360,
				res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->90,feIncluded->p1,seIncluded->")"]],c2,c3,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->270,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
			],
			alfa1>=90&&alfa1<180,
			Which[
				alfa2>180&&alfa2<=270,
				If[alfa2==270&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->180,feIncluded->p1,seIncluded->")"]],c3,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->270,secondExtreme->270,feIncluded->"[",seIncluded->"]"]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->180,feIncluded->p1,seIncluded->")"]],CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->180,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
				],
				alfa2>270&&alfa2<=360,
				res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->180,feIncluded->p1,seIncluded->")"]],c3,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->270,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};,
				alfa2>0&&alfa2<90,
				res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->180,feIncluded->p1,seIncluded->")"]],c3,c4,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
			],
			alfa1>=180&&alfa1<270,
			Which[
				alfa2>270&&alfa2<=360,
				res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->270,feIncluded->p1,seIncluded->")"]],CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->270,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};,
				alfa2>0&&alfa2<=90,
				If[alfa2==90&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->270,feIncluded->p1,seIncluded->")"]],c4,c1,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->90,secondExtreme->90,feIncluded->"[",seIncluded->"]"]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->270,feIncluded->p1,seIncluded->")"]],c4,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
				],
				alfa2>90&&alfa2<180,
				res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->270,feIncluded->p1,seIncluded->")"]],c4,c1,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->90,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
			],
			alfa1>=270&&alfa1<360,
			Which[
				alfa2>0&&alfa2<=90,
				If[alfa2==90&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->360,feIncluded->p1,seIncluded->"]"]],c1,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->90,secondExtreme->90,feIncluded->"[",seIncluded->"]"]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->360,feIncluded->p1,seIncluded->"]"]],CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->0,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
				],
				alfa2>90&&alfa2<=180,
				If[alfa2==180&&p2=="]",
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->360,feIncluded->p1,seIncluded->"]"]],c1,c2,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->180,secondExtreme->180,feIncluded->"[",seIncluded->"]"]]};,
					res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->360,feIncluded->p1,seIncluded->"]"]],c1,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->90,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
				],
				alfa2>180&&alfa2<270,
				res={CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->alfa1,secondExtreme->360,feIncluded->p1,seIncluded->"]"]],c1,c2,CFDefine[magnitudeInterval->mi,angleInterval->INDefine[firstExtreme->180,secondExtreme->alfa2,feIncluded->"[",seIncluded->p2]]};
			]
		];
		(*Graphics[Map[CFBeforePlot,res],Axes\[Rule]True];*)
		res
	];

(* Addition of two complex fan, case 1 *)
Clear[CFAdditionCase1];
CFAdditionCase1[cf1_,cf2_]:=
	Block[{debug=False,mi1=CFGetMI[cf1],mi2=CFGetMI[cf2],ai1=CFGetAI[cf1],ai2=CFGetAI[cf2],a,b,c,d,e,f,alfa1,alfa2,alfa3,alfa4,alfa5,alfa6,anguloMin,anguloMax},
		a=INGetFE[mi1];
		b=INGetSE[mi1];
		c=INGetFE[mi2];
		d=INGetSE[mi2];
		alfa1=INGetFE[ai1];
		alfa2=INGetSE[ai1];
		alfa3=INGetFE[ai2];
		alfa4=INGetSE[ai2];
		If[debug,
			Print[a," ",b," ",alfa1," ",alfa2," ",c," ",d," ",alfa3," ",alfa4]
		];
		If[alfa2>=alfa3,
			anguloMin=0;,
			anguloMin=alfa2-alfa3;
		];
		anguloMax = Max[alfa4-alfa1,alfa2-alfa3];
		e = Sqrt[Power[a,2]+Power[c,2]+Times[2,a,c,Cos[anguloMax Degree]]];
		f = Sqrt[Power[b,2]+Power[d,2]+Times[2,b,d,Cos[anguloMin Degree]]];
		alfa5 = ArcTan[(b*Sin[alfa1 Degree]+c*Sin[alfa3 Degree])/(b Cos[alfa1 Degree]+c Cos[alfa3 Degree])];
		alfa5 = alfa5/Degree;
		If[alfa2<alfa4,
			alfa6 = ArcTan[(a*Sin[alfa2 Degree]+d*Sin[alfa4 Degree])/(a Cos[alfa2 Degree]+d Cos[alfa4 Degree])];,
			If[alfa2>alfa4,
				alfa6 = ArcTan[(b*Sin[alfa2 Degree]+c*Sin[alfa4 Degree])/(b Cos[alfa2 Degree]+c Cos[alfa4 Degree])];,
				alfa6 = alfa2 Degree;
			]
		];
		alfa6 = alfa6/Degree;
		CFDefine[magnitudeInterval->INDefine[firstExtreme->N[e],secondExtreme->N[f]],angleInterval->INDefine[firstExtreme->N[alfa5],secondExtreme->N[alfa6]]]
	];

(* Addition of two complex fans, Case 2 *)
Clear[CFAdditionCase2];
CFAdditionCase2[cf1_,cf2_]:=
	Block[{mi,ai},
		mi=CFMagnitudeCase2[cf1,cf2];
		ai=CFAngleCase2[cf1,cf2];
		(*Print[mi,ai];*)
		CFDefine[magnitudeInterval->mi,angleInterval->ai]
	];

(* Addition of two complex fan, magnitude case 2 *)
Clear[CFMagnitudeCase2];
CFMagnitudeCase2[cf1_,cf2_]:=
	Block[{V1m,V2m,xm,ym,interseccion,mi1=CFGetMI[cf1],mi2=CFGetMI[cf2],ai1=CFGetAI[cf1],ai2=CFGetAI[cf2],a,b,c,d,e,f,alfa1,alfa2,alfa3,alfa4,anguloMin,anguloMax},
		(*Print[mi1,ai1,mi2,ai2];*)
		a=INGetFE[mi1];
		b=INGetSE[mi1];
		c=INGetFE[mi2];
		d=INGetSE[mi2];
		alfa1=INGetFE[ai1];
		alfa2=INGetSE[ai1];
		alfa3=INGetFE[ai2];
		alfa4=INGetSE[ai2];
		anguloMin=alfa3-alfa2;
		anguloMax=alfa4-alfa1;
		If[anguloMin<=90,
			f=Sqrt[Power[b,2]+Power[d,2]+2*b*d*Cos[anguloMin Degree]];,
			f=Max[
				(*p35m*)
				Sqrt[Power[c*Cos[Degree alfa3]+a*Cos[Degree alfa2],2]+Power[c*Sin[Degree alfa3]+a*Sin[Degree alfa2],2]],
				(*p36m*)
				Sqrt[Power[d*Cos[Degree alfa3]+a*Cos[Degree alfa2],2]+Power[d*Sin[Degree alfa3]+a*Sin[Degree alfa2],2]],
				(*p45m*)
				Sqrt[Power[c*Cos[Degree alfa3]+b*Cos[Degree alfa2],2]+Power[c*Sin[Degree alfa3]+b*Sin[Degree alfa2],2]],
				(*p46m*)
                Sqrt[Power[d*Cos[Degree alfa3]+b*Cos[Degree alfa2],2]+Power[d*Sin[Degree alfa3]+b*Sin[Degree alfa2],2]]                        
			];
		];
		V1m = mi1;
		V2m = mi2;
		(* calculando V2m(cos anguloMax) *)
		INByConstant[V2m,Cos[anguloMax Degree]];
		V2m = INNegation[V2m];
		interseccion = INIntersection[V1m,V2m];
		If[!INEmptyQ[interseccion],
			xm = INGetFE[interseccion];,
			If[a>-d*Cos[anguloMax Degree],
				xm = a;,
				If[b<-c*Cos[anguloMax Degree],
					xm = b;
				]
			]
		];
		V2m = mi2;
		(* calculando V1m(cos anguloMax) *)
		INByConstant[V1m,Cos[anguloMax Degree]];
		V1m = INNegation[V1m];
		interseccion = INIntersection[V2m,V1m];
		If[!INEmptyQ[interseccion],
			ym = INGetFE[interseccion];,
			If[c>-b*Cos[anguloMax Degree],
				ym = c;,
				If[d<-a*Cos[anguloMax Degree],
					ym = d;
				]
			]
		];
		e = Sqrt[Power[xm,2]+Power[ym,2]+2*xm*ym*Cos[anguloMax Degree]];
		INDefine[firstExtreme->N[e],secondExtreme->N[f]]
	];

(* Addition of two ComplexFan, angle case 2 *)
Clear[CFAngleCase2];
CFAngleCase2[cf1_,cf2_]:=
	Block[{aux1,aux2,aux3,aux4,interseccion,V1a,V2a,a,b,c,d,alfa1,alfa2,alfa3,alfa4,alfa5,alfa6,anguloy,anguloo,mi1=CFGetMI[cf1],mi2=CFGetMI[cf2],ai1=CFGetAI[cf1],ai2=CFGetAI[cf2]},
		a=INGetFE[mi1];
		b=INGetSE[mi1];
		c=INGetFE[mi2];
		d=INGetSE[mi2];
		alfa1=INGetFE[ai1];
		alfa2=INGetSE[ai1];
		alfa3=INGetFE[ai2];
		alfa4=INGetSE[ai2];
		(*p25a*)
		aux1=CFAngleFixer[c Cos[alfa3 Degree]+b Cos[alfa1 Degree],c*Sin[alfa3 Degree]+b*Sin[alfa1 Degree]];
		(*p27a*)
		aux2=CFAngleFixer[c Cos[alfa4 Degree]+b Cos[alfa1 Degree],c*Sin[alfa4 Degree]+b*Sin[alfa1 Degree]];
		alfa5 = Min[aux1,aux2];
		(*p18a*)
		aux3=CFAngleFixer[d Cos[alfa4 Degree]+a Cos[alfa1 Degree],d*Sin[alfa4 Degree]+a*Sin[alfa1 Degree]];
		(*p38a*)
		aux4=CFAngleFixer[d Cos[alfa4 Degree]+a Cos[alfa2 Degree],d*Sin[alfa4 Degree]+a*Sin[alfa2 Degree]];
		alfa6 = Max[aux3,aux4];
		V1a = ai1;
		V2a = ai2;
		If[alfa6<90,
			anguloy = alfa2+N[ArcSin[d/a]]/Degree;
			anguloo = anguloy+90;
			interseccion = INIntersection[INDefine[firstExtreme->anguloo,secondExtreme->anguloo],V2a];
			If[!INEmptyQ[interseccion],
				alfa6 = anguloy;,
				If[anguloo<alfa3,
					(*alfa6 = p36a*)
					alfa6 = CFAngleFixer[d Cos[alfa3 Degree]+a Cos[alfa2 Degree],d*Sin[alfa3 Degree]+a*Sin[alfa2 Degree]];,
					If[anguloo>alfa4,
						(*alfa6 = p38a*)
						alfa6 = CFAngleFixer[d Cos[alfa4 Degree]+a Cos[alfa2 Degree],d*Sin[alfa4 Degree]+a*Sin[alfa2 Degree]];
					]
				]
			]
		];
		If[alfa5>90,
			anguloy = alfa3 - N[ArcSin[b/c]]/Degree;
			anguloo = anguloy - 90;
			interseccion = INIntersection[INDefine[firstExtreme->anguloo,secondExtreme->anguloo],V1a];
			If[!INEmptyQ[interseccion],
				(* Correccion del algoritmo de alfa5=anguloo a alfa5=anguloy*)
				alfa5 = anguloy;,
				If[anguloo<alfa1,
					(* alfa5 = p25a *)
					alfa5 = CFAngleFixer[c Cos[alfa3 Degree]+b Cos[alfa1 Degree],c*Sin[alfa3 Degree]+b*Sin[alfa1 Degree]];,
					If[anguloo>alfa2,
						(* alfa5 = p45a *)
						alfa5 = CFAngleFixer[c Cos[alfa3 Degree]+b Cos[alfa2 Degree],c*Sin[alfa3 Degree]+b*Sin[alfa2 Degree]];
					]
				]
			]
		];
		INDefine[firstExtreme->alfa5,secondExtreme->alfa6]
	];

(* Addition of two complex fans, Case 3 *)
Clear[CFAdditionCase3];
CFAdditionCase3[cf1_,cf2_]:=
	Block[{mi,ai},
		mi=CFMagnitudeCase3[cf1,cf2];
		ai=CFAngleCase3[cf1,cf2];
		CFDefine[magnitudeInterval->mi,angleInterval->ai]
	];

(* Addition of two complex fan, magnitude case3 *)
Clear[CFMagnitudeCase3];
CFMagnitudeCase3[cf1_,cf2_]:=
	Block[{V1m,V2m,xm,ym,interseccion,mi1=CFGetMI[cf1],mi2=CFGetMI[cf2],ai1=CFGetAI[cf1],ai2=CFGetAI[cf2],a,b,c,d,e,f,alfa1,alfa2,alfa3,alfa4,angulo1,angulo2},
		a=INGetFE[mi1];
		b=INGetSE[mi1];
		c=INGetFE[mi2];
		d=INGetSE[mi2];
		alfa1=INGetFE[ai1];
		alfa2=INGetSE[ai1];
		alfa3=INGetFE[ai2];
		alfa4=INGetSE[ai2];
		angulo1 = alfa3-alfa2;
		angulo2 = 360 - (alfa4 - alfa1);
		If[angulo1<angulo2,
			f = N[Max[
				(*p35m*)
				Sqrt[Power[c*Cos[Degree alfa3]+a*Cos[Degree alfa2],2]+Power[c*Sin[Degree alfa3]+a*Sin[Degree alfa2],2]],
				(*p36m*)
				Sqrt[Power[d*Cos[Degree alfa3]+a*Cos[Degree alfa2],2]+Power[d*Sin[Degree alfa3]+a*Sin[Degree alfa2],2]],
				(*p45m*)
				Sqrt[Power[c*Cos[Degree alfa3]+b*Cos[Degree alfa2],2]+Power[c*Sin[Degree alfa3]+b*Sin[Degree alfa2],2]],
				(*p46m*)
                Sqrt[Power[d*Cos[Degree alfa3]+b*Cos[Degree alfa2],2]+Power[d*Sin[Degree alfa3]+b*Sin[Degree alfa2],2]]                        
			]];,
			f = N[Max[
				(*p17m*)
				Sqrt[Power[c*Cos[Degree alfa4]+a*Cos[Degree alfa1],2]+Power[c*Sin[Degree alfa4]+a*Sin[Degree alfa1],2]],
				(*p18m*)
				Sqrt[Power[d*Cos[Degree alfa4]+a*Cos[Degree alfa1],2]+Power[d*Sin[Degree alfa4]+a*Sin[Degree alfa1],2]],
				(*p27m*)
				Sqrt[Power[c*Cos[Degree alfa4]+b*Cos[Degree alfa1],2]+Power[c*Sin[Degree alfa4]+b*Sin[Degree alfa1],2]],
				(*p28m*)
                Sqrt[Power[d*Cos[Degree alfa4]+b*Cos[Degree alfa1],2]+Power[d*Sin[Degree alfa4]+b*Sin[Degree alfa1],2]]                        
			]];
		];
		V1m = mi1;
		V2m = mi2;
		interseccion = INIntersection[V1m,V2m];
		If[debug,INPrint[interseccion]];
		If[!INEmptyQ[interseccion],
			xm = INGetFE[interseccion];
			ym = INGetFE[interseccion];,
			If[a>d,
				xm = a;
				ym = d;,
				If[b<c,
					xm = b;
					ym = c;
				]
			]
		];
		e=Sqrt[Power[xm,2]+Power[ym,2]-2*xm*ym];
		INDefine[firstExtreme->e,secondExtreme->f]
	];

(* Addition of two complex fan, angle case 3 *)
Clear[CFAngleCase3];
CFAngleCase3[cf1_,cf2_]:=
	Block[{res,anguloMax,in1,in2,V1a,V2a,V1m,V2m,MagDiff,a,b,c,d,alfa1,alfa2,alfa3,alfa4,alfa5,alfa6,anguloy1,anguloo1,anguloy2,anguloo2,mi1=CFGetMI[cf1],mi2=CFGetMI[cf2],ai1=CFGetAI[cf1],ai2=CFGetAI[cf2]},
		a=INGetFE[mi1];
		b=INGetSE[mi1];
		c=INGetFE[mi2];
		d=INGetSE[mi2];
		alfa1=INGetFE[ai1];
		alfa2=INGetSE[ai1];
		alfa3=INGetFE[ai2];
		alfa4=INGetSE[ai2];
		anguloMax = 180;
		V1m = mi1;
		V2m = mi2;
		INByConstant[V2m,Cos[anguloMax Degree]];
		MagDiff = INAddition[V1m,V2m];
		V1a = ai1;
		V2a = ai2;
		in1 = INIntersection[INDefine[],MagDiff];
		If[!INEmptyQ[in1],
			alfa5=0;
			alfa6=360;,
			If[INGetFE[MagDiff]>0&&INGetSE[MagDiff]>0,
				(* alfa6 = p36a *)
				alfa6 = CFAngleFixer[(d Cos[alfa3 Degree] + a Cos[alfa2 Degree]),(d Sin[alfa3 Degree] + a Sin[alfa2 Degree])];
				If[alfa6>90,
					anguloy1 = N[ArcSin[d/a]/Degree]+alfa2;
					anguloo1 = anguloy1 + 90;
					in2 = INIntersection[INDefine[firstExtreme->anguloo1,secondExtreme->anguloo1],V2a];
					If[!INEmptyQ[in2],
						alfa6 = anguloy1;,
						If[anguloo1<alfa3,
							(* alfa6 = p36a *)
							alfa6 = CFAngleFixer[(d Cos[alfa3 Degree] + a Cos[alfa2 Degree]),(d Sin[alfa3 Degree] + a Sin[alfa2 Degree])];,
							If[anguloo1>alfa4,
								(* alfa6 = p38a *)
								alfa6 = CFAngleFixer[(d Cos[alfa4 Degree] + a Cos[alfa2 Degree]),(d Sin[alfa4 Degree] + a Sin[alfa2 Degree])];
							]
						]
					]
				];
				(* alfa5 = p18a *)
				alfa5 = CFAngleFixer[(d Cos[alfa4 Degree] + a Cos[alfa1 Degree]),(d Sin[alfa4 Degree] + a Sin[alfa1 Degree])];
				If[alfa5>270,
					anguloy2 = 360 - N[ArcSin[d/a]/Degree];
					anguloo2 = anguloy2 - 90;
					in2 = INIntersection[INDefine[firstExtreme->anguloo2,secondExtreme->anguloo2],V2a];
					If[!INEmptyQ[in2],
						alfa5 = anguloy2;,
						If[anguloo2<alfa3,
							(* alfa5 = p16a *)
							alfa5 = CFAngleFixer[(d Cos[alfa3 Degree] + a Cos[alfa1 Degree]),(d Sin[alfa3 Degree] + a Sin[alfa1 Degree])];,
							If[anguloo2>alfa4,
								(* alfa5 = p18a *)
								alfa5 = CFAngleFixer[(d Cos[alfa4 Degree] + a Cos[alfa1 Degree]),(d Sin[alfa4 Degree] + a Sin[alfa1 Degree])];
							]
						]
					]
				];,
				(* Case MagDiff < 0 is symmetrical *)
				(* alfa6 = p72a *)
				alfa6 = CFAngleFixer[(c Cos[alfa4 Degree] + b Cos[alfa1 Degree]),(c Sin[alfa4 Degree] + b Sin[alfa1 Degree])];
				If[alfa6>270,
					anguloy1 = alfa4 + N[ArcSin[b/c]/Degree];
					anguloo1 = Mod[anguloy1 + 90,360];
					in2 = INIntersection[INDefine[firstExtreme->anguloo1,secondExtreme->anguloo1],V1a];
					If[!INEmptyQ[in2],
						alfa6 = anguloy1;,
						If[anguloo1<alfa1,
							(* alfa6 = p72a *)
							alfa6 = CFAngleFixer[(c Cos[alfa4 Degree] + b Cos[alfa1 Degree]),(c Sin[alfa4 Degree] + b Sin[alfa1 Degree])];,
							If[anguloo1>alfa2,
								(* alfa6 = p74a *)
								alfa6 = CFAngleFixer[(c Cos[alfa4 Degree] + b Cos[alfa2 Degree]),(c Sin[alfa4 Degree] + b Sin[alfa2 Degree])];
							]
						]
					]
				];
				(* alfa5 = p54a *)
				alfa5 = CFAngleFixer[(c Cos[alfa3 Degree] + b Cos[alfa2 Degree]),(c Sin[alfa3 Degree] + b Sin[alfa2 Degree])];
				If[alfa5<180,
					anguloy2 = alfa3 - N[ArcSin[b/c]/Degree];
					anguloo2 = anguloy2 - 90;
					in2 = INIntersection[INDefine[firstExtreme->anguloo2,secondExtreme->anguloo2],V1a];
					If[!INEmptyQ[in2],
						alfa5 = anguloy2;,
						If[anguloo2<alfa1,
							(* alfa5 = p52a *)
							alfa5 = CFAngleFixer[(c Cos[alfa3 Degree] + b Cos[alfa1 Degree]),(c Sin[alfa3 Degree] + b Sin[alfa1 Degree])];,
							If[anguloo2>alfa2,
								(* alfa5 = p54a *)
								alfa5 = CFAngleFixer[(c Cos[alfa3 Degree] + b Cos[alfa2 Degree]),(c Sin[alfa3 Degree] + b Sin[alfa2 Degree])];
							]
						]
					]
				];
			]
		];
		INDefine[firstExtreme->alfa5,secondExtreme->alfa6]
	];

(* Function for angle correction when we add two vectors *)
Clear[CFAngleFixer];
CFAngleFixer[x_,y_]:=
	Block[{theta},
		Which[
			x>=0&&y>0,
			If[x==0,
				theta=90;,
				theta=ArcTan[y/x]/Degree;
			],
			x>=0&&y==0,
			If[x==0,
				(*Print["Division por cero!"];
				Exit[];*)theta=0;,
				theta=0;
			],
			x>=0&&y<0,
			If[x==0,
				theta=270;,
				theta=360-ArcTan[Abs[y]/x]/Degree;
			],
			x<0&&y>0,
			theta=180-ArcTan[y/Abs[x]]/Degree;,
			x<0&&y==0,
			theta=180;,
			x<0&&y<0,
			theta=180+ArcTan[Abs[y]/Abs[x]]/Degree;	
		];
		N[theta]
	];

(* It prints the representation of a complex fan *)
Clear[CFPrint];
CFPrint[cf_]:=Print[CFStringForm[cf]];

(*It returns the String Representation of a Complex Fan*)
Clear[CFStringForm];
CFStringForm[cf_]:=INStringForm[CFGetMI[cf]]<>" \[Angle] "<>INStringForm[CFGetAI[cf]];

(* It prepares a complex fan for ploting *)
Clear[CFBeforePlot];
CFBeforePlot[cf_]:=
	Block[{mi=CFGetMI[cf],ai=CFGetAI[cf],a,b,alfa1,alfa2},
		a=INGetFE[mi];
		b=INGetSE[mi];
		alfa1=INGetFE[ai];
		alfa2=INGetSE[ai];
		If[alfa1>alfa2,alfa1=alfa1-360;];
		{Circle[{0,0},a,{alfa1 Degree,alfa2 Degree}],Circle[{0,0},b,{alfa1 Degree,alfa2 Degree}],Line[{{a Cos[alfa1 Degree],a Sin[alfa1 Degree]},{b Cos[alfa1 Degree],b Sin[alfa1 Degree]}}],Line[{{a Cos[alfa2 Degree],a Sin[alfa2 Degree]},{b Cos[alfa2 Degree],b Sin[alfa2 Degree]}}]}
	];

(* It plots a complex fan *)
Clear[CFPlot];
CFPlot[cf_]:=
	Block[{},
		If[ListQ[cf],
			If[Length[cf]>0,
				Graphics[Map[CFBeforePlot,cf],Axes->True,AxesOrigin->{0,0},AxesStyle->Gray,Method->{"AxesInFront"->False}]
			]
		]
	];

(* Graphical representation of the addition of two complex fans *)
Clear[CFAdditionPlot];
CFAdditionPlot[cf1_,cf2_,cfr_]:=
	Block[{cf1g,cf2g,cfrg,aux1,aux2,aux3,aux4,aux5,aux6,aux7,aux8,mi1=CFGetMI[cf1],ai1=CFGetAI[cf1],mi2=CFGetMI[cf2],ai2=CFGetAI[cf2],a,b,alfa1,alfa2,c,d,alfa3,alfa4},
		a=INGetFE[mi1];
		b=INGetSE[mi1];
		alfa1=INGetFE[ai1];
		alfa2=INGetSE[ai1];
		c=INGetFE[mi2];
		d=INGetSE[mi2];
		alfa3=INGetFE[ai2];
		alfa4=INGetSE[ai2];
		cf1g=CFBeforePlot[cf1];
		cf2g=CFBeforePlot[cf2];
		cfrg=CFBeforePlot[cfr];
		aux1=CFAdditionPlotAux[{a Cos[alfa1 Degree],a Sin[alfa1 Degree]},cf2];
		aux2=CFAdditionPlotAux[{b Cos[alfa1 Degree],b Sin[alfa1 Degree]},cf2];
		aux3=CFAdditionPlotAux[{a Cos[alfa2 Degree],a Sin[alfa2 Degree]},cf2];
		aux4=CFAdditionPlotAux[{b Cos[alfa2 Degree],b Sin[alfa2 Degree]},cf2];
		aux5=CFAdditionPlotAux[{c Cos[alfa3 Degree],c Sin[alfa3 Degree]},cf1];
		aux6=CFAdditionPlotAux[{d Cos[alfa3 Degree],d Sin[alfa3 Degree]},cf1];
		aux7=CFAdditionPlotAux[{c Cos[alfa4 Degree],c Sin[alfa4 Degree]},cf1];
		aux8=CFAdditionPlotAux[{d Cos[alfa4 Degree],d Sin[alfa4 Degree]},cf1];
		{Graphics[Join[{Dashing[Tiny]},aux1,aux2,aux3,aux4,{Red,Dashing[{}]},cfrg,{Blue},cf1g,{Green},cf2g],Axes->True,AxesStyle->Gray,AxesOrigin->{0,0},Method->{"AxesInFront"->False}],Graphics[Join[{Dashing[Tiny],Green},aux5,aux6,aux7,aux8,{Red,Dashing[{}]},cfrg,{Blue},cf1g,{Green},cf2g],Axes->True,AxesStyle->Gray,AxesOrigin->{0,0},Method->{"AxesInFront"->False}]}
		(*{Graphics[Join[cf1g,cf2g,cfrg,{Dashing[Tiny]},aux1,aux2,aux3,aux4],Axes->True,AxesOrigin->{0,0}],Graphics[Join[cf1g,cf2g,cfrg,{Dashing[Tiny]},aux5,aux6,aux7,aux8],Axes->True,AxesOrigin->{0,0}]}*)
	];

(* Auxiliar Function for CFAdditionPlot *)
Clear[CFAdditionPlotAux];
CFAdditionPlotAux[p_,cf_]:=
	Block[{mi=CFGetMI[cf],ai=CFGetAI[cf],a,b,alfa1,alfa2},
		a=INGetFE[mi];
		b=INGetSE[mi];
		alfa1=INGetFE[ai];
		alfa2=INGetSE[ai];
		If[alfa1>alfa2,alfa1=alfa1-360;];
		{Gray,Circle[p,a,{alfa1 Degree,alfa2 Degree}],Circle[p,b,{alfa1 Degree,alfa2 Degree}],Line[{{a Cos[alfa1 Degree]+p[[1]],a Sin[alfa1 Degree]+p[[2]]},{b Cos[alfa1 Degree]+p[[1]],b Sin[alfa1 Degree]+p[[2]]}}],Line[{{a Cos[alfa2 Degree]+p[[1]],a Sin[alfa2 Degree]+p[[2]]},{b Cos[alfa2 Degree]+p[[1]],b Sin[alfa2 Degree]+p[[2]]}}],Line[{p,{a Cos[alfa1 Degree]+p[[1]],a Sin[alfa1 Degree]+p[[2]]}}],Line[{p,{a Cos[alfa2 Degree]+p[[1]],a Sin[alfa2 Degree]+p[[2]]}}]}
		(*{Gray,Circle[p,a,{alfa1 Degree,alfa2 Degree}],Circle[p,b,{alfa1 Degree,alfa2 Degree}],Green,Line[{p,{b Cos[alfa1 Degree]+p[[1]],b Sin[alfa1 Degree]+p[[2]]}}],Line[{p,{b Cos[alfa2 Degree]+p[[1]],b Sin[alfa2 Degree]+p[[2]]}}]}*)
	];

(* Graphical representation of the addition of two complex fans *)
(*verificar cuando CF[IN[FE[22],SE[24],FEI["["],SEI["]"]],IN[FE[180],SE[90],FEI["["],SEI[")"]]]
CF[IN[FE[2],SE[4],FEI["["],SEI["]"]],IN[FE[90],SE[180],FEI["["],SEI[")"]]]*)
Clear[CFProjectionPlot];
CFProjectionPlot[cf1_,cf2_]:=
	Block[{cf1g,cf2g,aux1,aux2,aux3,aux4,aux5,aux6,aux7,aux8,mi1=CFGetMI[cf1],ai1=CFGetAI[cf1],mi2=CFGetMI[cf2],ai2=CFGetAI[cf2],a,b,alfa1,alfa2,c,d,alfa3,alfa4},
		a=INGetFE[mi1];
		b=INGetSE[mi1];
		alfa1=INGetFE[ai1];
		alfa2=INGetSE[ai1];
		c=INGetFE[mi2];
		d=INGetSE[mi2];
		alfa3=INGetFE[ai2];
		alfa4=INGetSE[ai2];
		cf1g=CFBeforePlot[cf1];
		cf2g=CFBeforePlot[cf2];
		aux1=CFAdditionPlotAux[{a Cos[alfa1 Degree],a Sin[alfa1 Degree]},cf2];
		aux2=CFAdditionPlotAux[{b Cos[alfa1 Degree],b Sin[alfa1 Degree]},cf2];
		aux3=CFAdditionPlotAux[{a Cos[alfa2 Degree],a Sin[alfa2 Degree]},cf2];
		aux4=CFAdditionPlotAux[{b Cos[alfa2 Degree],b Sin[alfa2 Degree]},cf2];
		aux5=CFAdditionPlotAux[{c Cos[alfa3 Degree],c Sin[alfa3 Degree]},cf1];
		aux6=CFAdditionPlotAux[{d Cos[alfa3 Degree],d Sin[alfa3 Degree]},cf1];
		aux7=CFAdditionPlotAux[{c Cos[alfa4 Degree],c Sin[alfa4 Degree]},cf1];
		aux8=CFAdditionPlotAux[{d Cos[alfa4 Degree],d Sin[alfa4 Degree]},cf1];
		{Graphics[Join[cf1g,cf2g,{Dashing[Tiny],Blue},aux1,aux2,aux3,aux4],Axes->True,AxesStyle->Gray,AxesOrigin->{0,0},Method->{"AxesInFront"->False}],Graphics[Join[cf1g,cf2g,{Dashing[Tiny],Red},aux5,aux6,aux7,aux8],Axes->True,AxesStyle->Gray,AxesOrigin->{0,0},Method->{"AxesInFront"->False}]}
	];

(* Graphical representation of the subtraction of two complex fans *)
Clear[CFSubtractionPlot];
CFSubtractionPlot[cf1_,cf2_,cfr_]:=
	Block[{cf2n},
		cf2n=CFNegation[cf2];
		CFAdditionPlot[cf1,cf2n,cfr]
	];

(* It plots operands of an operation with its result *)
Clear[CFOperationPlot];
CFOperationPlot[cf1_,cf2_,cfr_]:=Graphics[Join[{Blue},CFBeforePlot[cf1],{Green},CFBeforePlot[cf2],{Red},CFBeforePlot[cfr]],Axes->True,AxesStyle->Gray,AxesOrigin->{0,0},Method->{"AxesInFront"->False}];

(* It plots a negation operation *)
Clear[CFNegationPlot];
CFNegationPlot[cf_,cfr_]:=Graphics[Join[{Blue},CFBeforePlot[cf],{Red},CFBeforePlot[cfr]],Axes->True,AxesStyle->Gray,AxesOrigin->{0,0},Method->{"AxesInFront"->False}];
