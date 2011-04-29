open Camlp4
open PreCast
open Ast
open Str
open Loc

(* Il faut, a partir de chaque nouvelle descente dans une fonction ie. exLet, stVal etc,*)
(* fournir un Lexenv vide et l'enrichir a chaque nouvelle def, ensuite pour une utilisation*)
(* on regarde dans ce Lexenv (liste chainée) a partir de la derniere ajoutee*)
(*  si on trouve pas de correspondance, regarder dans le common*)
(* *)
(* 2 hashtbl :*)
(*     k                   v*)
(*  nouveau_nom       loc,loc_list *)
(*  ancien_nom        portée,nouveau_nom*)



type loc_locList = loc * loc list
type range_genName = loc * string

let newLoc loc name =
	Loc.of_tuple (Loc.file_name loc, Loc.start_line loc, Loc.start_bol loc,
      Loc.start_off loc, Loc.stop_line loc, Loc.stop_bol loc, (Loc.start_off loc)+(String.length name), Loc.is_ghost loc)

let parse_rec_flag = function
|   ReRecursive -> ()
|   ReNil       -> ()
|   ReAnt str   -> ()

let parse_direction_flag = function
|   DiTo        -> ()
|   DiDownto    -> ()
|   DiAnt str   -> ()

let parse_mutable_flag = function
|   MuMutable   -> ()
|   MuNil       -> ()
|   MuAnt str   -> ()

let parse_private_flag = function
|   PrPrivate   -> ()
|   PrNil       -> ()
|   PrAnt str   -> ()

let parse_virtual_flag = function
|   ViVirtual   -> ()
|   ViNil       -> ()
|   ViAnt str   -> ()

let parse_override_flag = function
|   OvOverride  -> ()
|   OvNil       -> ()
|   OvAnt str   -> ()

let parse_row_var_flag = function
|   RvRowVar    -> ()
|   RvNil       -> ()
|   RvAnt str   -> ()

let string_of_loc loc =
    (string_of_int (Loc.start_off loc)) ^ "," ^ (string_of_int (Loc.stop_off loc))

let parse_ident c n = function (* The type of identifiers (including path like Foo(X).Bar.y) *)
    | IdUid(loc, name) -> print_endline ("PARSE_IDENT Uid "^name);(newLoc loc name, name)
		| IdLid(loc, name) -> print_endline ("PARSE_IDENT Lid "^name);(newLoc loc name, name)
		| _-> (Loc.ghost,"")

let rec parse_strings c n = function 
	  | _ -> ()
		
let rec findRange loc max s = function 
	| [] -> s
	| (range,name)::q -> let start_range = Loc.start_pos range and stop_range = Loc.stop_pos range in
													if( start_range <= (Loc.start_pos loc) && stop_range >= (Loc.stop_pos loc)
															&& start_range >= Loc.start_pos max) then
														findRange loc range name q
													else findRange loc max s q
		
let addLoc common names expname =
	let (loc,key) = expname in
		let res=  try match (Hashtbl.find names key) with
							| [] -> failwith "unbound variable"^key
							| l -> findRange loc Loc.ghost "" l
							with Not_found -> key (* que globale *)
		in
		print_endline ("TROUVE "^res);
			if(res=="") then failwith "should never happen";
			try let (locDef, locList) = (Hashtbl.find common res) in
				Hashtbl.replace common res (locDef, (fst expname)::locList)
			with Not_found -> Hashtbl.add common res ((fst expname), [])
			
let genVarName name =
	name ^"__"^ (string_of_float (Unix.time()))

let rec parse_ctyp c n = function 
		(* i *) (* Lazy.t *) (** Type identifier *)
	  | TyId(loc, ident1) -> addLoc c n (parse_ident c n ident1)
		(* type t 'a 'b 'c = t constraint t = t constraint t = t *) (** Type declaration *)
		| TyDcl(loc, name, ctyps, ctyp1, constraints) -> Hashtbl.add c name (newLoc loc name,  []); parse_ctyp c n ctyp1
		(** Empty type *)
    | TyNil(loc) -> ()
    (* t as t *) (* list 'a as 'a *) (** Type aliasing *)
    | TyAli(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* _ *) (** Wildcard *)
    | TyAny(loc) -> ()
    (* t t *) (* list 'a *) (** Application *)
    | TyApp(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* t) -> t *) (* int) -> string *) (** Arrow *)
    | TyArr(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* #i *) (* #point *) (** Class type *)
    | TyCls(loc, ident1) -> parse_ident c n ident1; ()
    (* ~s:t *) (** Label type *)
    | TyLab(loc, name, ctyp1) -> parse_ctyp c n ctyp1
    (* t == t *) (* type t = [ A | B ] == Foo.t *) (** Type manifest *)
    | TyMan(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* < (t)? (..)? > *) (* < move : int) -> 'a .. > as 'a  *) (**   Object type *)
    | TyObj(loc, ctyp1, row_var_flag) -> parse_ctyp c n ctyp1
    (* ?s:t *) (** Optional label type *)
    | TyOlb(loc, name, ctyp1) -> parse_ctyp c n ctyp1
    (* ! t . t *) (* ! 'a . list 'a) -> 'a *) (** Polymorphic type *)
    | TyPol(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* 's *)
    | TyQuo(loc, name) -> ()
    (* +'s *)
    | TyQuP(loc, name) -> ()
    (* -'s *)
    | TyQuM(loc, name) -> ()
    (* `s *) (** Polymorphic variant *)
    | TyVrn(loc, name) -> ()
    (* { t } *) (* { foo : int ; bar : mutable string } *) (** Record *)
    | TyRec(loc, ctyp1) -> parse_ctyp c n ctyp1
    (* t : t *) (** Field declaration *)
    | TyCol(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* t; t *) (** Semicolon-separated type list *)
    | TySem(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* t, t *) (** Comma-separated type list *)
    | TyCom(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* [ t ] *) (* [ A of int, string | B ] *) (** Sum type *)
    | TySum(loc, ctyp1) -> parse_ctyp c n ctyp1
    (* t of t *) (* A of int *)
    | TyOf(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* t, t *)
    | TyAnd(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* t | t *) (** "Or" pattern between types *)
    | TyOr(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* private t *) (** Private type *)
    | TyPrv(loc, ctyp1) -> parse_ctyp c n ctyp1
    (* mutable t *) (** Mutable type *)
    | TyMut(loc, ctyp1) -> parse_ctyp c n ctyp1
    (* ( t ) *) (* (int * string) *) (** Tuple *)
    | TyTup(loc, ctyp1) -> parse_ctyp c n ctyp1
    (* t * t *)
    | TySta(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* [ = t ] *)
    | TyVrnEq(loc, ctyp1) -> parse_ctyp c n ctyp1
    (* [ > t ] *)
    | TyVrnSup(loc, ctyp1) -> parse_ctyp c n ctyp1
    (* [ < t ] *)
    | TyVrnInf(loc, ctyp1) -> parse_ctyp c n ctyp1
    (* [ < t > t ] *)
    | TyVrnInfSup(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* t & t *)
    | TyAmp(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (* t of & t *)
    | TyOfAmp(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2
    (** Package type **)
    | TyPkg(loc, module_type1) -> parse_module_type c n module_type1
    (* $s$ *) (** Antiquotation *)
    | TyAnt(loc, name) -> ()

and parse_patt c n = function 
		| PaId(loc, ident1) -> parse_ident c n ident1
		| _ -> (Loc.ghost,"")
and parse_expr c n = function 
		| ExApp(loc, expr1, expr2) -> let expName = parse_expr c n expr2 and appName = parse_expr c n expr1 in 
																		( match (snd appName) with
																		| "raise" -> addLoc c n expName; (Loc.ghost,"")					 
																		| _ -> print_string (snd appName); addLoc c n appName; (Loc.ghost,"")
																		)
		| ExId(loc, ident1) -> parse_ident c n ident1
		(* try e with [ mc ] *) (** "Try .. with" construct *)
    | ExTry(loc, expr1, match_case1) -> parse_expr c n expr1;
			                                  let excName = parse_match_case c n match_case1 in
																				   addLoc c n excName; (Loc.ghost,"")		
		| ExFun(loc, match_case1) -> parse_match_case c n match_case1
		| ExLet(loc, rec_flag, binding1, expr1) -> let (defLoc,defName) = parse_binding c n binding1 in 
																								let genName = genVarName defName in
																									 let l = try (Hashtbl.find n defName) 
																										with Not_found -> [] in
																										Hashtbl.replace n defName ((loc,genName)::l);
																										Hashtbl.add c genName (defLoc, []);
																								parse_expr c n expr1
		(* (e : t) *) (** Type constraint *)
    | ExTyc(loc, expr1, ctyp1) ->  parse_ctyp c n ctyp1; parse_expr c n expr1
		| _ -> (Loc.ghost,"")
and parse_module = function
	  | _ -> ()
and parse_binding c n = function
		| BiEq(loc, patt1, expr1) -> let patt = parse_patt c n patt1 in parse_expr c n expr1; patt
		| BiAnd(loc, binding1, binding2) -> parse_binding c n binding1; parse_binding c n binding2;
		| _ -> (Loc.ghost,"")
and parse_rec_binding = function
    | _ -> ()
and parse_module_binding c n = function
		(** Empty module definition *)
    | MbNil(loc) -> ()
    (* mb, mb *) (* module rec (s : mt) = me, (s : mt) = me *)
    | MbAnd(loc, module_binding1, module_binding2) -> parse_module_binding c n module_binding1; parse_module_binding c n module_binding2
    (* s : mt = me *)
    | MbColEq(loc, name, module_type1, module_expr1) -> Hashtbl.add c name (newLoc loc name,  [])
    (* s : mt *)
    | MbCol(loc, name, module_type1) -> Hashtbl.add c name (newLoc loc name,  [])
    (* $s$ *)
    | MbAnt(loc, name) -> Hashtbl.add c name (newLoc loc name,  [])
and parse_match_case c n = function
	  | McArr(loc, patt1, expr1, expr2) -> let patt = parse_patt c n patt1 in parse_expr c n expr2; patt; 
		| _ -> (Loc.ghost,"")
and parse_module_expr c n = function
    | _ -> ()
and parse_module_type c n = function (* The type of module types                                   *)
    | MtNil(loc) -> ()
    (* i *) (* A.B.C *)
    | MtId(loc, ident1) -> parse_ident c n ident1; ()
    (* functor (s : mt)) -> mt *)
    | MtFun(loc, name, module_type1, module_type2) -> parse_module_type c n module_type1; parse_module_type c n module_type2; ()
    (* 's *)
    | MtQuo(loc, name) ->()
    (* sig sg end *)
    | MtSig(loc, sig_item1) -> parse_sig_item c n sig_item1; ()
    (* mt with wc *)
    | MtWit(loc, module_type1, with_constr1) ->parse_module_type c n module_type1; parse_with_constr c n with_constr1; ()
    (* $s$ *)
    | MtAnt(loc, name) -> ()
and parse_sig_item c n = function (* The type of signature items                                *)
    | SgNil(loc) -> ()
    (* class cict *)
    | SgCls(loc, class_type1) -> parse_class_type c n class_type1; ()
    (* class type cict *)
    | SgClt(loc, class_type1) -> parse_class_type c n class_type1; ()
    (* sg ; sg *)
    | SgSem(loc, sig_item1, sig_item2) -> parse_sig_item c n sig_item1; parse_sig_item c n sig_item2; ()
    (* # s or # s e *)
    | SgDir(loc, name, expr1) -> parse_expr c n expr1; ()
    (* exception t *)
    | SgExc(loc, ctyp1) -> parse_ctyp c n ctyp1; ()
    (* external s : t = s ... s *)
    | SgExt(loc, name, ctyp1, strings (*meta_list string*)) -> parse_ctyp c n ctyp1; parse_strings c n strings; ()
    (* include mt *)
    | SgInc(loc, module_type1) -> parse_module_type c n module_type1; ()
    (* module s : mt *)
    | SgMod(loc, name, module_type1) -> parse_module_type c n module_type1; ()
    (* module rec mb *)
    | SgRecMod(loc, module_binding1) -> parse_module_binding c n module_binding1; ()
    (* module type s = mt *)
    | SgMty(loc, name, module_type1) -> parse_module_type c n module_type1; ()
    (* open i *)
    | SgOpn(loc, ident1) -> parse_ident c n ident1; ()
    (* type t *)
    | SgTyp(loc, ctyp1) -> parse_ctyp c n ctyp1; ()
    (* value s : t *)
    | SgVal(loc, name, ctyp1) -> parse_ctyp c n ctyp1; ()
    (* $s$ *)
    | SgAnt(loc, name) -> ()
and parse_with_constr c n = function (* The type of `with' constraints                             *)
    | WcNil(loc) -> ()
    (* type t = t *)
    | WcTyp(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2; ()
    (* module i = i *)
    | WcMod(loc, ident1, ident2) -> parse_ident c n ident1; parse_ident c n ident2; ()
    (* type t = t *)
    | WcTyS(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2; ()
    (* module i = i *)
    | WcMoS(loc, ident1, ident2) ->parse_ident c n ident1; parse_ident c n ident2; ()
    (* wc, wc *)
    | WcAnd(loc, with_constr1, with_constr2) -> parse_with_constr c n with_constr1; parse_with_constr c n with_constr2; ()
    (* $s$ *)
    | WcAnt(loc, name) -> ()
and parse_str_item c n m = function (* The type of structure items                                *)
    | StNil(loc) -> ();
    (* # s or # s e *)
    | StDir(loc, name, expr1) -> Hashtbl.add c name (loc,  [])
		(* exception t or exception t = i *)
    | StExc(loc, ctyp1, option_ident) -> parse_ctyp c n ctyp1; ()
    (* external s : t = s ... s *)
    | StExt(loc, name, ctyp1, (*TODO*) strings(*meta_list string*)) -> Hashtbl.add c name (loc,  [])
    (* module s = me *)
    | StMod(loc, name, module_expr1) -> Hashtbl.add c name  (loc,  []); parse_module_expr c n module_expr1
    (* module rec mb *)
    | StRecMod(loc, module_binding1) -> parse_module_binding c n module_binding1
    (* module type s = mt *)
    | StMty(loc, name, module_type1) -> Hashtbl.add c name (loc,  []); parse_module_type c n module_type1
    (* open i *)
    | StOpn(loc, ident1) -> m := ident1::!m
    (* type t *)
    | StTyp(loc, ctyp1) -> parse_ctyp c n ctyp1
    (* value (rec)? bi *) 
    | StVal(loc, rec_flag, binding1) -> let bind = (parse_binding c n binding1) in Hashtbl.add c (snd bind) (fst bind,  [])
    (* $s$ *)
    | StAnt(loc, name) -> Hashtbl.add c name  (loc, [])
    (* st ; st *)
		| StSem(loc, str_item1, str_item2) -> parse_str_item c n m str_item1; parse_str_item c n m str_item2
		(* e *)
		| StExp(loc, expr1) -> parse_expr c n expr1; ()
		(* include me *)
    | StInc(loc, module_expr1) -> ()
    (* class type cict *)
    | StClt(loc, class_type1) -> ()
		(* class cice *)
    | StCls(loc, class_expr1) -> ()
and parse_class_type c n = function
    | CtNil(loc) -> ()
    (* (virtual)? i ([ t ])? *)
    | CtCon(loc, virtual_flag, ident1, ctyp1) -> parse_ident c n ident1; parse_ctyp c n ctyp1; ()
    (* [t]) -> ct *)
    | CtFun(loc, ctyp1, class_type1) -> parse_ctyp c n ctyp1; parse_class_type c n class_type1; ()
    (* object ((t))? (csg)? end *)
    | CtSig(loc, ctyp1, class_sig_item1) -> parse_ctyp c n ctyp1; parse_class_sig_item c n class_sig_item1; ()
    (* ct, ct *)
    | CtAnd(loc, class_type1, class_type2) -> parse_class_type c n class_type1; parse_class_type c n class_type2; ()
    (* ct : ct *)
    | CtCol(loc, class_type1, class_type2) -> parse_class_type c n class_type1; parse_class_type c n class_type2; ()
    (* ct = ct *)
    | CtEq(loc, class_type1, class_type2) -> parse_class_type c n class_type1; parse_class_type c n class_type2; ()
    (* $s$ *)
    | CtAnt(loc, name) -> ()
and parse_class_sig_item c n = function
    | CgNil(loc) -> ()
    (* type t = t *)
    | CgCtr(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2; ()
    (* csg ; csg *)
    | CgSem(loc, class_sig_item1, class_sig_item2) -> parse_class_sig_item c n class_sig_item1; parse_class_sig_item c n class_sig_item2; ()
    (* inherit ct *)
    | CgInh(loc, class_type1) -> parse_class_type c n class_type1; ()
    (* method s : t or method private s : t *)
    | CgMth(loc, name, private_flag, ctyp1) -> parse_ctyp c n ctyp1; ()
    (* value (virtual)? (mutable)? s : t *)
    | CgVal(loc, name, mutable_flag, virtual_flag, ctyp1) -> parse_ctyp c n ctyp1; ()
    (* method virtual (private)? s : t *)
    | CgVir(loc, name, private_flag, ctyp1) -> parse_ctyp c n ctyp1; ()
    (* $s$ *)
    | CgAnt(loc, name) -> ()
and parse_class_expr c n = function
    | CeNil(loc) -> ();
    (* ce e *)
    | CeApp(loc, class_expr1, expr1) -> parse_class_expr c n class_expr1; parse_expr c n expr1; ()
    (* (virtual)? i ([ t ])? *)
    | CeCon(loc, virtual_flag, ident1, ctyp1) -> parse_ident c n ident1; parse_ctyp c n ctyp1;()
    (* fun p -> ce *)
    | CeFun(loc, patt1, class_expr1) -> parse_patt c n patt1; parse_class_expr c n class_expr1;()
    (* let (rec)? bi in ce *)
    | CeLet(loc, rec_flag, binding1, class_expr1) -> parse_binding c n binding1; parse_class_expr c n class_expr1;()
    (* object ((p))? (cst)? end *)
    | CeStr(loc, patt1, class_str_item1) -> parse_patt c n patt1; parse_class_str_item c n class_str_item1;()
    (* ce : ct *)
    | CeTyc(loc, class_expr1, class_type1) -> parse_class_expr c n class_expr1; parse_class_type c n class_type1;()
    (* ce, ce *)
    | CeAnd(loc, class_expr1, class_expr2) -> parse_class_expr c n class_expr1; parse_class_expr c n class_expr2;()
    (* ce = ce *)
    | CeEq(loc, class_expr1, class_expr2) -> parse_class_expr c n class_expr1; parse_class_expr c n class_expr2;()
    (* $s$ *)
    | CeAnt(loc, name) -> ();
and parse_class_str_item c n = function
    | CrNil(loc) ->()
    (* cst ; cst *)
    | CrSem(loc, class_str_item1, class_str_item2) -> parse_class_str_item c n class_str_item1; parse_class_str_item c n class_str_item2; ()
    (* type t = t *)
    | CrCtr(loc, ctyp1, ctyp2) -> parse_ctyp c n ctyp1; parse_ctyp c n ctyp2; ()
    (* inherit ce or inherit ce as s *)
    | CrInh(loc, override_flag, class_expr1, name) -> parse_class_expr c n class_expr1; ()
    (* initializer e *)
    | CrIni(loc, expr1) -> parse_expr c n expr1; ()
    (* method (private)? s : t = e or method (private)? s = e *)
    | CrMth(loc, name, override_flag, private_flag, expr1, ctyp1) -> parse_expr c n expr1; parse_ctyp c n ctyp1; ()
    (* value (mutable)? s = e *)
    | CrVal(loc, name, override_flag, mutable_flag, expr1) -> parse_expr c n expr1; ()
    (* method virtual (private)? s : t *)
    | CrVir(loc, name, private_flag, ctyp1) -> parse_ctyp c n ctyp1; ()
    (* value virtual (mutable)? s : t *)
    | CrVvr(loc, name, mutable_flag , ctyp1) -> parse_ctyp c n ctyp1; ()
    (* $s$ *)
    | CrAnt(loc, name) -> ()
and parse_ctyps = function
    | _ -> ()
and parse_constraints l = function
		| (ctyp1, ctyp2):: r -> parse_ctyp l ctyp1; parse_ctyp l ctyp2; parse_constraints l r;
		| _ -> ()
and parse_option_ident l = function
    | OSome(x) -> parse_ident l x; ()
		| _ -> ()
 
let rec parse_modulist = function
    | [IdUid (loc, name)] -> print_string name
    | IdUid (loc, name)::q -> print_string (name^" ;"); parse_modulist q;
    | _ -> ()

let parse_common k v = 
	  print_string ("\n"^ k^"@_def"^(string_of_loc(fst v))^"\n\t@_uses");
		List.iter (function loc -> print_string ((string_of_loc loc)^";")) (snd v)

let parse_ast_in_xml channel =
	match Deserializerp4.deserialize_chan channel with
	| Some parse_tree ->
			let common = (Hashtbl.create 50 : (string,loc_locList) Hashtbl.t) 
			and names = (Hashtbl.create 50 : (string,range_genName list) Hashtbl.t) 
			and moduList = ref [] in
			parse_str_item common names moduList parse_tree;
(*			parse_modulist Format.str_formatter !moduList;*)
			Hashtbl.iter parse_common common;
	| None -> ()

