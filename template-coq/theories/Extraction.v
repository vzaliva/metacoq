(** Extraction setup for template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

(* From Template Require All. *)
Require Template.Ast.
Require Import Template.utils.
Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Inductive Datatypes.list => list [ "[]" "(fun (x, xs) -> x :: xs)" ] "(fun on_nil on_cons -> function [] -> on_nil () | x :: xs -> on_cons x xs)".

Extract Inductive Ast.recursivity_kind => "Declarations.recursivity_kind" [ "Declarations.Finite" "Declarations.CoFinite" "Declarations.BiFinite" ].

Extract Constant utils.ascii_compare =>
 "fun x y -> match Char.compare x y with 0 -> Eq | x when x < 0 -> Lt | _ -> Gt".

Extract Inductive BasicAst.cast_kind => "Constr.cast_kind"
  [ "Constr.VMcast" "Constr.NATIVEcast"
    "Constr.DEFAULTcast" "Constr.REVERTcast" ].

Extraction Blacklist config uGraph univ Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Logic Common.
Set Warnings "-extraction-opaque-accessed".

Require Export Template.Ast.

Cd "gen-src".

Require Import Template.TemplateMonad.Extractable.

Recursive Extraction Library Extractable.

Cd "..".