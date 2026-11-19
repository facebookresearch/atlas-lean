/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.SubstitutionLaws

@[expose] public section

/-!
# Client tests for STLC substitution laws

These examples exercise composition, lifting, fusion, and capture avoidance
through the public API.  The open examples deliberately cross binders, where
an incorrect implementation would capture a free variable.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.SubstitutionLawsTests

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

def openIdentity : Tm [O] (O ⇒ O) := .lam (.var (.succ .zero))

def first : Tm [O, O] O := .var .zero

def second : Tm [O, O] O := .var (.succ .zero)

def swap : Sub [O, O] [O, O]
  | _, .zero => second
  | _, .succ .zero => first
  | _, .succ (.succ x) => nomatch x

def duplicateNewest : Sub [O, O] [O]
  | _, .zero => .var .zero
  | _, .succ .zero => .var .zero
  | _, .succ (.succ x) => nomatch x

def openFirst : Tm [O, O] (O ⇒ O) := .lam (.var (.succ .zero))

def openSecond : Tm [O, O] (O ⇒ O) := .lam (.var (.succ (.succ .zero)))

example (x : Var [O, O] O) : Sub.comp swap duplicateNewest x = duplicateNewest x := by
  cases x with
  | zero => rfl
  | succ x => cases x with
    | zero => rfl
    | succ x => nomatch x

example (x : Var [O, O] O) : Sub.comp swap swap x = Sub.id x := by
  cases x with
  | zero => rfl
  | succ x => cases x with
    | zero => rfl
    | succ x => nomatch x

example : Tm.subst swap openFirst = openSecond := by
  rfl

example :
    Tm.subst (Sub.lift duplicateNewest) (Tm.weaken (B := O) first) =
      Tm.weaken (B := O) (Tm.subst duplicateNewest first) := by
  exact Tm.subst_lift_weaken duplicateNewest first

example :
    Tm.rename (Var.lift (A := O) (Var.id : Ren [O] [O]))
        (Tm.weaken (B := O) openIdentity) = Tm.weaken (B := O) openIdentity := by
  rw [Tm.rename_weaken, Tm.rename_id]

example (body : Tm [O, O] O) (a : Tm [O] O) :
    Tm.rename (Var.id : Ren [O] [O]) (Tm.instantiate body a) =
      Tm.instantiate (Tm.rename (Var.lift Var.id) body) (Tm.rename Var.id a) := by
  exact Tm.rename_instantiate Var.id body a

example (σ : Sub [O] [O, O]) (body : Tm [O, O] O) (a : Tm [O] O) :
    Tm.subst σ (Tm.instantiate body a) =
      Tm.instantiate (Tm.subst (Sub.lift σ) body) (Tm.subst σ a) := by
  exact Tm.subst_instantiate σ body a

example (σ : Sub [O] [O, O]) (body : Tm [O, O] O) (a : Tm [O, O] O) :
    Tm.subst (Sub.cons a σ) body = Tm.instantiate (Tm.subst (Sub.lift σ) body) a := by
  exact Tm.subst_cons σ body a

example (ρ : Ren [O, O] [O, O]) (x : Var [O, O] O) :
    Sub.rename swap ρ x = Sub.comp swap (Sub.ofRen ρ) x := by
  exact Sub.rename_eq_comp_ofRen_apply swap ρ x

example (ρ : Ren [O, O] [O, O]) (x : Var [O, O, O] O) :
    Sub.rename (Sub.lift swap) (Var.lift ρ) x = Sub.lift (Sub.rename swap ρ) x := by
  exact Sub.rename_lift_apply swap ρ x

example (t : Tm [O] O) (a : Tm [O] O) :
    Tm.instantiate (Tm.weaken (B := O) t) a = t := by
  simp

#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.rename_subst
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.subst_rename
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.subst_subst
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Sub.comp_assoc_apply
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Sub.lift_comp_apply
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.rename_instantiate
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.subst_instantiate
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.subst_cons
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Sub.rename_lift_apply

end Cslib.Languages.LambdaCalculus.Stlc.SubstitutionLawsTests
