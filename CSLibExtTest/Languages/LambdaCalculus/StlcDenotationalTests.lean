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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Denotational

@[expose] public section

/-!
# Client tests for STLC denotational semantics

The base type is interpreted as `Bool`.  Tests cover open environments,
substitution, beta reduction, and agreement of operational and denotational
evaluation.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.DenotationalTests

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

def BoolModel : Unit → Type := fun _ ↦ Bool

def identity (A : Ty Unit) : Tm [] (A ⇒ A) := .lam (.var .zero)

def emptyEnv : Env BoolModel [] := fun x ↦ nomatch x

def chooseNewest : Tm [O, O] O := .var .zero

def twoBooleans : Env BoolModel [O, O]
  | _, .zero => true
  | _, .succ .zero => false
  | _, .succ (.succ x) => nomatch x

example : Tm.denote BoolModel chooseNewest twoBooleans = true := rfl

example : Tm.denote BoolModel (identity O) emptyEnv false = false := rfl

example (t : Tm [O] O) (η : Env BoolModel [O]) :
    Tm.denote BoolModel (Tm.instantiate (Tm.weaken (B := O) t) (.var .zero)) η =
      Tm.denote BoolModel t η := by
  rw [Tm.instantiate_weaken]

example (σ : Sub [O] [O, O]) (t : Tm [O] O) :
    Tm.denote BoolModel (Tm.subst σ t) twoBooleans =
      Tm.denote BoolModel t (Tm.denoteSub BoolModel σ twoBooleans) :=
  Tm.denote_subst BoolModel σ t twoBooleans

example : Tm.denote BoolModel (.app (identity (O ⇒ O)) (identity O)) emptyEnv =
    Tm.denote BoolModel (identity O) emptyEnv := by
  exact Step.denote_eq BoolModel (.beta (.lam _)) emptyEnv

example {t t' : Tm [] (O ⇒ O)} (h : Steps t t') :
    Tm.denote BoolModel t emptyEnv = Tm.denote BoolModel t' emptyEnv :=
  h.denote_eq BoolModel emptyEnv

#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.denote_rename
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.denote_subst
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.denote_instantiate
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Step.denote_eq
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Steps.denote_eq

end Cslib.Languages.LambdaCalculus.Stlc.DenotationalTests
