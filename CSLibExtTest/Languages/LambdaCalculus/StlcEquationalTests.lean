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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Equational

@[expose] public section

/-!
# Client tests for the STLC equational theory

The Bool model exercises beta, eta, congruence, and semantic equality of
substitutions through the public API.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.EquationalTests

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

def BoolModel : Unit → Type := fun _ ↦ Bool

def identity : Tm [] (O ⇒ O) := .lam (.var .zero)

def openFunction : Tm [O ⇒ O] (O ⇒ O) := .var .zero

example : SemEq BoolModel (.app (Tm.weaken identity) (.var (.zero : Var [O] O)))
    (.var (.zero : Var [O] O)) := SemEq.beta BoolModel (.var .zero) (.var .zero)

example : SemEq BoolModel
    (.lam (.app (Tm.weaken openFunction) (.var .zero))) openFunction :=
  SemEq.eta BoolModel openFunction

example {f g : Tm [O] (O ⇒ O)} {a b : Tm [O] O}
    (hfg : SemEq BoolModel f g) (hab : SemEq BoolModel a b) :
    SemEq BoolModel (.app f a) (.app g b) := SemEq.app hfg hab

example {t u : Tm [O] O} (h : SemEq BoolModel t u) (σ : Sub [O] [O, O]) :
    SemEq BoolModel (Tm.subst σ t) (Tm.subst σ u) := h.subst σ

example (t : Tm [O] O) {σ τ : Sub [O] [O, O]} (h : SubSemEq BoolModel σ τ) :
    SemEq BoolModel (Tm.subst σ t) (Tm.subst τ t) := SemEq.subst_congr t h

example {t u : Tm [O] O} (h : Step t u) : SemEq BoolModel t u := SemEq.of_step h

example : Equivalence (@SemEq Unit O [O] BoolModel) := SemEq.equivalence BoolModel

#print axioms Cslib.Languages.LambdaCalculus.Stlc.SemEq.app
#print axioms Cslib.Languages.LambdaCalculus.Stlc.SemEq.lam
#print axioms Cslib.Languages.LambdaCalculus.Stlc.SemEq.beta
#print axioms Cslib.Languages.LambdaCalculus.Stlc.SemEq.eta
#print axioms Cslib.Languages.LambdaCalculus.Stlc.SemEq.subst_congr

end Cslib.Languages.LambdaCalculus.Stlc.EquationalTests
