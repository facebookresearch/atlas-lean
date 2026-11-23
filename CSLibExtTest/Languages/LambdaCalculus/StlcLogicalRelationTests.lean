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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.LogicalRelation

@[expose] public section

/-!
# Client tests for the STLC logical relation

The examples exercise the public normalization API on closed applications and
the fundamental theorem on an open term.  The concrete reductions cross beta
redexes, so they also check that the call-by-value compatibility lemmas line up
with capture-avoiding instantiation.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.LogicalRelationTests

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

/-- Polymorphic (at the meta-level) object-language identity. -/
def identity (A : Ty Unit) : Tm [] (A ⇒ A) := .lam (.var .zero)

/-- Applying identity at a function type to identity at a base type. -/
def identityApplication : Tm [] (O ⇒ O) := .app (identity (O ⇒ O)) (identity O)

example : Step identityApplication (identity O) := by
  exact .beta (.lam _)

example : Steps identityApplication (identity O) := by
  exact Relation.ReflTransGen.single (.beta (.lam _))

example : Terminates identityApplication := terminates_closed identityApplication

example : Reducible identityApplication := reducible_closed identityApplication

example : ∃ v, Steps identityApplication v ∧ Value v :=
  terminates_closed identityApplication

/-- The open function `fun f => f` used to exercise closing substitutions. -/
def openFunction : Tm [O ⇒ O] (O ⇒ O) := .var .zero

def closeOpenFunction : Sub [O ⇒ O] [] := Sub.cons (identity O) Sub.id

example : ReducibleSub closeOpenFunction := by
  apply ReducibleSub.cons (ReducibleSub.empty Sub.id)
  exact reducible_closed (identity O)

example : Reducible (Tm.subst closeOpenFunction openFunction) := by
  exact fundamental openFunction closeOpenFunction (by
    apply ReducibleSub.cons (ReducibleSub.empty Sub.id)
    exact reducible_closed (identity O))

example : Tm.subst closeOpenFunction openFunction = identity O := rfl

example {t t' : Tm [] (O ⇒ O)} (h : Steps t t') : Reducible t ↔ Reducible t' :=
  Reducible.iff_of_steps h

#print axioms Cslib.Languages.LambdaCalculus.Stlc.Steps.suffix_of_value
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Reducible.forward
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Reducible.anti
#print axioms Cslib.Languages.LambdaCalculus.Stlc.fundamental
#print axioms Cslib.Languages.LambdaCalculus.Stlc.terminates_closed

end Cslib.Languages.LambdaCalculus.Stlc.LogicalRelationTests
