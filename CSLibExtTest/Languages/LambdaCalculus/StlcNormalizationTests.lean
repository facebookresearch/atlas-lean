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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Normalization

@[expose] public section

/-!
# Client tests for STLC normalization corollaries

These examples use nested call-by-value applications to exercise uniqueness,
canonicity, and congruence of evaluation results through the public API.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.NormalizationTests

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

def identity (A : Ty Unit) : Tm [] (A ⇒ A) := .lam (.var .zero)

def twiceIdentity : Tm [] (O ⇒ O) :=
  .app (identity (O ⇒ O)) (.app (identity (O ⇒ O)) (identity O))

example : Normalizes twiceIdentity := normalizes_closed twiceIdentity

example : ∃ body : Tm [O] O, Steps twiceIdentity (.lam body) :=
  closed_function_evaluates_to_lam twiceIdentity

example {n m : Tm [] (O ⇒ O)} (hn : Steps twiceIdentity n) (hnf : Step.NormalForm n)
    (hm : Steps twiceIdentity m) (hmf : Step.NormalForm m) : n = m :=
  normalForm_unique hn hnf hm hmf

example {t v w : Tm [O] O} (htv : Steps t v) (hv : Value v)
    (htw : Steps t w) (hw : Value w) : v = w :=
  Steps.value_unique htv hv htw hw

example : SameResult twiceIdentity (identity O) := by
  apply SameResult.of_steps
  apply Relation.ReflTransGen.head (.appArg (.lam _) (.beta (.lam _)))
  exact Relation.ReflTransGen.single (.beta (.lam _))

example : SameResult
    (.app (identity ((O ⇒ O) ⇒ (O ⇒ O))) (identity (O ⇒ O)))
    (identity (O ⇒ O)) := by
  exact SameResult.of_steps (Relation.ReflTransGen.single (.beta (.lam _)))

example {f g : Tm [] ((O ⇒ O) ⇒ (O ⇒ O))} {a b : Tm [] (O ⇒ O)}
    (hfg : SameResult f g) (hab : SameResult a b) :
    SameResult (.app f a) (.app g b) := SameResult.app hfg hab

example : Equivalence (@SameResult Unit (O ⇒ O)) := sameResult_equivalence

example (t : Tm [] (.base ())) : False := no_closed_base () t

/-- Closed-term normalization, restated with the upstream predicate `Relation.Normalizable`. -/
example : Relation.Normalizable Step twiceIdentity :=
  normalizes_iff_normalizable.mp (normalizes_closed twiceIdentity)

/-- The bridge also runs backwards, from upstream normalizability to `Normalizes`. -/
example (t : Tm [] (O ⇒ O)) (h : Relation.Normalizable Step t) : Terminates t :=
  Normalizes.iff_terminates.mp (normalizes_iff_normalizable.mpr h)

#print axioms Cslib.Languages.LambdaCalculus.Stlc.normalizes_iff_normalizable
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Steps.value_unique
#print axioms Cslib.Languages.LambdaCalculus.Stlc.normalForm_unique
#print axioms Cslib.Languages.LambdaCalculus.Stlc.closed_function_evaluates_to_lam
#print axioms Cslib.Languages.LambdaCalculus.Stlc.no_closed_base
#print axioms Cslib.Languages.LambdaCalculus.Stlc.SameResult.app
#print axioms Cslib.Languages.LambdaCalculus.Stlc.sameResult_equivalence

end Cslib.Languages.LambdaCalculus.Stlc.NormalizationTests
