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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.StrongNormalization

@[expose] public section

/-!
# Client tests for strong normalization of STLC

The examples expose accessibility, exclusion of infinite runs, and the exact
two-step cost of a nested identity application.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.StrongNormalizationTests

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

def identity (A : Ty Unit) : Tm [] (A ⇒ A) := .lam (.var .zero)

def nestedIdentity : Tm [] (O ⇒ O) :=
  .app (identity (O ⇒ O)) (.app (identity (O ⇒ O)) (identity O))

example : StronglyNormalizing nestedIdentity := stronglyNormalizing_closed nestedIdentity

example : ¬InfiniteReduction nestedIdentity := no_infinite_reduction nestedIdentity

example : StepsN 2 nestedIdentity (identity O) := by
  apply StepsN.head (.appArg (.lam _) (.beta (.lam _)))
  apply StepsN.head (.beta (.lam _))
  exact .refl _

example : ∃ n v, StepsN n nestedIdentity v ∧ Value v := by
  rcases exists_unique_cost_value nestedIdentity with ⟨n, v, hsteps, hv, _⟩
  exact ⟨n, v, hsteps, hv⟩

example {n : Nat} {v : Tm [] (O ⇒ O)} (h : StepsN n nestedIdentity v) (hv : Value v) :
    n = 2 ∧ v = identity O := by
  exact StepsN.value_cost_unique h hv (by
    apply StepsN.head (.appArg (.lam _) (.beta (.lam _)))
    apply StepsN.head (.beta (.lam _))
    exact .refl _) (.lam _)

example {n m : Nat} {t v w : Tm [O] O} (htv : StepsN n t v) (hv : Value v)
    (htw : StepsN m t w) (hw : Value w) : n = m ∧ v = w :=
  StepsN.value_cost_unique htv hv htw hw

/-- Closed-term termination, restated with the upstream predicate `Relation.SN`. -/
example : Relation.SN Step nestedIdentity :=
  stronglyNormalizing_iff_sn.mp (stronglyNormalizing_closed nestedIdentity)

/-- Upstream `Relation.SN` lemmas apply after the bridge: a one-step reduct stays SN. -/
example {t' : Tm [] (O ⇒ O)} (h : Step nestedIdentity t') : StronglyNormalizing t' :=
  stronglyNormalizing_iff_sn.mpr ((stronglyNormalizing_iff_sn.mp
    (stronglyNormalizing_closed nestedIdentity)).inv h)

#print axioms Cslib.Languages.LambdaCalculus.Stlc.stronglyNormalizing_iff_sn
#print axioms Cslib.Languages.LambdaCalculus.Stlc.stronglyNormalizing_closed
#print axioms Cslib.Languages.LambdaCalculus.Stlc.no_infinite_reduction
#print axioms Cslib.Languages.LambdaCalculus.Stlc.StepsN.value_cost_unique
#print axioms Cslib.Languages.LambdaCalculus.Stlc.exists_unique_cost_value

end Cslib.Languages.LambdaCalculus.Stlc.StrongNormalizationTests
