/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Combinatorics.JansonInequality

import Mathlib.Tactic.NormNum

open MeasureTheory unitInterval MathlibExt.Probability.Combinatorics.RandomSubset
open MathlibExt.Probability.JansonInequalityWanted

namespace MathlibExtTest.Probability.Combinatorics.JansonInequality

/-- Avoiding a singleton also avoids its superset. The two ordered overlap terms
cancel the contribution of the superset to the exponent. -/
example (p : Bool → I) :
    (randomSubsetLaw p).real {ω | ω true = false} ≤ Real.exp (-(p true : ℝ)) := by
  let S : Fin 2 → Finset Bool := ![{true}, {true, false}]
  have hevent : {ω | ∀ i, ω ∉ containsEvent (S i)} = {ω : Bool → Bool | ω true = false} := by
    ext ω
    simp +contextual [Fin.forall_fin_two, S, containsEvent]
  rw [← hevent]
  refine (janson_inequality p S).trans_eq (congrArg Real.exp ?_)
  norm_num [jansonMu, jansonDelta, Fin.sum_univ_two, S, containsEvent_inter,
    randomSubsetLaw_real_containsEvent]
  ring

/-- With no events, both sums vanish and the bound is attained. -/
example {α : Type*} [Fintype α] [DecidableEq α] (p : α → I) (S : Empty → Finset α) :
    (randomSubsetLaw p).real {ω | ∀ i, ω ∉ containsEvent (S i)} =
      Real.exp (-(jansonMu p S ^ 2 / (2 * jansonDelta p S))) := by
  simp [jansonMu, jansonDelta]

/-- Three copies of a fair singleton give six ordered pairs and thinning probability one half. -/
example (p : Bool → I) (hp : (p true : ℝ) = 1 / 2) :
    (randomSubsetLaw p).real {ω | ω true = false} ≤ Real.exp (-(3 / 8)) := by
  let S (_ : Fin 3) : Finset Bool := {true}
  have hμ : jansonMu p S = 3 / 2 := by
    norm_num [jansonMu, S, hp, randomSubsetLaw_real_containsEvent]
  have hΔ : jansonDelta p S = 3 := by
    norm_num [jansonDelta, Fin.sum_univ_succ, S, hp, containsEvent_inter,
      randomSubsetLaw_real_containsEvent]
  have hevent : {ω | ∀ i, ω ∉ containsEvent (S i)} = {ω : Bool → Bool | ω true = false} := by
    ext ω
    simp [S, containsEvent]
  have h := janson_inequality_of_le p S (by rw [hμ, hΔ]; norm_num)
  rw [hevent, hμ, hΔ] at h
  norm_num only at h
  exact h

end MathlibExtTest.Probability.Combinatorics.JansonInequality
