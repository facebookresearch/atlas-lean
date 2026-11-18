/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Combinatorics.SecondMomentMethod

@[expose] public section

open MeasureTheory ProbabilityTheory
  MathlibExt.Probability.Combinatorics.SecondMomentMethod

namespace MathlibExtTest.Probability.Combinatorics.SecondMomentMethod

/-- The expected count of three sure events is `3`. -/
example : expectedCount (Measure.dirac ()) (fun _ : Fin 3 => (Set.univ : Set Unit)) = 3 := by
  simp [expectedCount]

/-- With the complete dependency graph every pair of three sure events is dependent, so
`Δ = 3 · 2 = 6`. -/
example :
    dependentPairSum (Measure.dirac ()) (fun _ : Fin 3 => (Set.univ : Set Unit)) ⊤ = 6 := by
  simp [dependentPairSum, Fin.sum_univ_succ]
  norm_num

/-- Non-vacuity of the counting form: the hypotheses hold for the complete dependency graph
(the independence hypothesis is then empty) as soon as `μ > 0`. -/
example : (Measure.dirac ()).real {ω : Unit | ∀ _i : Fin 3, ω ∉ (Set.univ : Set Unit)} ≤
    (expectedCount (Measure.dirac ()) (fun _ : Fin 3 => (Set.univ : Set Unit)) +
      dependentPairSum (Measure.dirac ()) (fun _ : Fin 3 => (Set.univ : Set Unit)) ⊤) /
      expectedCount (Measure.dirac ()) (fun _ : Fin 3 => (Set.univ : Set Unit)) ^ 2 :=
  measureReal_forall_not_mem_le _ (fun _ => MeasurableSet.univ) ⊤
    (fun i j hij h => absurd ((SimpleGraph.top_adj i j).mpr hij) h) (by simp [expectedCount])

/-- Non-vacuity with the empty dependency graph: sure events are pairwise independent, and
the variance bound reads `0 ≤ μ + 0`. -/
example : variance (count (fun _ : Fin 3 => (Set.univ : Set Unit))) (Measure.dirac ()) ≤
    expectedCount (Measure.dirac ()) (fun _ : Fin 3 => (Set.univ : Set Unit)) +
      dependentPairSum (Measure.dirac ()) (fun _ : Fin 3 => (Set.univ : Set Unit)) ⊥ :=
  variance_sum_indicator_le _ (fun _ => MeasurableSet.univ) ⊥
    (fun _ _ _ _ => by simp)

/-- The second moment method for a constant variable `X = 1`: `P(X = 0) ≤ 0 / 1`. -/
example : (Measure.dirac ()).real {ω : Unit | (fun _ => (1 : ℝ)) ω = 0} ≤
    variance (fun _ : Unit => (1 : ℝ)) (Measure.dirac ()) /
      ((Measure.dirac ())[fun _ : Unit => (1 : ℝ)]) ^ 2 :=
  measureReal_eq_zero_le_variance_div_sq (memLp_const 1) (by simp)

/-- The first moment method for a constant variable `X = 2`. -/
example : (Measure.dirac ()).real {ω : Unit | 1 ≤ (fun _ => (2 : ℝ)) ω} ≤
    ∫ ω, (fun _ : Unit => (2 : ℝ)) ω ∂(Measure.dirac ()) :=
  measureReal_one_le_le_integral (Filter.Eventually.of_forall fun _ => by norm_num)
    (integrable_const 2)

/-- The Cauchy–Schwarz form for a constant variable `X = 2`. -/
example : (∫ ω, (fun _ : Unit => (2 : ℝ)) ω ∂(Measure.dirac ())) ^ 2 ≤
    (∫ ω, (fun _ : Unit => (2 : ℝ)) ω ^ 2 ∂(Measure.dirac ())) *
      (Measure.dirac ()).real {ω : Unit | 0 < (fun _ => (2 : ℝ)) ω} :=
  sq_integral_le_integral_sq_mul_measureReal_pos
    (Filter.Eventually.of_forall fun _ => by norm_num) (memLp_const 2)

end MathlibExtTest.Probability.Combinatorics.SecondMomentMethod
