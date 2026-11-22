/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.CountData.ExactTest

@[expose] public section

open MeasureTheory ProbabilityTheory Real MathlibExt.Probability.Statistics.ExactTests
  MathlibExt.Probability.Statistics.MultipleTesting MathlibExt.Probability.Statistics.GLM.CountData
open scoped NNReal unitInterval

namespace MathlibExtTest.Probability.Statistics.GLM.CountData.ExactTest

/-! ### Likelihood, score, deviance -/

/-- With unit library size and `η = 0` the offset log-likelihood of a zero count is `-1`. -/
example : log (Po(countMean 1 0).real {0}) = -1 := by
  rw [log_poissonMeasure_countMean one_pos]
  simp

/-- The score of a count `y = 3` with library size `2` at `η = 0` is `3 - 2 = 1`. -/
example : HasDerivAt (fun η => log (Po(countMean 2 η).real {3})) 1 0 := by
  have h := hasDerivAt_log_poissonMeasure_countMean (s := 2) two_pos 3 0
  norm_num at h
  exact h

/-- Pooled-rate score equation: libraries of sizes `1, 3` with counts `2, 6` have score zero
exactly at fitted rate `e^η = 8 / 4 = 2`. -/
example (η : ℝ) :
    (∑ i : Fin 2, ((![2, 6] : Fin 2 → ℕ) i : ℝ)) -
        exp η * ∑ i : Fin 2, ((![1, 3] : Fin 2 → ℝ≥0) i : ℝ) = 0 ↔
      exp η = 2 := by
  rw [sum_score_eq_zero_iff Finset.univ (by simp [Fin.sum_univ_two]; norm_num)]
  simp [Fin.sum_univ_two]
  norm_num

/-- The deviance of a zero count against mean `3` is `6`. -/
example : poissonDeviance 0 3 = 6 := by
  rw [poissonDeviance_zero_left]
  norm_num

/-- Boundary: a perfect fit has zero deviance, and a misfit does not. -/
example : poissonDeviance 2 2 = 0 ∧ poissonDeviance 1 2 ≠ 0 :=
  ⟨(poissonDeviance_eq_zero_iff (by norm_num) (by norm_num)).2 rfl,
    fun h => absurd ((poissonDeviance_eq_zero_iff (by norm_num) (by norm_num)).1 h)
      (by norm_num)⟩

/-- The deviance as a likelihood ratio at a zero count is twice the fitted rate. -/
example : 2 * (log (Po(((0 : ℕ) : ℝ≥0)).real {0}) - log (Po(1).real {0})) = 2 := by
  rw [← poissonDeviance_eq_two_mul_log_ratio one_pos 0]
  simp [poissonDeviance]

example (y μ : ℝ) (hy : 0 ≤ y) (hμ : 0 < μ) : 0 ≤ poissonDeviance y μ :=
  poissonDeviance_nonneg hy hμ

/-! ### The exact test -/

/-- Equal library sizes give the fair coin. -/
example : (libraryFraction 1 1 : ℝ) = 1 / 2 := by
  simp only [coe_libraryFraction, NNReal.coe_one]
  norm_num

/-- Non-vacuity: the coordinates of `Po(s₁ r) ⊗ Po(s₂ r)` are independent Poisson counts with a
common rate, so the hypotheses of the exact-test theorems are satisfiable. -/
theorem witness (s₁ s₂ r : ℝ≥0) :
    HasLaw (fun ω : ℕ × ℕ => ω.1) Po(s₁ * r) (Po(s₁ * r).prod Po(s₂ * r)) ∧
      HasLaw (fun ω : ℕ × ℕ => ω.2) Po(s₂ * r) (Po(s₁ * r).prod Po(s₂ * r)) ∧
      IndepFun (fun ω : ℕ × ℕ => ω.1) (fun ω : ℕ × ℕ => ω.2) (Po(s₁ * r).prod Po(s₂ * r)) :=
  ⟨measurePreserving_fst.hasLaw, measurePreserving_snd.hasLaw,
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id⟩

/-- On the witness with equal library sizes and rate `1`, given a total of `2` reads the
condition-1 count is `1` with probability `C(2,1) / 4 = 1/2`. -/
example :
    ((Po(1 * 1).prod Po(1 * 1))[|{ω : ℕ × ℕ | ω.1 + ω.2 = 2}]).real {ω | ω.1 = 1} = 1 / 2 := by
  have h := witness 1 1 1
  rw [cond_measureReal_eq_binomial_libraryFraction (X := fun ω : ℕ × ℕ => ω.1)
    (Y := fun ω : ℕ × ℕ => ω.2) (by norm_num) measurable_fst measurable_snd h.1 h.2.1 h.2.2
    (measure_add_eq_ne_zero (by norm_num) one_pos h.1 h.2.1 h.2.2 2) 1,
    binomial_real_singleton]
  simp only [coe_libraryFraction, NNReal.coe_one]
  norm_num [Nat.choose]

/-- Conditional validity on the witness, given any total, for a positive rate. -/
example (s₁ s₂ r : ℝ≥0) (hs : 0 < s₁ + s₂) (hr : 0 < r) (n : ℕ) :
    IsValidPValue ((Po(s₁ * r).prod Po(s₂ * r))[|{ω : ℕ × ℕ | ω.1 + ω.2 = n}])
      (upperTailPValue Bin(n, libraryFraction s₁ s₂) fun ω : ℕ × ℕ => ω.1) :=
  have h := witness s₁ s₂ r
  isValidPValue_countExact_cond (X := fun ω : ℕ × ℕ => ω.1) (Y := fun ω : ℕ × ℕ => ω.2) hs
    measurable_fst measurable_snd h.1 h.2.1 h.2.2
    (measure_add_eq_ne_zero hs hr h.1 h.2.1 h.2.2 n)

/-- Conditional validity at rate `r = 0`: the total `0` is certain, so the positive-mass
hypothesis holds and the conditional guarantee applies without `r > 0`. -/
example (s₁ s₂ : ℝ≥0) (hs : 0 < s₁ + s₂) :
    IsValidPValue ((Po(s₁ * 0).prod Po(s₂ * 0))[|{ω : ℕ × ℕ | ω.1 + ω.2 = 0}])
      (upperTailPValue Bin(0, libraryFraction s₁ s₂) fun ω : ℕ × ℕ => ω.1) := by
  have h := witness s₁ s₂ 0
  refine isValidPValue_countExact_cond (X := fun ω : ℕ × ℕ => ω.1) (Y := fun ω : ℕ × ℕ => ω.2)
    hs measurable_fst measurable_snd h.1 h.2.1 h.2.2 ?_
  have h0 : {ω : ℕ × ℕ | ω.1 + ω.2 = 0} = {(0, 0)} := by
    ext ⟨a, b⟩; simp [Prod.ext_iff]
  rw [h0, ← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [poissonMeasure_singleton]

/-- Boundary: with no reads at all the exact p-value is `1` (nothing to reject). -/
example (s₁ s₂ : ℝ≥0) : countExactTail s₁ s₂ (0, 0) = 1 := by
  simp [countExactTail, upperTail]

/-- The exact p-value is valid on the witness, for every rate including `r = 0`. -/
example (s₁ s₂ r : ℝ≥0) (hs : 0 < s₁ + s₂) :
    IsValidPValue (Po(s₁ * r).prod Po(s₂ * r))
      (countExactPValue s₁ s₂ (fun ω : ℕ × ℕ => ω.1) fun ω => ω.2) :=
  have h := witness s₁ s₂ r
  isValidPValue_countExactPValue (X := fun ω : ℕ × ℕ => ω.1) (Y := fun ω : ℕ × ℕ => ω.2) hs
    measurable_fst measurable_snd h.1 h.2.1 h.2.2

/-- Non-vacuity of the multiple-testing wiring: one null gene observed on the witness. -/
example (s₁ s₂ r : ℝ≥0) (hs : 0 < s₁ + s₂) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion {0}
        (bhRejections (q / harmonic 1) fun _ : Fin 1 =>
          countExactPValue s₁ s₂ (fun ω : ℕ × ℕ => ω.1) (fun ω => ω.2) ω)
        ∂(Po(s₁ * r).prod Po(s₂ * r)) ≤ q * ({0} : Finset (Fin 1)).card / ((1 : ℕ) : ℝ) :=
  integral_fdp_bhRejections_countExact_le_of_arbitrary_dependence (m := 1)
    (μ := Po(s₁ * r).prod Po(s₂ * r)) hs (fun _ ω => ω.1) (fun _ ω => ω.2)
    (fun _ => measurable_fst) (fun _ => measurable_snd) {0} (fun _ => r)
    (fun _ _ => witness s₁ s₂ r) q hq₀ hq₁

end MathlibExtTest.Probability.Statistics.GLM.CountData.ExactTest
