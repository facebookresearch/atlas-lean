/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.OLSConsistency

namespace MathlibExtTest.LinearModelOLSConsistency

open Matrix MeasureTheory ProbabilityTheory Filter Finset Topology
  MathlibExt.Probability.Statistics.LinearModel

open scoped Function

/-- Entries of the constant `Fin 1` vector `![1]`. -/
theorem vec_single_one (a : Fin 1) : (![1] : Fin 1 → ℝ) a = 1 := by
  have ha : a = 0 := Fin.eq_zero a
  subst ha
  exact Matrix.cons_val_zero _ _

/-- Entries of the constant `Fin 1` vector `![3]`. -/
theorem vec_single_three (a : Fin 1) : (![3] : Fin 1 → ℝ) a = 3 := by
  have ha : a = 0 := Fin.eq_zero a
  subst ha
  exact Matrix.cons_val_zero _ _

/-- The population Gram of the constant row `![1]` is `1`: the entry is
`∫ ω, 1 ∂μ = 1`. This checks the definition of `popGram`, not convergence. -/
theorem popGram_const_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    popGram (fun _ : Ω => ![1]) μ = 1 := by
  ext a b
  have hab : a = b := Subsingleton.elim a b
  subst hab
  have hreal : μ.real Set.univ = 1 := by
    simp [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  simp only [popGram, Matrix.of_apply, vec_single_one a, mul_one,
    integral_const, hreal, one_smul, Matrix.one_apply_eq]

/-- With `k = Fin 1`, regressors `X i ω = ![1]`, and observed responses
`Y i ω = ![1] ⬝ᵥ ![3] + 0 = 3` (coefficient `![3]`, zero errors), the OLS
estimator is exactly `![3]` for every positive `n` (sample Gram `[[1]]`,
sample moment `![3]`). This checks the definition of `olsSeqEstimator`,
not convergence. -/
theorem olsSeqEstimator_const {Ω : Type*} (ω : Ω) (n : ℕ) (hn : 0 < n) :
    olsSeqEstimator (fun _ _ => (![1] : Fin 1 → ℝ))
      (fun _ _ => (![1] : Fin 1 → ℝ) ⬝ᵥ (![3] : Fin 1 → ℝ) + 0) n ω = ![3] := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hdot : (![1] : Fin 1 → ℝ) ⬝ᵥ (![3] : Fin 1 → ℝ) = 3 := by
    simp [dotProduct]
  have hsum1 : (∑ i ∈ Finset.range n, (1 : ℝ)) = n := by simp
  have hsum3 : (∑ i ∈ Finset.range n, (3 : ℝ)) = (n : ℝ) * 3 := by simp
  have hQ : ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
      Matrix.vecMulVec (![1] : Fin 1 → ℝ) (![1] : Fin 1 → ℝ)) = 1 := by
    ext a b
    have hab : a = b := Subsingleton.elim a b
    subst hab
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      vec_single_one a, mul_one, smul_eq_mul]
    rw [hsum1, inv_mul_cancel₀ hn0, Matrix.one_apply_eq]
  have hG : ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
      (((![1] : Fin 1 → ℝ) ⬝ᵥ (![3] : Fin 1 → ℝ) + 0) • ![1])) =
      (![3] : Fin 1 → ℝ) := by
    ext a
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hdot, add_zero,
      vec_single_one a, mul_one, vec_single_three a]
    rw [hsum3, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  have h1inv : (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = 1 := inv_one
  simp only [olsSeqEstimator]
  rw [hQ, hG, h1inv, Matrix.one_mulVec]

end MathlibExtTest.LinearModelOLSConsistency
