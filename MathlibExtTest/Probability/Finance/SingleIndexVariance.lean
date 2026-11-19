/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.SingleIndexVariance
import Mathlib.Tactic.NormNum

/-!
# Tests for the single-index variance decomposition

A concrete non-degenerate model: four equally likely states (`Fin 4` with the
quarter-scaled counting measure), market return `RM = (1, 1, -1, -1)` and residual
`ε = (1, -1, 1, -1)`. Both are nonconstant, with `Var[RM] = Var[ε] = 1`, and they are
orthogonal, `cov[RM, ε] = 0`; these values are computed directly as finite sums. The
theorem is then applied with its hypotheses discharged by those computations. With
`α = 3` and `β = 2` the single-index return is `(6, 4, 2, 0)`; its variance `5` is also
computed directly and matches `β ^ 2 * Var[RM] + Var[ε] = 4 * 1 + 1`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Finance.SingleIndexVariance

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Finance.SingleIndexVariance

/-- The uniform law on four states. -/
noncomputable def unif4 : Measure (Fin 4) :=
  (4⁻¹ : ENNReal) • Measure.count

instance : IsProbabilityMeasure unif4 := by
  constructor
  rw [unif4, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  simp [ENat.card_eq_coe_fintype_card]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma unif4_real_singleton (i : Fin 4) : unif4.real {i} = 1 / 4 := by
  simp [unif4, measureReal_def]

lemma integral_unif4 (f : Fin 4 → ℝ) :
    ∫ i, f i ∂unif4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  rw [integral_fintype Integrable.of_finite]
  simp only [unif4_real_singleton, smul_eq_mul, Fin.sum_univ_four]
  ring

/-- The market return `(1, 1, -1, -1)`. -/
def marketReturn : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- The residual `(1, -1, 1, -1)`. -/
def residual : Fin 4 → ℝ := ![1, -1, 1, -1]

lemma integral_marketReturn : ∫ i, marketReturn i ∂unif4 = 0 := by
  rw [integral_unif4]
  norm_num [marketReturn]

lemma integral_residual : ∫ i, residual i ∂unif4 = 0 := by
  rw [integral_unif4]
  norm_num [residual]

/-- The residual is orthogonal to the market: `cov[RM, ε] = 0`. -/
theorem covariance_marketReturn_residual : cov[marketReturn, residual; unif4] = 0 := by
  rw [covariance, integral_marketReturn, integral_residual, integral_unif4]
  norm_num [marketReturn, residual]

/-- The market return is nonconstant: `Var[RM] = 1`. -/
theorem variance_marketReturn : Var[marketReturn; unif4] = 1 := by
  rw [variance_eq_integral Measurable.of_discrete.aemeasurable, integral_marketReturn,
    integral_unif4]
  norm_num [marketReturn]

/-- The residual is nonconstant: `Var[ε] = 1`. -/
theorem variance_residual : Var[residual; unif4] = 1 := by
  rw [variance_eq_integral Measurable.of_discrete.aemeasurable, integral_residual,
    integral_unif4]
  norm_num [residual]

/-- Direct computation: with `α = 3` and `β = 2` the return is `(6, 4, 2, 0)`, with
mean `3` and variance `5`. -/
theorem variance_singleIndexReturn :
    Var[singleIndexReturn 3 2 marketReturn residual; unif4] = 5 := by
  have hmean : ∫ i, singleIndexReturn 3 2 marketReturn residual i ∂unif4 = 3 := by
    rw [integral_unif4]
    norm_num [singleIndexReturn, marketReturn, residual]
  rw [variance_eq_integral Measurable.of_discrete.aemeasurable, hmean, integral_unif4]
  norm_num [singleIndexReturn, marketReturn, residual]

/-- The theorem on the concrete model, its hypotheses discharged by the computations
above. -/
example : Var[singleIndexReturn 3 2 marketReturn residual; unif4] =
    2 ^ 2 * Var[marketReturn; unif4] + Var[residual; unif4] :=
  singleIndex_variance_decomposition 3 2 marketReturn residual MemLp.of_discrete
    MemLp.of_discrete covariance_marketReturn_residual

/-- The decomposition agrees with the direct computation: `4 * 1 + 1 = 5`. -/
example : (2 : ℝ) ^ 2 * Var[marketReturn; unif4] + Var[residual; unif4] =
    Var[singleIndexReturn 3 2 marketReturn residual; unif4] := by
  rw [variance_marketReturn, variance_residual, variance_singleIndexReturn]
  norm_num

end MathlibExtTest.Probability.Finance.SingleIndexVariance
