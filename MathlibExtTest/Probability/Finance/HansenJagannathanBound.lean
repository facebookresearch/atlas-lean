/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.HansenJagannathanBound
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Tests for the Hansen--Jagannathan bound

Equality case on two states: `P = ![1/2, 1/2]`, `m = ![9/10, 11/10]`,
`Re = ![11/10, -9/10]`, with `E[m] = 1`, `E[Re] = 1/10`, `E[m * Re] = 0`,
`Var(m) = 1/100`, `Var(Re) = 1`, so both sides of the bound equal `1/10`. Also a
direct check of the covariance Cauchy--Schwarz lemma on the same example.

Zero-mass boundary: adding a third state with probability `0` and arbitrary payoffs,
`P₀ = ![1/2, 1/2, 0]`, leaves every moment and both sides of the bound unchanged, and the
bound still applies although `P₀` is not strictly positive.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Finance.HansenJagannathanBound

open _root_.MathlibExt.Probability.Finance.HansenJagannathanBound
open _root_.MathlibExt.Probability.FiniteProbability



noncomputable def P : Fin 2 → ℝ := ![1/2, 1/2]
noncomputable def m : Fin 2 → ℝ := ![9/10, 11/10]
noncomputable def Re : Fin 2 → ℝ := ![11/10, -9/10]

theorem exp_m : expectation P m = 1 := by
  unfold expectation P m
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem exp_Re : expectation P Re = 1 / 10 := by
  unfold expectation P Re
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem exp_mRe : expectation P (fun ω => m ω * Re ω) = 0 := by
  unfold expectation P m Re
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem var_m : variance P m = 1 / 100 := by
  unfold variance
  rw [exp_m]
  unfold expectation P m
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem var_Re : variance P Re = 1 := by
  unfold variance
  rw [exp_Re]
  unfold expectation P Re
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem hP_pos : ∀ ω, 0 < P ω := by
  intro ω
  fin_cases ω <;> unfold P <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem hP_sum : ∑ ω, P ω = 1 := by
  unfold P
  rw [Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem cs_example : (covariance P m Re) ^ 2 ≤ variance P m * variance P Re := by
  apply covariance_sq_le_variance_mul_variance
  intro ω
  exact le_of_lt (hP_pos ω)

theorem hj_bound_example :
    |expectation P Re| / Real.sqrt (variance P Re)
      ≤ Real.sqrt (variance P m) / expectation P m := by
  apply hansenJagannathan_bound (fun ω => le_of_lt (hP_pos ω)) hP_sum exp_mRe
  · rw [exp_m]; norm_num
  · rw [var_Re]; norm_num

theorem lhs_eq : |expectation P Re| / Real.sqrt (variance P Re) = 1 / 10 := by
  rw [exp_Re, var_Re, Real.sqrt_one]
  norm_num

theorem rhs_eq : Real.sqrt (variance P m) / expectation P m = 1 / 10 := by
  rw [var_m, exp_m]
  have hsqrt : Real.sqrt (1/100 : ℝ) = 1/10 := by
    rw [show (1/100 : ℝ) = (1/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt, div_one]

noncomputable def P₀ : Fin 3 → ℝ := ![1/2, 1/2, 0]
noncomputable def m₀ : Fin 3 → ℝ := ![9/10, 11/10, 3]
noncomputable def Re₀ : Fin 3 → ℝ := ![11/10, -9/10, 5]

theorem P₀_not_pos : ¬ ∀ ω, 0 < P₀ ω := by
  intro h
  have h2 := h 2
  simp [P₀] at h2

theorem P₀_nonneg : ∀ ω, 0 ≤ P₀ ω := by
  intro ω
  fin_cases ω <;> simp [P₀]

theorem P₀_sum : ∑ ω, P₀ ω = 1 := by
  unfold P₀
  rw [Fin.sum_univ_three]
  simp
  norm_num

theorem exp_m₀ : expectation P₀ m₀ = 1 := by
  unfold expectation P₀ m₀
  rw [Fin.sum_univ_three]
  simp
  norm_num

theorem exp_Re₀ : expectation P₀ Re₀ = 1 / 10 := by
  unfold expectation P₀ Re₀
  rw [Fin.sum_univ_three]
  simp
  norm_num

theorem exp_mRe₀ : expectation P₀ (fun ω => m₀ ω * Re₀ ω) = 0 := by
  unfold expectation P₀ m₀ Re₀
  rw [Fin.sum_univ_three]
  simp
  norm_num

theorem var_m₀ : variance P₀ m₀ = 1 / 100 := by
  unfold variance
  rw [exp_m₀]
  unfold expectation P₀ m₀
  rw [Fin.sum_univ_three]
  simp
  norm_num

theorem var_Re₀ : variance P₀ Re₀ = 1 := by
  unfold variance
  rw [exp_Re₀]
  unfold expectation P₀ Re₀
  rw [Fin.sum_univ_three]
  simp
  norm_num

theorem hj_bound_zero_mass :
    |expectation P₀ Re₀| / Real.sqrt (variance P₀ Re₀)
      ≤ Real.sqrt (variance P₀ m₀) / expectation P₀ m₀ := by
  apply hansenJagannathan_bound P₀_nonneg P₀_sum exp_mRe₀
  · rw [exp_m₀]; norm_num
  · rw [var_Re₀]; norm_num

theorem lhs_eq₀ : |expectation P₀ Re₀| / Real.sqrt (variance P₀ Re₀) = 1 / 10 := by
  rw [exp_Re₀, var_Re₀, Real.sqrt_one]
  norm_num

theorem rhs_eq₀ : Real.sqrt (variance P₀ m₀) / expectation P₀ m₀ = 1 / 10 := by
  rw [var_m₀, exp_m₀]
  have hsqrt : Real.sqrt (1/100 : ℝ) = 1/10 := by
    rw [show (1/100 : ℝ) = (1/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt, div_one]


end MathlibExtTest.Probability.Finance.HansenJagannathanBound
