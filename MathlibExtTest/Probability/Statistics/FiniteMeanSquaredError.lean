/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FiniteMeanSquaredError

import Mathlib.Data.Fin.VecNotation
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ENNReal

open scoped ENNReal


namespace MathlibExtTest.Probability.Statistics.FiniteMeanSquaredError

open MathlibExt.Probability.FiniteProbability

/-- Uniform weights on three points. -/
noncomputable def pU : Fin 3 → ℝ := fun _ => 1 / 3

/-- A symmetric variable taking `-1, 0, 1`. -/
def sym : Fin 3 → ℝ := ![-1, 0, 1]

/-- Signed weights `2, -1`: normalized but not nonnegative. -/
def pS : Fin 2 → ℝ := ![2, -1]

/-- The variable `0, 1` on two points. -/
def xS : Fin 2 → ℝ := ![0, 1]

/-- the uniform `ℝ≥0∞` masses on three points sum to one (fixture fact). -/
theorem sum_qU_mass : ∑ _ : Fin 3, (3 : ℝ≥0∞)⁻¹ = 1 := by
  have h0 : (3 : ℝ≥0∞) ≠ 0 := by simp
  have ht : (3 : ℝ≥0∞) ≠ ∞ := by simp
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    ENNReal.mul_inv_cancel h0 ht]

/-- The uniform probability mass function on three points. -/
noncomputable def qU : PMF (Fin 3) :=
  PMF.ofFintype (fun _ => (3 : ℝ≥0∞)⁻¹) sum_qU_mass

/-- the uniform weights are normalized (fixture fact). -/
theorem sum_pU : ∑ i, pU i = 1 := by
  show ∑ _ : Fin 3, (1 / 3 : ℝ) = 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- the signed weights are normalized (fixture fact). -/
theorem sum_pS : ∑ i, pS i = 1 := by
  rw [Fin.sum_univ_two]; simp [pS]; norm_num

/-- (Y = X² with symmetric X): at target `1` the finite MSE of `sym²` splits as
its variance plus `(2/3 - 1)²`. -/
theorem symmetric_square_mse_split :
    expectation pU (fun i => (sym i ^ 2 - 1) ^ 2) =
      variance pU (fun i => sym i ^ 2) + (2 / 3 - 1) ^ 2 := by
  have hE : expectation pU (fun i => sym i ^ 2) = 2 / 3 := by
    simp [expectation, pU, sym, Fin.sum_univ_three]; norm_num
  rw [expectation_sq_sub_eq_variance_add_sq sum_pU _ 1, hE]

/-- (Y = X² with symmetric X): the identity at target `0` determines the
variance of `sym²` from its first two moments. -/
theorem symmetric_square_variance :
    variance pU (fun i => sym i ^ 2) = 2 / 9 := by
  have hE : expectation pU (fun i => sym i ^ 2) = 2 / 3 := by
    simp [expectation, pU, sym, Fin.sum_univ_three]; norm_num
  have hE4 : expectation pU (fun i => (sym i ^ 2 - 0) ^ 2) = 2 / 3 := by
    simp [expectation, pU, sym, Fin.sum_univ_three]; norm_num
  have h := expectation_sq_sub_eq_variance_add_sq sum_pU (fun i => sym i ^ 2) 0
  rw [hE4, hE] at h
  norm_num at h
  linarith

/-- (constant random variable): the identity forces zero variance for a
constant under any normalized weights. -/
theorem constant_variance_eq_zero {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∑ x, p x = 1) (c : ℝ) : variance p (fun _ => c) = 0 := by
  rw [variance_eq_sub hp]
  simp [expectation_const hp]

/-- (constant random variable): the finite MSE of a constant is its squared
bias. -/
theorem constant_mse_eq_sq_bias {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∑ x, p x = 1) (c θ : ℝ) :
    expectation p (fun x => ((fun _ : α => c) x - θ) ^ 2) =
      variance p (fun _ => c) + (c - θ) ^ 2 := by
  have hEc : expectation p (fun _ : α => c) = c := expectation_const hp c
  have h := expectation_sq_sub_eq_variance_add_sq hp (fun _ : α => c) θ
  rwa [hEc] at h

/-- (perfect positive linear relation): `Y = 2 X + 1` at target `0` has finite
MSE `4 Var X + 1 = 11/3`. -/
theorem positive_linear_mse :
    expectation pU (fun i => (2 * sym i + 1 - 0) ^ 2) = 11 / 3 := by
  simp [expectation, pU, sym, Fin.sum_univ_three]; norm_num

/-- (perfect negative linear relation): `Y = -X + 1` is unbiased for `1`, so
its finite MSE is its variance `Var X = 2/3`. -/
theorem negative_linear_mse :
    expectation pU (fun i => ((-1) * sym i + 1 - 1) ^ 2) = 2 / 3 := by
  simp [expectation, pU, sym, Fin.sum_univ_three]; norm_num

/-- the variance is below the finite MSE at a far target. -/
theorem variance_le_mse_far_target :
    variance pU sym ≤ expectation pU (fun i => (sym i - 5) ^ 2) := by
  exact variance_le_expectation_sq_sub sum_pU sym 5

/-- (zero mass): without normalization the identity fails; the zero weight on
one point gives MSE `0` at target `1` but variance plus squared bias `1`. -/
theorem zero_mass_identity_fails :
    expectation (fun _ : Fin 1 => (0 : ℝ)) (fun x => ((fun _ => (0 : ℝ)) x - 1) ^ 2) ≠
      variance (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 0) +
        (expectation (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 0) - 1) ^ 2 := by
  have hMSE : expectation (fun _ : Fin 1 => (0 : ℝ))
      (fun x => ((fun _ => (0 : ℝ)) x - 1) ^ 2) = 0 := by
    simp [expectation]
  have hVar : variance (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 0) = 0 := by
    simp [variance, expectation]
  have hE : expectation (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 0) = 0 := by
    simp [expectation]
  rw [hMSE, hVar, hE]
  norm_num

/-- (signed weights): the identity holds for normalized signed weights. -/
theorem signed_weights_identity :
    expectation pS (fun i => (xS i - 0) ^ 2) = variance pS xS + (expectation pS xS - 0) ^ 2 := by
  exact expectation_sq_sub_eq_variance_add_sq sum_pS xS 0

/-- (signed weights): the variance under signed weights is negative, so the
statistical reading needs nonnegative weights. -/
theorem signed_weights_variance_neg : variance pS xS = -2 := by
  have hE : expectation pS xS = -1 := by
    simp [expectation, pS, xS, Fin.sum_univ_two]
  have hE2 : expectation pS (fun x => xS x ^ 2) = -1 := by
    simp [expectation, pS, xS, Fin.sum_univ_two]
  rw [variance_eq_sub sum_pS, hE2, hE]
  norm_num

/-- (bridge): the source finite MSE of `sym` at target `0` under the uniform
probability mass function on three points is `2/3`. -/
theorem uniform_bridge_mse :
    MathlibExt.Probability.Statistics.EstimationRisk.meanSquaredError sym
        qU.toMeasure.toProbabilityMeasure 0
        Integrable.of_finite = 2 / 3 := by
  rw [meanSquaredError_toMeasure_eq_expectation]
  have hq : (fun a => (qU a).toReal) = pU := by
    ext a
    simp only [qU, PMF.ofFintype_apply, pU, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    norm_num
  rw [hq]
  simp [expectation, pU, sym, Fin.sum_univ_three]; norm_num

/-- (bridge): the source finite bias of `sym²` at target `1` under the uniform
probability mass function is `-1/3`. -/
theorem uniform_bridge_bias :
    MathlibExt.Probability.Statistics.EstimationRisk.bias (fun i => sym i ^ 2)
        qU.toMeasure.toProbabilityMeasure 1
        Integrable.of_finite = -1 / 3 := by
  rw [bias_toMeasure_eq_expectation_sub]
  have hq : (fun a => (qU a).toReal) = pU := by
    ext a
    simp only [qU, PMF.ofFintype_apply, pU, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    norm_num
  rw [hq]
  have hE : expectation pU (fun i => sym i ^ 2) = 2 / 3 := by
    simp [expectation, pU, sym, Fin.sum_univ_three]; norm_num
  rw [hE]
  norm_num

/-- (bridge): the measure-theoretic variance of `sym²` under the uniform
probability mass function is `2/9`, obtained from the agreement theorem. -/
theorem uniform_bridge_variance :
    ProbabilityTheory.variance (fun i => sym i ^ 2)
        qU.toMeasure = 2 / 9 := by
  rw [variance_toMeasure_eq]
  have hq : (fun a => (qU a).toReal) = pU := by
    ext a
    simp only [qU, PMF.ofFintype_apply, pU, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    norm_num
  rw [hq]
  exact symmetric_square_variance

end MathlibExtTest.Probability.Statistics.FiniteMeanSquaredError
