/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.OLSAsymptoticNormality

namespace MathlibExtTest.LinearModelOLSAsymptoticNormality

open Matrix MeasureTheory ProbabilityTheory Filter Finset
open MathlibExt.Probability.Statistics.LinearModel

-- Moment hypotheses are assumed, not discharged: this example instantiates
-- the theorem at `k = Fin 1`.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (Fin 1 → ℝ)} {U : ℕ → Ω → ℝ} (β : Fin 1 → ℝ)
    (hindep : iIndepFun (fun (i : ℕ) (ω : Ω) => (X i ω, U i ω)) μ)
    (hident : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω))
      (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (hintGram : ∀ a b, Integrable (fun ω => X 0 ω a * X 0 ω b) μ)
    (hintScore : Integrable (fun ω => (U 0 ω) • X 0 ω) μ)
    (hmeanScore : ∫ ω, (U 0 ω) • X 0 ω ∂μ = 0)
    (hscore2 : MemLp (fun ω => (U 0 ω) • X 0 ω) 2 μ)
    (hQ : IsUnit (popGram (X 0) μ)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => WithLp.toLp 2 ((√(n : ℝ)) •
        (olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - β)))
      atTop (id : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (fun _ => μ)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
        ((popGram (X 0) μ)⁻¹ * (popScoreCov (X 0) (U 0) μ) * (popGram (X 0) μ)⁻¹)) := by
  exact tendstoInDistribution_sqrt_mul_olsSeqEstimator_sub β
    hindep hident hintGram hintScore hmeanScore hscore2 hQ

/-- `Q = 4` for constant regressor `x₀ = ![2]`. -/
theorem popGram_const_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] :
    popGram (fun _ : Ω => ![2]) μ = !![4] := by
  ext a b
  fin_cases a
  fin_cases b
  simp [popGram]
  norm_num

/-- `Ω = 36` for `x₀ = ![2]`, `u₀ = 3`. -/
theorem popScoreCov_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] :
    popScoreCov (fun _ : Ω => ![2]) (fun _ : Ω => 3) μ =
      !![36] := by
  ext a b
  fin_cases a
  fin_cases b
  simp [popScoreCov, hc0PopMeat]
  norm_num

/-- For `k = Fin 1` the sandwich is `Ω / Q²`. -/
theorem sandwich_fin_one :
    ((!![4] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * !![36] *
      (!![4] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹) =
      !![36 / 4 ^ 2] := by
  have hMul : (!![4] : Matrix (Fin 1) (Fin 1) ℝ) * !![(4 : ℝ)⁻¹] = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply]
  have hInv4 : (!![4] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![(4 : ℝ)⁻¹] :=
    Matrix.inv_eq_right_inv hMul
  rw [hInv4]
  ext a b
  fin_cases a
  fin_cases b
  simp [Matrix.mul_apply]
  norm_num

end MathlibExtTest.LinearModelOLSAsymptoticNormality
