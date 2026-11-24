/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Control.RecursiveLeastSquaresEnergy

open Matrix MeasureTheory Filter MathlibExt.Analysis.Control.RecursiveLeastSquares

/-- Zero regressors make both the logarithm and prediction loss zero, but the arbitrary initial
error remains. The energy estimate then gives a bound by its additive constant alone. -/
example {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (θ θ₀ : Fin 1 → ℝ) :
    ∀ᵐ _ω ∂μ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ _t : ℕ in atTop, (θ₀ - θ) ⬝ᵥ (θ₀ - θ) ≤ C₀ := by
  have houter : vecMulVec (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) = 0 := by
    ext i j
    simp [vecMulVec_apply]
  have hstate (t : ℕ) : rls (fun _ => (0 : Fin 1 → ℝ)) (fun _ => 0) θ₀ 1 t = (θ₀, 1) := by
    induction t with
    | zero => rfl
    | succ t ih => simp [rls, rlsStep, ih, houter]
  have h := rls_energy_add_half_sum_le_log μ ℱ θ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ => measurable_const) (fun _ => measurable_const) (β := 3) (by norm_num)
    (fun _ => by simp)
    (fun k => by
      change μ[(0 : Ω → ℝ) | ℱ k] =ᵐ[μ] 0
      simp)
    ⟨0, fun k => by
      simp only [abs_zero, Real.zero_rpow (by norm_num : (3 : ℝ) ≠ 0)]
      change μ[(0 : Ω → ℝ) | ℱ k] ≤ᵐ[μ] 0
      rw [condExp_zero]⟩
    (fun _ _ => by simp) θ₀ PosDef.one
  filter_upwards [h] with ω hω
  obtain ⟨C₀, C₁, h₀, _, hC⟩ := hω
  refine ⟨C₀, h₀, ?_⟩
  filter_upwards [hC] with t ht
  simpa [hstate, rlsInformation, houter] using ht
