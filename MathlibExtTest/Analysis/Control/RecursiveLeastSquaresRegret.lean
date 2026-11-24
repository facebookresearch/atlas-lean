/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Control.RecursiveLeastSquaresRegret

open Matrix MeasureTheory Filter MathlibExt.Analysis.Control.RecursiveLeastSquares

/-- Constant scalar regressors and zero noise satisfy the hypotheses, with divergent energy and
leverage `1 / (1 + t)`. In particular the estimate need not start at the true parameter. -/
example {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (θ θ₀ : Fin 1 → ℝ) :
    ∀ᵐ _ω ∂μ, ∃ C : ℝ, ∀ᶠ t in atTop,
      ∑ k ∈ Finset.range (t + 1),
          ((fun _ : Fin 1 => 1) ⬝ᵥ ((rls (fun _ _ => 1) (fun _ => θ 0) θ₀ 1 k).1 - θ)) ^ 2 ≤
        C * Real.log (1 + (t + 1 : ℕ)) := by
  let φ : ℕ → Ω → Fin 1 → ℝ := fun _ _ _ => 1
  have hφ : Adapted ℱ φ := fun _ => measurable_const
  have hw : Adapted ℱ (0 : ℕ → Ω → ℝ) := fun _ => measurable_const
  have hbdd : ∀ᵐ ω ∂μ, ∃ B : ℝ, ∀ t,
      φ t ω ⬝ᵥ ((rls (φ · ω) (fun _ => θ 0) θ₀ 1 t).2 *ᵥ φ t ω) ≤ B :=
    ae_of_all μ fun ω => ⟨1, fun t => by
      rw [rls_snd_eq_inv PosDef.one]
      let R := rlsInformation (1 : Matrix (Fin 1) (Fin 1) ℝ) (φ · ω) t
      have hR : R 0 0 = 1 + t := by
        change (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ 0 0 +
          (∑ k ∈ Finset.range t, vecMulVec (φ k ω) (φ k ω)) 0 0 = 1 + t
        rw [inv_one, Matrix.one_apply_eq, Matrix.sum_apply]
        simp [φ, vecMulVec_apply]
      have hpos := posDef_rlsInformation PosDef.one (φ · ω) t
      have hp := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℝ => A 0 0)
        (Matrix.mul_nonsing_inv R ((isUnit_iff_isUnit_det _).mp hpos.isUnit))
      change (R * R⁻¹) 0 0 = 1 at hp
      rw [Matrix.mul_apply, Fin.sum_univ_one, hR] at hp
      have hinv : R⁻¹ 0 0 = (1 + (t : ℝ))⁻¹ := by
        rw [show (1 + (t : ℝ))⁻¹ = 1 / (1 + (t : ℝ)) from (one_div _).symm,
          eq_div_iff (by positivity)]
        rwa [mul_comm]
      change φ t ω ⬝ᵥ (R⁻¹ *ᵥ φ t ω) ≤ 1
      simp only [φ, dotProduct, mulVec, Fin.sum_univ_one, one_mul, mul_one, hinv]
      exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (Nat.cast_nonneg t))⟩
  have h := rls_regret_sum_le_log μ ℱ θ φ 0 (fun _ _ => θ 0) hφ hw
    (β := 3) (by norm_num) (fun _ => by simp) (fun _ => by simp)
    ⟨0, fun _ => by
      simp only [Pi.zero_apply, abs_zero, Real.zero_rpow (by norm_num : (3 : ℝ) ≠ 0)]
      rw [show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, condExp_zero]⟩
    (fun _ _ => by simp [φ, dotProduct]) θ₀ PosDef.one hbdd
  filter_upwards [h] with ω hω
  have hsum (t : ℕ) : (∑ k ∈ Finset.range (t + 1), φ k ω ⬝ᵥ φ k ω) = (t + 1 : ℕ) := by
    simp [φ, dotProduct]
  have henergy : Tendsto (fun t => ∑ k ∈ Finset.range (t + 1), φ k ω ⬝ᵥ φ k ω) atTop atTop := by
    simp_rw [hsum]
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  simpa only [hsum, φ] using hω henergy
