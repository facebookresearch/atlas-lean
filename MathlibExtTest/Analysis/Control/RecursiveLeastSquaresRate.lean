/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Control.RecursiveLeastSquaresRate

open Matrix MeasureTheory Filter MathlibExt.Analysis.Control.RecursiveLeastSquares

namespace MathlibExtTest.Analysis.Control.RecursiveLeastSquaresRate

private noncomputable def energy : ℕ → ℝ
  | 0 => 1
  | k + 1 => energy k + (energy k) ^ 2

private noncomputable def regressor (k : ℕ) : Fin 1 → ℝ := fun _ => energy k

private theorem le_energy (k : ℕ) : (k : ℝ) + 1 ≤ energy k := by
  induction k with
  | zero => simp [energy]
  | succ k ih =>
    have h₁ : 1 ≤ energy k := (le_add_of_nonneg_left (Nat.cast_nonneg k)).trans ih
    have h₂ : 1 ≤ (energy k) ^ 2 := by nlinarith
    simp only [energy, Nat.cast_succ]
    linarith

private theorem energy_eq (t : ℕ) :
    energy t = 1 + ∑ k ∈ Finset.range t, regressor k ⬝ᵥ regressor k := by
  induction t with
  | zero => simp [energy]
  | succ t ih =>
    rw [energy, Finset.sum_range_succ, ← add_assoc, ← ih]
    simp [regressor, dotProduct, pow_two]

private theorem information_eq (t : ℕ) :
    rlsInformation (1 : Matrix (Fin 1) (Fin 1) ℝ) regressor t = Matrix.diagonal (regressor t) := by
  ext i j
  fin_cases i
  fin_cases j
  simpa [rlsInformation, Matrix.sum_apply, vecMulVec_apply, dotProduct, regressor] using
    (energy_eq t).symm

/-- The scalar fixture deliberately has unbounded leverage: its leverage at time `t` is the
information value `energy t`, which grows without bound. -/
example (θ₀ : Fin 1 → ℝ) (t : ℕ) : (t : ℝ) + 1 ≤
    regressor t ⬝ᵥ ((rls regressor (fun _ => 0) θ₀ 1 t).2 *ᵥ regressor t) := by
  rw [rls_snd_eq_inv PosDef.one, information_eq, Matrix.inv_subsingleton]
  have hpos : 0 < energy t := lt_of_lt_of_le (by positivity) (le_energy t)
  simpa only [regressor, dotProduct, mulVec, Fin.sum_univ_one, diagonal_apply_eq,
    Ring.inverse_eq_inv, inv_mul_cancel₀ hpos.ne', mul_one] using le_energy t

/-- The parameter-error rate applies to the same unbounded-leverage fixture, with zero noise and
an arbitrary initial estimate. The scalar information value is the exact eigenvalue bound. -/
example {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (θ₀ : Fin 1 → ℝ) :
    ∀ᵐ _ω ∂μ, ∃ C : ℝ, ∀ᶠ t in atTop,
      energy (t + 1) * ((rls regressor (fun _ => 0) θ₀ 1 (t + 1)).1 ⬝ᵥ
        (rls regressor (fun _ => 0) θ₀ 1 (t + 1)).1) ≤ C * Real.log (energy (t + 1)) := by
  have henergy : Tendsto (fun t => ∑ k ∈ Finset.range (t + 1), regressor k ⬝ᵥ regressor k)
      atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop b] with t ht
    have h := le_energy (t + 1)
    rw [energy_eq, Nat.cast_succ] at h
    linarith
  have h := rls_error_sq_le_log_div_lambdaMin μ ℱ (0 : Fin 1 → ℝ)
    (fun k _ => regressor k) (fun _ _ => 0) (fun _ _ => 0)
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
  obtain ⟨C, hC⟩ := hω henergy
  refine ⟨C, ?_⟩
  filter_upwards [hC] with t ht
  have hscalar := ht (energy (t + 1)) fun x => by
    rw [information_eq]
    simp only [dotProduct, mulVec, Fin.sum_univ_one, diagonal_apply_eq, regressor]
    exact (mul_left_comm (energy (t + 1)) (x 0) (x 0)).le
  simpa only [energy_eq, sub_zero] using hscalar

end MathlibExtTest.Analysis.Control.RecursiveLeastSquaresRate
