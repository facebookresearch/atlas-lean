/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Control.RecursiveLeastSquares

@[expose] public section

open Matrix Filter Topology MathlibExt.Analysis.Control.RecursiveLeastSquares

namespace MathlibExtTest.Analysis.Control.RecursiveLeastSquares

/-- One RLS step from `θ_0 = 0`, `P_0 = 1` with regressor `1` and observation `2` gives
`θ_1 = 2 / (1 + 1) = 1` and `P_1 = 1 - 1 / 2 = 1 / 2`. -/
example : rls (fun _ => fun _ : Fin 1 => (1 : ℝ)) (fun _ => 2) 0 1 1 =
    (fun _ => 1, (1 / 2 : ℝ) • 1) := by
  simp only [rls, rlsStep]
  refine Prod.ext ?_ ?_
  · ext i; simp [dotProduct, mulVec]; norm_num
  · ext i j; fin_cases i; fin_cases j; simp [vecMulVec, dotProduct]; norm_num

/-- The matrix-inversion identity on this example: `P_1 = (P_0⁻¹ + φ φᵀ)⁻¹`. -/
example : (rls (fun _ => fun _ : Fin 1 => (1 : ℝ)) (fun _ => 2) 0 1 1).2 =
    (rlsInformation 1 (fun _ => fun _ : Fin 1 => (1 : ℝ)) 1)⁻¹ :=
  rls_snd_eq_inv PosDef.one _ _ _ 1

/-- Non-vacuity of the excitation hypothesis: with the constant regressor `φ_k = 1` in dimension
one, `∑_{k<t} φ_k φ_kᵀ = t`, whose smallest eigenvalue tends to infinity, so noise-free RLS
recovers any `θ` from any initial estimate. -/
example (θ θ₀ : Fin 1 → ℝ) :
    Tendsto (fun t => (rls (fun _ _ => 1) (fun _ => (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ θ) θ₀ 1 t).1)
      atTop (𝓝 θ) := by
  refine tendsto_rls_fst_of_noiseFree PosDef.one _ _ θ₀ θ (fun _ => rfl) fun M => ?_
  filter_upwards [eventually_ge_atTop ⌈M⌉₊] with t ht x
  have hx : 0 ≤ x 0 * x 0 := mul_self_nonneg _
  have hM : M ≤ t := (Nat.le_ceil M).trans (by exact_mod_cast ht)
  have hsum : (∑ k ∈ Finset.range t, vecMulVec (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ))) =
      (t : ℝ) • vecMulVec (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  rw [hsum]
  simp [dotProduct, mulVec, vecMulVec]
  nlinarith

/-- The logarithmic gain bound with the constant scalar regressor and `P_0 = 1`: the information
matrix is `1 + t`, so the accumulated gains are at most `log (1 + t)`. -/
example (y : ℕ → ℝ) (θ₀ : Fin 1 → ℝ) (t : ℕ) :
    ∑ k ∈ Finset.range t,
        (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ ((rls (fun _ _ => 1) y θ₀ 1 k).2 *ᵥ fun _ => 1) /
          (1 + (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ ((rls (fun _ _ => 1) y θ₀ 1 k).2 *ᵥ fun _ => 1)) ≤
      Real.log (1 + t) := by
  have h := sum_rls_gain_le_log_det PosDef.one (fun _ _ => (1 : ℝ)) y θ₀ t
  have hdet : (rlsInformation (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) t).det = 1 + t := by
    rw [rlsInformation, Matrix.det_unique, Matrix.add_apply, Matrix.sum_apply]
    simp [vecMulVec_apply, add_comm]
  rw [hdet] at h
  simpa using h

end MathlibExtTest.Analysis.Control.RecursiveLeastSquares
