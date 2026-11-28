/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.SelectionScan.LatentFactorMixedModel
import MathlibExt.LinearAlgebra.Matrix.RealSVD

/-! Tests for the ridge estimates of the latent factor mixed model: the hypotheses hold for every
matrix of primary variables, the shrinkage matrix on a concrete example, and the rank-zero case,
where the estimate is ridge regression and the gap condition is void. -/

open Matrix Matrix.EckartYoungFrobenius
open Domains.Biology.PopulationGenetics.LatentFactorMixedModel

namespace DomainsTest.Biology.PopulationGenetics.SelectionScan.LatentFactorMixedModel

/-- Non-vacuity: every matrix of primary variables with `d < n` has a singular value
decomposition, so the ridge loss always has a minimizer over `rank W ≤ K`. -/
example {n p d : ℕ} (Y : Matrix (Fin n) (Fin p) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (hd : d < n) (K : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ (W : Matrix (Fin n) (Fin p) ℝ) (B : Matrix (Fin p) (Fin d) ℝ), W.rank ≤ K ∧
      ∀ W' B', W'.rank ≤ K → ridgeLoss Y X lam W B ≤ ridgeLoss Y X lam W' B' := by
  obtain ⟨Q, R, σ, -, -, hQ, hR, hX⟩ :=
    MathlibExt.LinearAlgebra.Matrix.RealSVDWanted.real_singular_value_decomposition n d X
  obtain ⟨hrank, hmin, -⟩ := ridge_estimates Y X hd K hlam hQ hR hX
  exact ⟨_, _, hrank, hmin⟩

/-- The shrinkage matrix for `λ = 1`, one singular value `σ₁ = 1` and `n = 2` is
`diag(√(1/2), 1)`. -/
example : shrinkage 2 1 ![(1 : ℝ)] = diagonal ![√(1 / 2), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [shrinkage, diagonal_apply]

/-- The shrinkage entries lie in `(0, 1]`. -/
example {n d : ℕ} {lam : ℝ} (hlam : 0 < lam) (σ : Fin d → ℝ) (i : Fin n) :
    0 < shrinkage n lam σ i i ∧ shrinkage n lam σ i i ≤ 1 := by
  rw [shrinkage, diagonal_apply_eq]
  by_cases hi : i.val < d
  · simp only [hi, dite_true]
    have hpos : 0 < lam + σ ⟨i.val, hi⟩ ^ 2 := by positivity
    refine ⟨Real.sqrt_pos.mpr (div_pos hlam hpos), Real.sqrt_le_one.mpr ?_⟩
    rw [div_le_one hpos]
    nlinarith [sq_nonneg (σ ⟨i.val, hi⟩)]
  · simp [hi]

/-- At rank `K = 0` the latent estimate vanishes. -/
theorem latentEstimate_zero {n p d : ℕ} (Y : Matrix (Fin n) (Fin p) ℝ) (lam : ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (σ : Fin d → ℝ) : latentEstimate Y lam Q σ 0 = 0 := by
  simp [latentEstimate, truncSVD]

/-- At rank `K = 0`, ridge regression `B̂ᵀ = (XᵀX + λ I)⁻¹ Xᵀ Y` is the unique minimizer of
`‖Y - X Bᵀ‖² + λ ‖B‖²`, with no condition on singular values. -/
example {n p d : ℕ} (Y : Matrix (Fin n) (Fin p) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (hd : d < n) {lam : ℝ} (hlam : 0 < lam)
    {Q : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin d) (Fin d) ℝ} {σ : Fin d → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hR : R ∈ orthogonalGroup (Fin d) ℝ)
    (hX : X = Q * of (fun i j => if i.val = j.val then σ j else 0) * Rᵀ)
    (B : Matrix (Fin p) (Fin d) ℝ) :
    ridgeLoss Y X lam 0 (effectEstimate Y X lam 0) ≤ ridgeLoss Y X lam 0 B ∧
      (ridgeLoss Y X lam 0 B ≤ ridgeLoss Y X lam 0 (effectEstimate Y X lam 0) →
        B = effectEstimate Y X lam 0) := by
  obtain ⟨-, hmin, huniq⟩ := ridge_estimates Y X hd 0 hlam hQ hR hX
  rw [latentEstimate_zero] at hmin huniq
  refine ⟨hmin 0 B (by simp), fun hle => ?_⟩
  exact (huniq (fun i hi => absurd hi (Nat.not_lt_zero i)) 0 B (by simp) hle).2

/-- The ridge loss is nonnegative for a nonnegative ridge parameter. -/
example {n p d : ℕ} (Y : Matrix (Fin n) (Fin p) ℝ) (X : Matrix (Fin n) (Fin d) ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (W : Matrix (Fin n) (Fin p) ℝ) (B : Matrix (Fin p) (Fin d) ℝ) :
    0 ≤ ridgeLoss Y X lam W B := by
  rw [ridgeLoss]
  positivity

end DomainsTest.Biology.PopulationGenetics.SelectionScan.LatentFactorMixedModel
