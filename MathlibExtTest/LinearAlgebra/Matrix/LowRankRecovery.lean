/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.LowRankRecovery
import MathlibExt.LinearAlgebra.Matrix.RankAddGeneral
import Mathlib.Tactic.FinCases

open Matrix
open scoped Matrix.Norms.Frobenius

namespace MathlibExt.LinearAlgebra.Matrix.LowRankRecovery

-- The nuclear norm of the zero matrix is `0`.
example : nuclearNorm (0 : Matrix (Fin 2) (Fin 3) ℝ) = 0 := by
  simp [nuclearNorm, LinearMap.singularValues_zero]

-- Subadditivity of the rank, on two matrices of rank at most one.
example (A B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.rank ≤ 1) (hB : B.rank ≤ 1) :
    (A - B).rank ≤ 2 :=
  (Matrix.rank_sub_le A B).trans (by omega)

-- Theorem 3.2 with `r = 1`: under `δ₂ < 1`, two rank-one matrices with the same measurements
-- coincide.
example {p : ℕ} (𝒜 : Matrix (Fin 3) (Fin 4) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (hRIP : IsRestrictedIsometry 𝒜 (2 * 1) (1 / 2)) (X X₀ : Matrix (Fin 3) (Fin 4) ℝ)
    (hX : X.rank ≤ 1) (hX₀ : X₀.rank ≤ 1) (h : 𝒜 X = 𝒜 X₀) : X = X₀ :=
  eq_of_isRestrictedIsometry_two_mul hRIP (by norm_num) hX hX₀ h

/-- Reading the single entry of a `1 × 1` matrix as a vector of `ℝ¹`. -/
private noncomputable def entryMap : Matrix (Fin 1) (Fin 1) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun X := WithLp.toLp 2 fun _ => X 0 0
  map_add' X Y := by ext; simp
  map_smul' c X := by ext; simp

-- The restricted isometry property is satisfiable: the entry map is an isometry (`δ = 0`).
example (r : ℕ) : IsRestrictedIsometry entryMap r 0 := by
  intro X _
  have h : ‖entryMap X‖ = ‖X‖ := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    simp [entryMap, EuclideanSpace.norm_eq]
  simp [h]

-- The structural hypotheses of the matrix completion theorem (Candès–Recht, Theorem 1.3, in
-- `WantedExt.LinearAlgebra.MatrixCompletionWanted`) are jointly satisfiable with
-- `n₁ = n₂ = r = 1`, `U = V = 1`, `σ = 1`, `μ₀ = μ₁ = 1`: orthonormality, A0 and A1 are checked
-- below; with `V = U` the conditions on `V` are the same ones, and `σ = 1 > 0`, `μ₁ = 1 ≥ 1` are
-- immediate.
example : (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 = 1 ∧
    (∀ i, ((1 : ℕ) : ℝ) / (1 : ℕ) * ∑ k, (1 : Matrix (Fin 1) (Fin 1) ℝ) i k ^ 2 ≤ 1) ∧
    ∀ i j, |((1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) i j| ≤
      1 * √(((1 : ℕ) : ℝ) / ((1 : ℕ) * (1 : ℕ))) := by
  refine ⟨by simp, fun i => ?_, fun i j => ?_⟩
  · fin_cases i; simp [Matrix.one_apply]
  · fin_cases i; fin_cases j; simp

end MathlibExt.LinearAlgebra.Matrix.LowRankRecovery
