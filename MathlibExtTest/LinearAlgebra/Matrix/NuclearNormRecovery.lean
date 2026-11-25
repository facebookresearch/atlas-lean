/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.NuclearNormRecovery

open Matrix MathlibExt.LinearAlgebra.Matrix.LowRankRecovery
open MathlibExt.LinearAlgebra.NuclearNormRecoveryWanted

-- A rectangular problem at a distortion close to the threshold. The competitor can have any rank.
example {p : ℕ} {𝒜 : Matrix (Fin 100) (Fin 101) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p)}
    (hRIP : IsRestrictedIsometry 𝒜 5 (99 / 1000))
    {X₀ X : Matrix (Fin 100) (Fin 101) ℝ} (hX₀ : X₀.rank ≤ 1)
    (hX : 𝒜 X = 𝒜 X₀) (hMin : nuclearNorm X ≤ nuclearNorm X₀) : X = X₀ := by
  by_contra hne
  exact (not_lt_of_ge hMin) (nuclearNorm_lt_of_isRestrictedIsometry_five_mul
    (hr := le_rfl) (hRIP := hRIP) (hδ := by norm_num) (hX₀ := hX₀) (X := X)
    (hX := hX) (hne := hne))

-- The reference matrix may have rank zero even when the isometry order is positive.
example {p : ℕ} {𝒜 : Matrix (Fin 100) (Fin 101) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p)}
    (hRIP : IsRestrictedIsometry 𝒜 5 (1 / 20)) (X : Matrix (Fin 100) (Fin 101) ℝ)
    (hX : 𝒜 X = 0) (hne : X ≠ 0) : 0 < nuclearNorm X := by
  have hZero : nuclearNorm (0 : Matrix (Fin 100) (Fin 101) ℝ) = 0 := by simp [nuclearNorm]
  rw [← hZero]
  exact nuclearNorm_lt_of_isRestrictedIsometry_five_mul le_rfl hRIP
    (by norm_num) (by simp) X (by simpa using hX) hne
