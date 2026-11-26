/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentMobiusOrderIdentities

/-! # Tests for `MathlibExt.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentMobiusOrderIdentities` -/

namespace MathlibExtTest.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentMobiusOrderIdentities

open MetaMathlibExt

variable {K : Type*} [Field K]

-- With `A = D = 1`, `B = 0`, `C = 1` we have `S1 = 1`, `R1 = 0` for `P = 0`, `Q = 1`.
example [Fintype K] (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv 1 * α ^ Fintype.card K + polyToLaurentInv 0) /
      (polyToLaurentInv 1 * α ^ Fintype.card K + polyToLaurentInv 1))
    (hb0 : laurentPartialQuotient α 0 = 0)
    (hclose : (α - polyToLaurentInv 1 / polyToLaurentInv 1).order <
      (α - polyToLaurentInv 0 / polyToLaurentInv 1).order) :
    (polyToLaurentInv 1 * α ^ Fintype.card K - polyToLaurentInv 0).order =
      - (laurentPartialQuotient α 1).order := by
  have hΔ : (1 : Polynomial K) * 1 - 0 * 1 ≠ 0 := by simp
  have hC : (1 : Polynomial K) ≠ 0 := one_ne_zero
  have hPQ : IsCoprime (0 : Polynomial K) 1 := ⟨0, 1, by simp⟩
  have hQ : (1 : Polynomial K) ≠ 0 := one_ne_zero
  have hQ1 : laurentConvDen α 1 = 1 := by simp [laurentConvDen]
  have hP1 : laurentConvNum α 1 = laurentPartialQuotient α 0 := by simp [laurentConvNum]
  have hconv : polyToLaurentInv (0 : Polynomial K) * laurentConvDen α (0 + 1) =
      polyToLaurentInv (1 : Polynomial K) * laurentConvNum α (0 + 1) := by
    simp [hQ1, hP1, hb0, polyToLaurentInv]
  have h := (laurentMobius_order_identities (1 : Polynomial K) 0 1 1 hΔ hC α hα hfix 0 0 1
    hPQ hQ hconv).1 hclose
  have hS1 : -(1 : Polynomial K) * 0 + 1 * 1 = 1 := by simp
  have hR1 : (1 : Polynomial K) * 0 - 0 * 1 = 0 := by simp
  have hD : (1 : Polynomial K) * 1 - 0 * 1 = 1 := by simp
  simp only [hS1, hR1, hD] at h
  simpa using h

-- The second identity with the same values: `S2 = 1`, `R2 = 0`.
example [Fintype K] (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv 1 * α ^ Fintype.card K + polyToLaurentInv 0) /
      (polyToLaurentInv 1 * α ^ Fintype.card K + polyToLaurentInv 1))
    (hb0 : laurentPartialQuotient α 0 = 0)
    (hclose : (α ^ Fintype.card K + polyToLaurentInv 1 / polyToLaurentInv 1).order <
      (Fintype.card K : ℤ) * (α - polyToLaurentInv 0 / polyToLaurentInv 1).order) :
    (polyToLaurentInv 1 * α - polyToLaurentInv 0).order =
      - (Fintype.card K : ℤ) * (laurentPartialQuotient α 1).order := by
  have hΔ : (1 : Polynomial K) * 1 - 0 * 1 ≠ 0 := by simp
  have hC : (1 : Polynomial K) ≠ 0 := one_ne_zero
  have hPQ : IsCoprime (0 : Polynomial K) 1 := ⟨0, 1, by simp⟩
  have hQ : (1 : Polynomial K) ≠ 0 := one_ne_zero
  have hQ1 : laurentConvDen α 1 = 1 := by simp [laurentConvDen]
  have hP1 : laurentConvNum α 1 = laurentPartialQuotient α 0 := by simp [laurentConvNum]
  have hconv : polyToLaurentInv (0 : Polynomial K) * laurentConvDen α (0 + 1) =
      polyToLaurentInv (1 : Polynomial K) * laurentConvNum α (0 + 1) := by
    simp [hQ1, hP1, hb0, polyToLaurentInv]
  have h := (laurentMobius_order_identities (1 : Polynomial K) 0 1 1 hΔ hC α hα hfix 0 0 1
    hPQ hQ hconv).2 hclose
  have hS2 : (1 : Polynomial K) * (0 : Polynomial K) ^ Fintype.card K +
      1 * (1 : Polynomial K) ^ Fintype.card K = 1 := by simp
  have hR2 : (1 : Polynomial K) * (0 : Polynomial K) ^ Fintype.card K +
      0 * (1 : Polynomial K) ^ Fintype.card K = 0 := by simp
  have hD : (1 : Polynomial K) * 1 - 0 * 1 = 1 := by simp
  simp only [hS2, hR2, hD] at h
  simpa using h

end MathlibExtTest.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentMobiusOrderIdentities
