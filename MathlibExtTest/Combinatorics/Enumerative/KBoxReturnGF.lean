/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Enumerative.KBoxReturnGF

/-! Tests for the lowest coefficients of the returns generating function. -/

open MetaMathlibExt PowerSeries

namespace MathlibExtTest.KBoxReturnGF

local notation "𝒕" => PowerSeries.C (Polynomial.X : Polynomial ℤ)
local notation "𝒙" => (PowerSeries.X : PowerSeries (Polynomial ℤ))

-- The empty path is excluded from the returns series.
example (k : ℕ) : coeff 0 (kBoxReturnGF k) = 0 := by
  simp [kBoxReturnGF]

private theorem coeff_one_returns : coeff 1 (kBoxReturnGF 1) = Polynomial.X := by
  simp [kBoxReturnGF, kBoxPaths_one_one, show skewReturns
    [SkewDyckStep.U, SkewDyckStep.U, SkewDyckStep.D, SkewDyckStep.L] = 1 by decide]

-- At size two there is one path with one return and one path with two.
example : coeff 2 (kBoxReturnGF 1) = Polynomial.X + Polynomial.X ^ 2 := by
  let G := PowerSeries.map Polynomial.C (augmentedKDyckGF 2)
  let F := kBoxReturnGF 1
  have hg₀ : coeff 0 G = 1 := by
    have hc : (augmentedKDyckPaths 2 0).card = 1 := by decide
    simp [G, PowerSeries.coeff_map, augmentedKDyckGF, hc]
  have hg₁ : coeff 1 G = 1 := by
    have hc : (augmentedKDyckPaths 2 1).card = 1 := by decide
    simp [G, PowerSeries.coeff_map, augmentedKDyckGF, hc]
  have h : (1 - 𝒕 * 𝒙 * G ^ 2) * F = 𝒕 * 𝒙 * G := by
    simpa only [pow_one] using kBoxReturnGF_eq (k := 1) (hk := le_rfl)
  rw [sub_mul, one_mul, sub_eq_iff_eq_add] at h
  have h₂ := congrArg (coeff 2) h
  have hconst : constantCoeff G = 1 := by
    rwa [← coeff_zero_eq_constantCoeff]
  have hF₀ : coeff 0 F = 0 := by simp [F, kBoxReturnGF]
  have hF₁ : coeff 1 F = Polynomial.X := coeff_one_returns
  have ha : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  simp only [map_add, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] at h₂
  rw [PowerSeries.coeff_mul, ha] at h₂
  change coeff 2 F = _
  simpa [hconst, hg₁, hF₀, hF₁, pow_two] using h₂

end MathlibExtTest.KBoxReturnGF
