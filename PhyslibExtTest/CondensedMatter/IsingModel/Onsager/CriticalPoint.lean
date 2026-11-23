/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.CriticalPoint
public import Mathlib

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Onsager.CriticalPoint`

* The Onsager integrand `ons_gInt β k₁ k₂ = cosh² 2β - sinh 2β (cos k₁ + cos k₂)` is `1` at
  `β = 0` for every momentum.
* At `k = 0` it vanishes exactly at the critical point: `ons_gInt β_c 0 0 = 0`, while at `β = 0`
  and at `β = 1` it is positive (`sinh 2 ≠ 1`).
* `ons_betaC` is positive and satisfies `sinh 2β_c = 1`; its defining formula
  `β_c = ½ log (1 + √2)` evaluates to `≈ 0.4407`, checked by the bounds `0.4 < β_c < 0.5`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Onsager.CriticalPoint

open StatMech.Onsager

-- At infinite temperature the integrand is identically `1`.
example (k₁ k₂ : ℝ) : ons_gInt 0 k₁ k₂ = 1 := by
  simp [ons_gInt]

-- The integrand vanishes at `k = 0` at the critical point.
example : ons_gInt ons_betaC 0 0 = 0 :=
  (ons_gInt_zero_eq_zero_iff ons_betaC).mpr ons_betaC_sinh

-- Away from the critical point (`β = 1`) the integrand is positive at `k = 0`.
example : 0 < ons_gInt 1 0 0 := by
  rw [ons_gInt_zero]
  have h3 : (2 : ℝ) + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
  have h4 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hs : 1 < Real.sinh (2 * 1) := by
    rw [mul_one, Real.sinh_eq]
    linarith
  nlinarith

-- Numerical bounds on `β_c = ½ log (1 + √2) ≈ 0.4407`.
example : 0.4 < ons_betaC ∧ ons_betaC < 0.5 := by
  have hs1 : (1.41 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 2 < 1.42 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold ons_betaC
  constructor
  · -- `log (2.41) > 0.8` since `exp 0.8 < 2.41`.
    have he : Real.exp 0.8 < 2.41 := by
      have := Real.exp_bound' (x := 0.8) (by norm_num) (by norm_num) (n := 6) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    have : 0.8 < Real.log (1 + Real.sqrt 2) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      linarith
    linarith
  · -- `log (2.42) < 1` since `2.42 < exp 1`.
    have he : (2.42 : ℝ) < Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have := Real.exp_one_gt_d9
      linarith
    have : Real.log (1 + Real.sqrt 2) < 1 := by
      rw [Real.log_lt_iff_lt_exp (by positivity)]
      linarith
    linarith

end PhyslibExtTest.CondensedMatter.IsingModel.Onsager.CriticalPoint
