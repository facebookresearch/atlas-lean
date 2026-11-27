/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TriangularRepresentationWindow

/-!
# Tests for the window congruence for triangular representation counts
-/

open MetaMathlibExt

-- The smallest odd prime, with both bounds attained.
example : (3 : ℤ) ∣ ∑ i ∈ Finset.range 3, sumOfTriangularRepCount (3 - i) 1 := by
  exact sum_sumOfTriangularRepCount_window (n := 1) (p := 3) (s := 3)
    (hn := by decide) (hp := by decide) (hp2 := by decide) (hpn := by decide) (hs := by decide)

-- The maximal allowed degree for p = 5, with the window shifted past p.
example : (5 : ℤ) ∣ ∑ i ∈ Finset.range 5, sumOfTriangularRepCount (7 - i) 3 := by
  exact sum_sumOfTriangularRepCount_window (n := 3) (p := 5) (s := 7)
    (hn := by decide) (hp := by decide) (hp2 := by decide) (hpn := by decide) (hs := by decide)

open PowerSeries in
private theorem triangularCount_coeff_one (k : ℕ) :
    sumOfTriangularRepCount k 1 = (k : ℤ) ∧
      sumOfTriangularRepCount (-(k : ℤ)) 1 = -(k : ℤ) := by
  let u := isUnit_triangularThetaSeries.unit
  let g : PowerSeries ℤ := ↑u⁻¹
  have h0 : constantCoeff triangularThetaSeries = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_triangularThetaSeries_small.1]
  have h1 := coeff_triangularThetaSeries_small.2.1
  have hmul : triangularThetaSeries * g = 1 := by
    rw [← isUnit_triangularThetaSeries.unit_spec]
    change (↑(u * u⁻¹) : PowerSeries ℤ) = 1
    rw [mul_inv_cancel, Units.val_one]
  have hg0 := congrArg constantCoeff hmul
  rw [map_mul, h0, one_mul, map_one] at hg0
  have hg1 := congrArg (coeff 1) hmul
  rw [coeff_one_mul, h1, hg0, h0, one_mul, mul_one, coeff_one] at hg1
  simp only [one_ne_zero, ite_false] at hg1
  have hg1' : coeff 1 g = -1 := by omega
  constructor
  · change coeff 1 (↑(u ^ (k : ℤ)) : PowerSeries ℤ) = (k : ℤ)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, isUnit_triangularThetaSeries.unit_spec,
      coeff_one_pow, h1, h0]
    simp
  · change coeff 1 (↑(u ^ (-(k : ℤ))) : PowerSeries ℤ) = -(k : ℤ)
    rw [zpow_neg, ← inv_zpow, zpow_natCast, Units.val_pow_eq_pow_val, coeff_one_pow, hg1', hg0]
    simp

-- At p = n + 1 = 2 the shift r = -2 crosses zero: t₂(1) = 2 and t₋₂(1) = -2.
example : (2 : ℤ) ∣ sumOfTriangularRepCount (-2) 1 := by
  have h₂ : sumOfTriangularRepCount 2 1 = 2 := (triangularCount_coeff_one 2).1
  have h : (2 : ℤ) ∣ sumOfTriangularRepCount 2 1 := by rw [h₂]
  simpa using sumOfTriangularRepCount_add_mul_prime (n := 1) (k := 2) (p := 2)
    (hn := by decide) (hk := by decide) (hp := by decide) (hpn := by decide) (h := h) (r := -2)

-- At the smallest admissible prime and degree, the tail of the window for s = 2 sums to 1.
example : sumOfTriangularRepCount 2 1 ≠ 0 := by
  apply sumOfTriangularRepCount_ne_zero_of_window (n := 1) (p := 3)
    (by decide) (by decide) (by decide) (by decide) 2
  rw [show Finset.Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) by decide, Finset.sum_pair (by decide)]
  change ¬ (3 : ℤ) ∣ sumOfTriangularRepCount 1 1 + sumOfTriangularRepCount 0 1
  have h₁ : sumOfTriangularRepCount 1 1 = 1 := (triangularCount_coeff_one 1).1
  have h₀ : sumOfTriangularRepCount 0 1 = 0 := (triangularCount_coeff_one 0).1
  rw [h₁, h₀]
  decide

-- The same residue class has an entirely negative window: the tail sums to -5.
example : sumOfTriangularRepCount (-1) 1 ≠ 0 := by
  apply sumOfTriangularRepCount_ne_zero_of_window (n := 1) (p := 3)
    (by decide) (by decide) (by decide) (by decide) (-1)
  rw [show Finset.Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) by decide, Finset.sum_pair (by decide)]
  change ¬ (3 : ℤ) ∣ sumOfTriangularRepCount (-2) 1 + sumOfTriangularRepCount (-3) 1
  have h₂ : sumOfTriangularRepCount (-2) 1 = -2 := (triangularCount_coeff_one 2).2
  have h₃ : sumOfTriangularRepCount (-3) 1 = -3 := (triangularCount_coeff_one 3).2
  rw [h₂, h₃]
  decide
