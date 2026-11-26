/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquaresTriangularRepresentationsRepCountNeZeroOfWindow

/-!
# Tests for the representability criterion from a window of counts
-/

namespace MathlibExtTest.NumberTheory.SquaresTriangularRepresentationsRepCountNeZeroOfWindow

open MetaMathlibExt

-- At n = 1, p = 3 and s = 2 the square window sums to r₁(1) + r₀(1) = 2, forcing r₂(1) ≠ 0.
example : sumOfSquaresRepCount 2 1 ≠ 0 := by
  have hr1 : sumOfSquaresRepCount 1 1 = 2 := by
    simp only [sumOfSquaresRepCount_one, coeff_squareThetaSeries_small.2.1]
  have hr0 : sumOfSquaresRepCount 0 1 = 0 := by
    simp only [sumOfSquaresRepCount, zpow_zero, Units.val_one, PowerSeries.coeff_one,
      one_ne_zero, ite_false]
  have hIcc : Finset.Icc (1 : ℕ) ((3 : ℕ) - 1) = ({1, 2} : Finset ℕ) := by decide
  have e1 : (2 : ℤ) - ((1 : ℕ) : ℤ) = 1 := by norm_num
  have e2 : (2 : ℤ) - ((2 : ℕ) : ℤ) = 0 := by norm_num
  have hsum : ∑ i ∈ Finset.Icc (1 : ℕ) ((3 : ℕ) - 1), sumOfSquaresRepCount (2 - i) 1 = 2 := by
    rw [hIcc, Finset.sum_insert (by decide), Finset.sum_singleton, e1, e2, hr1, hr0, add_zero]
  have hnondiv :
      ¬ (3 : ℤ) ∣ ∑ i ∈ Finset.Icc (1 : ℕ) ((3 : ℕ) - 1), sumOfSquaresRepCount (2 - i) 1 := by
    rw [hsum]
    decide
  exact (repCount_ne_zero_of_window (n := 1) (p := 3) (s := 2)
    (hn := by decide) (hp := by decide) (hp2 := by decide) (hpn := by decide)).1 hnondiv

-- At n = 1, p = 3 and s = 2 the triangular window sums to t₁(1) + t₀(1) = 1, forcing t₂(1) ≠ 0.
example : sumOfTriangularRepCount 2 1 ≠ 0 := by
  have ht1 : sumOfTriangularRepCount 1 1 = 1 := by
    simp only [sumOfTriangularRepCount, zpow_one, IsUnit.unit_spec,
      coeff_triangularThetaSeries_small.2.1]
  have ht0 : sumOfTriangularRepCount 0 1 = 0 := by
    simp only [sumOfTriangularRepCount, zpow_zero, Units.val_one, PowerSeries.coeff_one,
      one_ne_zero, ite_false]
  have hIcc : Finset.Icc (1 : ℕ) ((3 : ℕ) - 1) = ({1, 2} : Finset ℕ) := by decide
  have e1 : (2 : ℤ) - ((1 : ℕ) : ℤ) = 1 := by norm_num
  have e2 : (2 : ℤ) - ((2 : ℕ) : ℤ) = 0 := by norm_num
  have hsum : ∑ i ∈ Finset.Icc (1 : ℕ) ((3 : ℕ) - 1), sumOfTriangularRepCount (2 - i) 1 = 1 := by
    rw [hIcc, Finset.sum_insert (by decide), Finset.sum_singleton, e1, e2, ht1, ht0, add_zero]
  have hnondiv :
      ¬ (3 : ℤ) ∣ ∑ i ∈ Finset.Icc (1 : ℕ) ((3 : ℕ) - 1), sumOfTriangularRepCount (2 - i) 1 := by
    rw [hsum]
    decide
  exact (repCount_ne_zero_of_window (n := 1) (p := 3) (s := 2)
    (hn := by decide) (hp := by decide) (hp2 := by decide) (hpn := by decide)).2 hnondiv

-- Contrapositive: a vanishing square count forces the window sum to vanish mod p.
example {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1)
    (s : ℤ) (h0 : sumOfSquaresRepCount s n = 0) :
    (p : ℤ) ∣ ∑ i ∈ Finset.Icc 1 (p - 1), sumOfSquaresRepCount (s - i) n := by
  by_contra hdiv
  exact (repCount_ne_zero_of_window hn hp hp2 hpn s).1 hdiv h0

end MathlibExtTest.NumberTheory.SquaresTriangularRepresentationsRepCountNeZeroOfWindow
