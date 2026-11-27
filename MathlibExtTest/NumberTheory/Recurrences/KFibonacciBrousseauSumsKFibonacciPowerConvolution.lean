/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSumsKFibonacciPowerConvolution

/-!
# Tests for the power-weighted k-Fibonacci convolution

We derive the constant-weight sum and check zero endpoints and positive and negative parameters.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 4 (`jis-2024-24.6.4-thm-4`).
-/

namespace MathlibExtTest.NumberTheory.Recurrences.KFibonacciBrousseauSumsKFibonacciPowerConvolution

open MetaMathlibExt

example (k : ℤ) (hk : k ≠ 0) (n : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.range (n + 1), (lucasU ⟨k, -1, by decide⟩ (n - i) : ℚ) =
      (lucasU ⟨k, -1, by decide⟩ (n + 1) : ℚ) + lucasU ⟨k, -1, by decide⟩ n - 1 := by
  simpa [brousseauA_zero, add_sub_assoc] using kFibonacci_power_convolution k hk n 0

example (k : ℤ) (hk : k ≠ 0) (p : ℕ) :
    brousseauA k p = ∑ r ∈ Finset.range (p + 1),
      brousseauA k r * (p.choose r : ℚ) * (0 : ℚ) ^ (p - r) := by
  have h : (0 : ℚ) = brousseauA k p - ∑ r ∈ Finset.range (p + 1),
      brousseauA k r * (p.choose r : ℚ) * (0 : ℚ) ^ (p - r) := by
    simpa [lucasU, Finset.sum_neg_distrib, sub_eq_add_neg] using
      kFibonacci_power_convolution k hk 0 p
  exact sub_eq_zero.mp h.symm

example :
    (2 : ℚ) * ∑ i ∈ Finset.range 4, (i : ℚ) ^ 2 * lucasU ⟨2, -1, by decide⟩ (3 - i) =
      12 := by
  convert kFibonacci_power_convolution 2 (by decide) 3 2 using 1
  norm_num [Finset.sum_range_succ, brousseauA_zero, brousseauA_one, brousseauA_two,
    lucasU, Nat.choose]

example :
    (-2 : ℚ) * ∑ i ∈ Finset.range 4, (i : ℚ) ^ 2 * lucasU ⟨-2, -1, by decide⟩ (3 - i) =
      -4 := by
  convert kFibonacci_power_convolution (-2) (by decide) 3 2 using 1 <;>
    norm_num [Finset.sum_range_succ, brousseauA_zero, brousseauA_one, brousseauA_two,
      lucasU, Nat.choose]

end MathlibExtTest.NumberTheory.Recurrences.KFibonacciBrousseauSumsKFibonacciPowerConvolution
