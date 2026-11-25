/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumRecurrences

open Finset MetaMathlibExt

-- On the diagonal the half-open summation range is empty, even at degree zero.
example (ℓ : ℕ) (x y : ℂ) : alternatingBinomialPowerSum ℓ (ℓ + 1) x y = 0 := by
  simpa using (alternatingBinomialPowerSum_recurrences x y ℓ ℓ).2.2.1

-- At order zero the correction term involving the predecessor drops out.
example (ℓ : ℕ) (x y : ℂ) :
    alternatingBinomialPowerSum (ℓ + 1) 0 x y = y * alternatingBinomialPowerSum ℓ 0 x y := by
  simpa using (alternatingBinomialPowerSum_recurrences x y ℓ 0).2.2.2.1

-- The first difference of a quadratic has constant derivative in the shift parameter.
example (x y : ℂ) : deriv (fun z => alternatingBinomialPowerSum 2 1 x z) y = -2 * x := by
  rw [(alternatingBinomialPowerSum_recurrences x y 2 1).2.2.2.2.2.1 (by decide)]
  simp [alternatingBinomialPowerSum, sum_range_succ]

-- At the positive endpoint the derivative vanishes, but the order-zero correction does not.
example : deriv (fun z => alternatingBinomialPowerSum 1 1 1 (z + 1)) 0 = 0 ∧
    alternatingBinomialPowerSum 1 1 1 (0 + 1) = -1 := by
  obtain ⟨hd, hr⟩ := carlitzSum_deriv_and_recurrence (ℓ := 1) (m := 1) (by decide) (by decide) 0
  constructor
  · rw [hd]
    norm_num [alternatingBinomialPowerSum, sum_range_succ]
  · rw [hr]
    norm_num [alternatingBinomialPowerSum, sum_range_succ]

-- A shifted quadratic at order one has derivative -2 and value -5 at n = 1.
example : deriv (fun z => alternatingBinomialPowerSum 2 1 1 (z + 1)) 1 = -2 ∧
    alternatingBinomialPowerSum 2 1 1 (1 + 1) = -5 := by
  obtain ⟨hd, hr⟩ := carlitzSum_deriv_and_recurrence (ℓ := 2) (m := 1) (by decide) (by decide) 1
  constructor
  · rw [hd]
    norm_num [alternatingBinomialPowerSum, sum_range_succ]
  · rw [hr]
    norm_num [alternatingBinomialPowerSum, sum_range_succ]

-- Use both predecessor sums at order two and degree three.
example : deriv (fun z => alternatingBinomialPowerSum 3 2 1 (z + 1)) 1 = 6 ∧
    alternatingBinomialPowerSum 3 2 1 (1 + 1) = 18 := by
  obtain ⟨hd, hr⟩ := carlitzSum_deriv_and_recurrence (ℓ := 3) (m := 2) (by decide) (by decide) 1
  constructor
  · rw [hd]
    norm_num [alternatingBinomialPowerSum, sum_range_succ, Nat.choose_succ_succ]
  · rw [hr]
    norm_num [alternatingBinomialPowerSum, sum_range_succ, Nat.choose_succ_succ]
