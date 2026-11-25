/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.PowerSeries.SeriesDivisorProduct

open PowerSeries MetaMathlibExt

-- Both integer series have nonunit constant terms. Their divisor sequences are one
-- even at index zero, which the recurrence omits.
example (n : ℕ) :
    let F := PowerSeries.mk (fun _ ↦ (2 : ℤ)) * PowerSeries.mk (fun _ ↦ (3 : ℤ))
    (n : ℤ) * coeff n F = 2 * ∑ i ∈ Finset.Icc 1 n, coeff (n - i) F := by
  let A (a : ℤ) := PowerSeries.mk (fun _ ↦ a)
  have h (a : ℤ) (k : ℕ) :
      (k : ℤ) * coeff k (A a) = ∑ i ∈ Finset.Icc 1 k, 1 * coeff (k - i) (A a) := by
    simp [A, Nat.card_Icc]
  simpa only [Finset.mul_sum, Int.reduceAdd] using
    series_divisor_add_of_mul (A 2) (A 3) (fun _ ↦ 1) (fun _ ↦ 1) (h 2) (h 3) n
