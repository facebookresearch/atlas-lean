/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlzerRichardsFubiniIdentity

open Finset MetaMathlibExt

private def alternatingStirling (r k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1),
    (-1 : ℤ) ^ j * (k.choose j : ℤ) * (j.factorial : ℤ) * (Nat.stirlingSecond r j : ℤ)

-- At the first admissible index the signed sum is negative.
example :
    (∑ k ∈ range 1, (1 : ℕ).choose k * (fubiniNumber k : ℤ) *
        ∑ ν ∈ range 3, (2 : ℕ).choose ν * (alternatingStirling (1 - k) ν : ℤ)) +
      (2 ^ (1 + 1) - 1) * fubiniNumber 1 = (-1 : ℤ) := by
  have h := sum_fubiniNumber_mul_sum_alternatingStirling (n := 1) (hn := by decide)
    alternatingStirling (hA := fun _ _ => rfl)
  exact h.trans (by decide)

-- The third row includes mixed signs and a nonzero contribution from the last index.
example :
    (∑ k ∈ range 3, (3 : ℕ).choose k * (fubiniNumber k : ℤ) *
        ∑ ν ∈ range 5, (4 : ℕ).choose ν * (alternatingStirling (3 - k) ν : ℤ)) +
      (2 ^ (3 + 1) - 1) * fubiniNumber 3 = (19 : ℤ) := by
  have h := sum_fubiniNumber_mul_sum_alternatingStirling (n := 3) (hn := by decide)
    alternatingStirling (hA := fun _ _ => rfl)
  exact h.trans (by decide)
