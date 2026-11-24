/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.IncompleteLeonardoPBinomialSum

/-!
# Tests for the binomial sum identity for incomplete Leonardo p-numbers
-/

open MetaMathlibExt

-- The terms of the identity at the smallest admissible index `n = p + r`, for `p = 1`, `r = 2`
-- and `k = 0`: it reads `1 + 2 * 7 + 15 + 3 = 33`.
example : incompleteLeonardoP 1 3 0 = 1 ∧ incompleteLeonardoP 1 4 1 = 7 ∧
    incompleteLeonardoP 1 5 2 = 15 ∧ incompleteLeonardoP 1 7 2 = 33 := by
  decide

-- The theorem applies at that boundary, where the cutoff `k = 0` is also the largest allowed one.
example :
    incompleteLeonardoP 1 3 0 + 2 * incompleteLeonardoP 1 4 1 + incompleteLeonardoP 1 5 2 + 3 =
      incompleteLeonardoP 1 7 2 := by
  simpa [Finset.sum_range_succ] using
    sum_choose_mul_incompleteLeonardoP 1 3 2 0 le_rfl (by decide) (by decide)

-- For `r = 1` the identity is the recurrence for incomplete Leonardo p-numbers at index
-- `n + p + 1`.
example (p n k : ℕ) (hp : 1 ≤ p) (hn : p + 1 ≤ n) (hk : k ≤ (n - p - 1) / (p + 1)) :
    incompleteLeonardoP p n k + incompleteLeonardoP p (n + p) (k + 1) + p =
      incompleteLeonardoP p (n + p + 1) (k + 1) := by
  simpa [Finset.sum_range_succ, add_assoc] using
    sum_choose_mul_incompleteLeonardoP p n 1 k hp hn hk
