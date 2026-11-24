/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.IncompleteLeonardoPPartialSum

/-!
# Tests for partial sums of incomplete Leonardo p-numbers
-/

open MetaMathlibExt

-- With no summands, both endpoints are the term at index `n`.
example (p n k : ℕ) (hp : 1 ≤ p) (hn : (p + 1) * (k + 1) ≤ n) :
    (∑ i ∈ Finset.range 0, incompleteLeonardoP p (n - p + i) k) =
      incompleteLeonardoP p n (k + 1) - incompleteLeonardoP p n (k + 1) := by
  simpa only [Nat.cast_zero, zero_mul, add_zero] using sum_incompleteLeonardoP p n k 0 hp hn

-- At the lower bound for `p = 2` and `k = 1`, the three terms are 7, 10, and 13.
example : (∑ i ∈ Finset.range 3, incompleteLeonardoP 2 (4 + i) 1) + 6 = 36 := by
  calc
    _ = incompleteLeonardoP 2 9 2 - incompleteLeonardoP 2 6 2 :=
      sum_incompleteLeonardoP 2 6 1 3 (by decide) (by decide)
    _ = 36 := by decide
