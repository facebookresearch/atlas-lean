/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutationsRecurrence

open MetaMathlibExt

-- The empty permutation cannot supply a marked point, even when the cycle count is positive.
example (k : ℕ) : kPermFixedPointCount 0 (k + 1) 1 = 0 := by
  simpa using mul_kPermFixedPointCount (n := 0) (hj := le_rfl) (hjk := Nat.le_add_left 1 k)

-- Removing two marked points leaves a derangement on the other two elements.
example : kPermFixedPointCount 4 3 2 = 6 * kPermFixedPointCount 2 1 0 := by
  have h₄ := mul_kPermFixedPointCount (n := 4) (k := 3) (j := 2) (by decide) (by decide)
  have h₃ := mul_kPermFixedPointCount (n := 3) (k := 2) (j := 1) (by decide) (by decide)
  simp only [Nat.reduceSub, one_mul] at h₄ h₃
  omega
