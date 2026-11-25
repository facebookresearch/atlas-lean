/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutationsDistribution
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.Combinatorics.Enumerative.FixedPointsKPermutationsDistribution

open MetaMathlibExt

-- The empty set has no permutations with a positive cycle count.
example {k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (k + 1), j * kPermFixedPointCount 0 k j = 0 := by
  simpa only [zero_mul] using sum_mul_kPermFixedPointCount (n := 0) hk

-- The two-cycle permutations of four points have eight fixed points in total.
example : ∑ j ∈ Finset.range 3, j * kPermFixedPointCount 4 2 j = 8 := by
  have h := sum_mul_kPermFixedPointCount (n := 4) (k := 2) (hk := by decide)
  norm_num [Nat.stirlingFirst] at h
  exact h

-- At the minimum allowed cycle count, the identity on two points has zero variance.
example : (∑ j ∈ Finset.range 3, (j : ℚ) ^ 2 * kPermFixedPointCount 2 2 j) - 2 ^ 2 = 0 := by
  have h := kPermFixedPoint_variance (n := 2) (k := 2) (hk := by decide) (hkn := by decide)
  norm_num [Nat.stirlingFirst] at h ⊢
  exact h

-- Of the eleven permutations of four elements with two cycles, eight have one fixed point.
example : (∑ j ∈ Finset.range 3, (j : ℚ) ^ 2 * kPermFixedPointCount 4 2 j) / 11 -
    (8 / 11 : ℚ) ^ 2 = 24 / 121 := by
  have h := kPermFixedPoint_variance (n := 4) (k := 2) (hk := by decide) (hkn := by decide)
  norm_num [Nat.stirlingFirst] at h ⊢
  exact h

end MathlibExtTest.Combinatorics.Enumerative.FixedPointsKPermutationsDistribution
