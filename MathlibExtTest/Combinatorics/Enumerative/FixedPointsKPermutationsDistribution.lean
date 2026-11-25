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
