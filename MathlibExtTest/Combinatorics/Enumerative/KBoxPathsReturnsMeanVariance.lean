/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Enumerative.KBoxPathsReturnsMeanVariance

/-! Tests for the mean and variance of the number of returns of $k$-box paths. -/

open MetaMathlibExt SkewDyckStep

namespace MathlibExtTest.KBoxPathsReturnsMeanVariance

-- At size one there is a single path, with one return.
example : (kBoxPaths 1 1).card = 1 ∧ ∑ w ∈ kBoxPaths 1 1, skewReturns w = 1 := by
  decide +kernel

-- The mean and variance at size one: mean `1`, variance `0`.
example : (∑ w ∈ kBoxPaths 1 1, (skewReturns w : ℚ)) / (kBoxPaths 1 1).card = 1 ∧
    (∑ w ∈ kBoxPaths 1 1, (skewReturns w : ℚ) ^ 2) / (kBoxPaths 1 1).card -
      ((∑ w ∈ kBoxPaths 1 1, (skewReturns w : ℚ)) / (kBoxPaths 1 1).card) ^ 2 = 0 := by
  have h := kBoxPaths_returns_mean_variance (k := 1) (n := 1) le_rfl le_rfl
  constructor
  · rw [h.1]
    norm_num
  · rw [h.2]
    norm_num

-- The mean and variance at size two: mean `3 / 2`, variance `1 / 4`.
example : (∑ w ∈ kBoxPaths 1 2, (skewReturns w : ℚ)) / (kBoxPaths 1 2).card = 3 / 2 ∧
    (∑ w ∈ kBoxPaths 1 2, (skewReturns w : ℚ) ^ 2) / (kBoxPaths 1 2).card -
      ((∑ w ∈ kBoxPaths 1 2, (skewReturns w : ℚ)) / (kBoxPaths 1 2).card) ^ 2 =
      1 / 4 := by
  have h := kBoxPaths_returns_mean_variance (k := 1) (n := 2) le_rfl (by decide)
  constructor
  · rw [h.1]
    norm_num
  · rw [h.2]
    norm_num

-- The augmented Dyck generating function satisfies the Fuss–Catalan equation.
example : augmentedKDyckGF 2 =
    1 + PowerSeries.X * augmentedKDyckGF 2 ^ 3 :=
  augmentedKDyckGF_eq (k := 1) le_rfl

end MathlibExtTest.KBoxPathsReturnsMeanVariance
