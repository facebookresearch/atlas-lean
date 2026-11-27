/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.RamanujanShiftedHarmonicConvolution

open MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

-- Evaluate the sum directly at the minimum k = n = 2, where the last top index is zero.
example :
    (∑ ν ∈ Finset.Icc 1 3,
      ((Nat.choose (4 - ν - 1) 2 : ℚ) - (Nat.choose (4 - ν - 1) 0 : ℚ)) * harmonic ν) =
      -10 / 3 := by
  rw [Finset.sum_Icc_succ_top (show 1 ≤ 3 by decide),
    Finset.sum_Icc_succ_top (show 1 ≤ 2 by decide)]
  norm_num [Nat.choose, harmonic_succ]

-- Apply the public theorem on the diagonal and with strictly separated parameters.
example :
    (∑ ν ∈ Finset.Icc 1 3,
      ((Nat.choose (4 - ν - 1) 2 : ℚ) - (Nat.choose (4 - ν - 1) 0 : ℚ)) * harmonic ν) =
      -10 / 3 := by
  rw [sum_choose_sub_choose_mul_harmonic_succ_eq 2 2 (by decide) (by decide)]
  norm_num [Nat.choose, harmonic_succ]

example :
    (∑ ν ∈ Finset.Icc 1 6,
      ((Nat.choose (8 - ν - 1) 5 : ℚ) - (Nat.choose (8 - ν - 1) 1 : ℚ)) * harmonic ν) =
      -133 / 5 := by
  rw [sum_choose_sub_choose_mul_harmonic_succ_eq 3 5 (by decide) (by decide)]
  norm_num [Nat.choose, harmonic_succ]
