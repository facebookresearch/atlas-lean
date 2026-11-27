/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RamanujanHarmonicIdentitySumChooseSubChooseMulHarmonicEqAdd
import Mathlib.Tactic.NormNum

/-!
# Tests for the shifted binomial–harmonic convolution

We specialize the convolution to an endpoint case and two interior cases, one with $k = 2$.

Source: Horst Alzer and Man Kam Kwong,
"Ramanujan and a Combinatorial Identity Involving Harmonic Numbers",
*Journal of Integer Sequences* 29 (2026), Article 26.4.8.
-/

namespace MathlibExtTest.NumberTheory.RamanujanHarmonicIdentitySumChooseSubChooseMulHarmonicEqAdd

open MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

example :
    ∑ ν ∈ Finset.Icc 1 2,
      ((Nat.choose (3 - ν - 1) 0 : ℚ) - (Nat.choose (3 - ν - 1) 1 : ℚ)) * harmonic ν =
      3 / 2 := by
  convert sum_choose_sub_choose_mul_harmonic_eq_add 1 2 (by decide) (by decide) using 1
  norm_num [Nat.choose, harmonic, Finset.sum_range_succ]

example :
    ∑ ν ∈ Finset.Icc 1 4,
      ((Nat.choose (5 - ν - 1) 2 : ℚ) - (Nat.choose (5 - ν - 1) 1 : ℚ)) * harmonic ν =
      -10 / 3 := by
  convert sum_choose_sub_choose_mul_harmonic_eq_add 1 4 (by decide) (by decide) using 1
  norm_num [Nat.choose, harmonic, Finset.sum_range_succ]

example :
    ∑ ν ∈ Finset.Icc 1 5,
      ((Nat.choose (7 - ν - 1) 3 : ℚ) - (Nat.choose (7 - ν - 1) 2 : ℚ)) * harmonic ν =
      -35 / 4 := by
  convert sum_choose_sub_choose_mul_harmonic_eq_add 2 5 (by decide) (by decide) using 1
  norm_num [Nat.choose, harmonic, Finset.sum_range_succ]

end MathlibExtTest.NumberTheory.RamanujanHarmonicIdentitySumChooseSubChooseMulHarmonicEqAdd
