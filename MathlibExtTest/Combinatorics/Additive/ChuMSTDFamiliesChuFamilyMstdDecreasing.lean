/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyMstdDecreasing

namespace MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyMstdDecreasing

open MetaMathlibExt Pointwise

example :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock (1 + 1) ++ chuBlock 1 ++ [1, 1])
    (A - A).card < (A + A).card :=
  chu_family_mstd_decreasing (by decide) (Or.inl rfl)

example :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock (1 + 1) ++ chuBlock 1 ++ [1, 1, 2])
    (A - A).card < (A + A).card :=
  chu_family_mstd_decreasing (by decide) (Or.inr (Or.inl rfl))

example :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock (1 + 1) ++ chuBlock 1 ++ [1, 1, 2, 1])
    (A - A).card < (A + A).card :=
  chu_family_mstd_decreasing (by decide) (Or.inr (Or.inr rfl))

end MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyMstdDecreasing
