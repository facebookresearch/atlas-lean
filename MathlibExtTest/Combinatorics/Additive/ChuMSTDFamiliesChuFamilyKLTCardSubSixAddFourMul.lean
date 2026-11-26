/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTCardSubSixAddFourMul

namespace MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTCardSubSixAddFourMul

open MetaMathlibExt
open scoped Pointwise

example :
    ((chuFamilyKLT 1 1 1 - chuFamilyKLT 1 1 1).filter
      fun d => 6 ≤ d ∧ d % 4 = 2).card = 2 :=
  chuFamilyKLT_card_sub_six_add_four_mul (by decide) (by decide) (by decide)

example :
    ((chuFamilyKLT 2 2 2 - chuFamilyKLT 2 2 2).filter
      fun d => 6 ≤ d ∧ d % 4 = 2).card = 6 :=
  chuFamilyKLT_card_sub_six_add_four_mul (by decide) (by decide) (by decide)

example {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    ((chuFamilyKLT k l 1 - chuFamilyKLT k l 1).filter
      fun d => 6 ≤ d ∧ d % 4 = 2).card = l + 1 := by
  simpa using chuFamilyKLT_card_sub_six_add_four_mul hk hl (by decide : 0 < 1)

end MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTCardSubSixAddFourMul
