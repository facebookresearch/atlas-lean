/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumsetFour

open MetaMathlibExt

-- The boundary value is attained even with unequal gaps.
example : (restrictedSignedSumset 4 {0, 1, 2, 4, 6}).card = 21 := by
  apply le_antisymm (by decide +kernel)
  have h := card_restrictedSignedSumset_four_nonnegative_ge 5 {0, 1, 2, 4, 6}
    (by decide) (by decide) (by decide) (by decide)
  omega

-- Adding a sixth term to a dilated interval attains the next bound.
example : (restrictedSignedSumset 4 {0, 2, 4, 6, 8, 10}).card = 29 := by
  apply le_antisymm (by decide +kernel)
  have h := card_restrictedSignedSumset_four_nonnegative_ge 6 {0, 2, 4, 6, 8, 10}
    (by decide) (by decide) (by decide) (by decide)
  omega
