/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumsetFour
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

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

-- The first gap is smaller than twice the minimum.
example : ((restrictedSignedSumset 4 (orderedFinset ![1, 2, 4, 6, 8])).card : ℤ) ≥ 26 := by
  exact card_restrictedSignedSumset_four_ge_of_one_exceptional_gap
    (a := ![1, 2, 4, 6, 8])
    (ha := by intro i j hij; fin_cases i <;> fin_cases j <;> first | contradiction | decide)
    (hpos := by decide) (hgaps := by decide +kernel)

-- The last gap is larger than twice the minimum. Some sums coincide, including zero
-- from both signs of `1 + 3 + 7 - 11`, and the actual cardinality is 27.
example : ((restrictedSignedSumset 4 (orderedFinset ![1, 3, 5, 7, 11])).card : ℤ) ≥ 26 := by
  exact card_restrictedSignedSumset_four_ge_of_one_exceptional_gap
    (a := ![1, 3, 5, 7, 11])
    (ha := by intro i j hij; fin_cases i <;> fin_cases j <;> first | contradiction | decide)
    (hpos := by decide) (hgaps := by decide +kernel)

example : (restrictedSignedSumset 4 (orderedFinset ![1, 3, 5, 7, 11])).card = 27 := by
  decide +kernel
