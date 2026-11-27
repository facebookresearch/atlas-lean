/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ParityRestrictedCompositions

open MetaMathlibExt

-- The empty composition is counted for every negative odd shift.
example (j : ℕ) : kArndtTotalCount (-(2 * j + 1 : ℤ)) 0 = 1 := by
  rw [kArndtTotalCount_neg_odd]
  simp [evenOrSmallOddCompositionCount]

-- For shift −1 the correction first counts the empty composition at weight three.
example : kArndtTotalCount (-1) 3 = 3 :=
  (kArndtTotalCount_neg_odd 0 3).trans (by decide)

-- The three thresholds in Hopkins and Tangboonduangjit's Table 6.
example : kArndtTotalCount (-1) 5 = 10 ∧ kArndtTotalCount (-3) 5 = 15 ∧
    kArndtTotalCount (-5) 5 = 16 :=
  ⟨(kArndtTotalCount_neg_odd 0 5).trans (by decide),
    (kArndtTotalCount_neg_odd 1 5).trans (by decide),
    (kArndtTotalCount_neg_odd 2 5).trans (by decide)⟩

-- At the least valid weight neither correction is active.
example : (evenOrSmallOddCompositionCount 1 3 : ℤ) = 4 ∧
    (oddOrSmallEvenCompositionCount 1 3 : ℤ) = 4 := by
  obtain ⟨he, ho⟩ := evenOrSmallOdd_oddOrSmallEven_recurrence 1 3 (by decide) (by decide)
  exact ⟨he.trans (by decide), ho.trans (by decide)⟩

-- At weight four only the odd-or-small-even correction counts the empty composition.
example : (evenOrSmallOddCompositionCount 1 4 : ℤ) = 8 ∧
    (oddOrSmallEvenCompositionCount 1 4 : ℤ) = 7 := by
  obtain ⟨he, ho⟩ := evenOrSmallOdd_oddOrSmallEven_recurrence 1 4 (by decide) (by decide)
  exact ⟨he.trans (by decide), ho.trans (by decide)⟩

-- At weight five the even-or-small-odd correction also activates.
example : (evenOrSmallOddCompositionCount 1 5 : ℤ) = 15 ∧
    (oddOrSmallEvenCompositionCount 1 5 : ℤ) = 14 := by
  obtain ⟨he, ho⟩ := evenOrSmallOdd_oddOrSmallEven_recurrence 1 5 (by decide) (by decide)
  exact ⟨he.trans (by decide), ho.trans (by decide)⟩

-- The correction is inactive at weight two, and each proposed right side is 3, not 2.
example : (evenOrSmallOddCompositionCount 1 2 : ℤ) ≠
      evenOrSmallOddCompositionCount 1 1 + 2 * evenOrSmallOddCompositionCount 1 0 ∧
    (oddOrSmallEvenCompositionCount 1 2 : ℤ) ≠
      oddOrSmallEvenCompositionCount 1 1 + 2 * oddOrSmallEvenCompositionCount 1 0 := by
  decide
