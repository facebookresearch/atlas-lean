/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomialModTwoRunLengthRunLengthTransformChooseAddSubSucc

/-! # Tests for `runLengthTransform_choose_add_sub_succ` -/

namespace MathlibExtTest.NumberTheory.BinomialModTwoRunLengthRunLengthTransformChooseAddSubSucc

open MetaMathlibExt

-- At 0 the sum has the single term for k = 0 and the run length transform is 1.
example : ((∑ k ∈ Finset.range (0 + 1),
    ((0 + k).choose (0 - k) * Nat.choose 0 k) % 2 : ℕ) : ℤ) = 1 := by
  rw [runLengthTransform_choose_add_sub_succ, runLengthTransform_zero]

-- In binary 11 is 1011, with runs of lengths 2 and 1, so both sides equal 6.
example : ((∑ k ∈ Finset.range (11 + 1),
    ((11 + k).choose (11 - k) * Nat.choose 11 k) % 2 : ℕ) : ℤ) = 6 := by
  rw [runLengthTransform_choose_add_sub_succ, runLengthTransform_eleven]
  decide

end MathlibExtTest.NumberTheory.BinomialModTwoRunLengthRunLengthTransformChooseAddSubSucc
