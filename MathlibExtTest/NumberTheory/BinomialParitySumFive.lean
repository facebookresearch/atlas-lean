/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomialParitySumFive

open MetaMathlibExt

namespace MetaMathlibExt.runLengthTransform_choose_add_five_mul_two_mul_add_two_mul

private def seq : ℕ → ℤ
  | 0 | 1 | 2 | 3 => 1
  | n + 4 => seq (n + 3) + seq (n + 2) - seq (n + 1) + seq n

private theorem seq_rec (m : ℕ) (hm : 4 ≤ m) :
    seq m = seq (m - 1) + seq (m - 2) - seq (m - 3) + seq (m - 4) := by
  obtain ⟨c, rfl⟩ : ∃ c, m = c + 4 := ⟨m - 4, by omega⟩
  rw [seq]
  rfl

-- The empty binary expansion contributes the empty product.
example : ((∑ k ∈ Finset.range 1, ((0 + 5 * k).choose (2 * 0 + 2 * k) *
    (0 : ℕ).choose k) % 2 : ℕ) : ℤ) = 1 := by
  exact (runLengthTransform_choose_add_five_mul_two_mul_add_two_mul seq
    rfl rfl rfl rfl seq_rec 0).trans (runLengthTransform_zero _)

-- The zero between the two runs in 1111011111 gives separate factors S(4) = 2 and S(5) = 3.
example : ((∑ k ∈ Finset.range (991 + 1), ((991 + 5 * k).choose (2 * 991 + 2 * k) *
    (991 : ℕ).choose k) % 2 : ℕ) : ℤ) = 6 := by
  rw [runLengthTransform_choose_add_five_mul_two_mul_add_two_mul seq rfl rfl rfl rfl seq_rec,
    runLengthTransform, show binaryRunLengths 991 = [5, 4] by decide]
  decide

end MetaMathlibExt.runLengthTransform_choose_add_five_mul_two_mul_add_two_mul
