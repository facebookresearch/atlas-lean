/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasBinomialSum

open MetaMathlibExt

-- At the first index the sum has just the constant term.
example (P : LucasSequenceParams) : lucasU P 1 = 1 := by
  rw [lucasU_eq_sum_choose P (by decide)]
  simp

-- For p = 0 and q = 2, the odd term comes entirely from the last summand;
-- in the even term every exponent of p is positive.
example : lucasU ⟨0, 2, by decide⟩ 7 = -8 := by
  rw [lucasU_eq_sum_choose _ (by decide)]
  decide

example : lucasU ⟨0, 2, by decide⟩ 6 = 0 := by
  rw [lucasU_eq_sum_choose _ (by decide)]
  decide

-- With negative p, several nonzero summands contribute.
example : lucasU ⟨-2, 3, by decide⟩ 6 = 10 := by
  rw [lucasU_eq_sum_choose _ (by decide)]
  decide
