/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RascalNumbers

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

-- The first admissible order, starting on the diagonal.
example (k : ℕ) :
    rascalZ k k - 2 * rascalZ (k + 1) k + rascalZ (k + 2) k = 0 := by
  simpa [Finset.sum_range_succ, Nat.choose, sub_eq_add_neg, Int.neg_mul] using
    sum_negOnePow_choose_rascalZ k k 2 le_rfl le_rfl

-- The first difference can be nonzero.
example : rascalZ 3 2 - rascalZ 2 2 = 2 := by decide

-- Starting one row before the diagonal, even the second difference can be nonzero.
example : rascalZ 1 2 - 2 * rascalZ 2 2 + rascalZ 3 2 = 1 := by decide

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
