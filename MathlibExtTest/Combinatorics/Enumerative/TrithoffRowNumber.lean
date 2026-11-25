/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrithoffRowNumber

/-! # Tests for row numbers of the Trithoff array -/

namespace MetaMathlibExt.trithoff_row_number_eq

private def firstColumn (m : ℕ) : Prop :=
  0 < m ∧ ∃ w, IsTribonacciRepr w m ∧ w.getD 0 0 = 1

-- The empty prefix gives the first row, at index zero.
example : Nat.nth firstColumn 0 = 1 ∧ 1 = 1 + 0 :=
  trithoff_row_number_eq [] 1 (by unfold IsTribonacciRepr; decide)

-- The padded word 01101 represents 12. Its nonzero U-weights are 2 and 3.
example : Nat.nth firstColumn 5 = 12 ∧ 6 = 1 + (2 + 3) :=
  trithoff_row_number_eq [0, 1, 1, 0] 12 (by unfold IsTribonacciRepr; decide)

end MetaMathlibExt.trithoff_row_number_eq
