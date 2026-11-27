/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AscentSequenceQuadrupleCardFormulas

namespace MetaMathlibExt

-- Both families are empty for lengths up to five: every sum in the formulas is empty there.
example (n : ℕ) (h1 : 1 ≤ n) (h5 : n ≤ 5) :
    (quadrupleUSet n 1).ncard = 0 ∧ (quadrupleVSet n 1).ncard = 0 := by
  rw [quadrupleUSet_quadrupleVSet_card_formulas.1 n h1,
    quadrupleUSet_quadrupleVSet_card_formulas.2.1 n h1]
  rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) with
    rfl | rfl | rfl | rfl | rfl <;> decide

-- The first nonempty length: `001032` is the only element of `U_{6,1}` and `000213` the only
-- element of `V_{6,1}`.
example : (quadrupleUSet 6 1).ncard = 1 ∧ (quadrupleVSet 6 1).ncard = 1 := by
  rw [quadrupleUSet_quadrupleVSet_card_formulas.1 6 (by decide),
    quadrupleUSet_quadrupleVSet_card_formulas.2.1 6 (by decide)]
  decide

-- At length nine the sum for `U` has two indices, and the two families have the same size.
example : (quadrupleUSet 9 1).ncard = 57 ∧ (quadrupleVSet 9 1).ncard = 57 := by
  rw [quadrupleUSet_quadrupleVSet_card_formulas.1 9 (by decide),
    quadrupleUSet_quadrupleVSet_card_formulas.2.1 9 (by decide)]
  decide

-- A multiple of three: the even term at the last index of the sum for `U` vanishes.
example : (quadrupleUSet 12 1).ncard = 1341 := by
  rw [quadrupleUSet_quadrupleVSet_card_formulas.1 12 (by decide)]
  decide

-- The integer form at its smallest length, where `2 ^ (n - 4) - n + 3 = 0`.
example : ((quadrupleVSet 4 1).ncard : ℤ) = 0 := by
  rw [quadrupleUSet_quadrupleVSet_card_formulas.2.2 4 le_rfl]
  decide

-- The integer form agrees with the first form for `V` at length ten.
example : ((quadrupleVSet 10 1).ncard : ℤ) = 169 := by
  rw [quadrupleUSet_quadrupleVSet_card_formulas.2.2 10 (by decide)]
  decide

end MetaMathlibExt
