/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SizeChooseTwoPow

/-! # Tests for `MathlibExt.NumberTheory.SizeChooseTwoPow` -/

namespace MathlibExtTest.SizeChooseTwoPow

open MathlibExt.NumberTheory.OeisConjecturesWanted

-- The smallest case `n = 1`: `C(2, 1) = 2`, written `10` in binary, has `2 ^ 1 - 1 / 2 = 2`
-- binary digits.
example : Nat.size (Nat.choose 2 1) = 2 := size_choose_two_pow 1 le_rfl

-- An independent check at `n = 4`, without the theorem: `2 ^ 13 ≤ C(16, 8) = 12870 < 2 ^ 14`,
-- so `C(16, 8)` has `14` binary digits.
example : Nat.size (Nat.choose 16 8) = 14 := by
  rw [show Nat.choose 16 8 = 12870 by decide]
  exact le_antisymm (Nat.size_le.2 (by decide)) (Nat.lt_size.2 (by decide))

-- The theorem gives the same count `2 ^ 4 - 4 / 2 = 14`.
example : Nat.size (Nat.choose 16 8) = 14 := by
  simpa using size_choose_two_pow 4 (by decide)

-- Odd and even `n` beyond the reach of evaluating `Nat.choose` by its recursion: `C(128, 64)`
-- has `2 ^ 7 - 3 = 125` binary digits and `C(1024, 512)` has `2 ^ 10 - 5 = 1019`.
example : Nat.size (Nat.choose 128 64) = 125 := by
  simpa using size_choose_two_pow 7 (by decide)

example : Nat.size (Nat.choose 1024 512) = 1019 := by
  simpa using size_choose_two_pow 10 (by decide)

-- Edge case `n = 0`, outside the hypothesis `1 ≤ n` (which follows the source): the truncated
-- subtraction `0 - 1 = 0` makes the left side `Nat.size (Nat.choose 1 1) = 1`, and the right
-- side is `2 ^ 0 - 0 / 2 = 1`.
example : Nat.size (Nat.choose (2 ^ 0) (2 ^ (0 - 1))) = 2 ^ 0 - 0 / 2 := by
  simp

end MathlibExtTest.SizeChooseTwoPow
