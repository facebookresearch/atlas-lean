/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PFrobeniusStarNumbersPSylvesterCountZeroStar

/-!
# Tests for the `0`-Sylvester number of three consecutive star numbers

Concrete instances and a positivity corollary of
`MathlibExt.NumberTheory.PFrobeniusStarNumbersWanted.pSylvesterCount_zero_star`.
-/

namespace MathlibExtTest.NumberTheory.PFrobeniusStarNumbersPSylvesterCountZeroStar

open MathlibExt.NumberTheory.PFrobeniusStarNumbersWanted

example : pSylvesterStarCount 0 6 = 3570 := by
  rw [pSylvesterCount_zero_star 6 le_rfl]
  decide

example : pSylvesterStarCount 0 10 = 15870 := by
  rw [pSylvesterCount_zero_star 10 (by omega)]
  decide

example (n : ℕ) (hn : 6 ≤ n) : 0 < pSylvesterStarCount 0 n := by
  rw [pSylvesterCount_zero_star n hn]
  exact mul_pos (by omega) (by omega)

end MathlibExtTest.NumberTheory.PFrobeniusStarNumbersPSylvesterCountZeroStar
