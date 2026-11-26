/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisibilityRunsDivRunCountTwo

/-!
# Tests for the exact formula for the length-two run count

At bound `0` there are no configurations, and at bound `1` the divisor sum is `S(1) = 3`
while the run count is `A_1(2) = 104`, both directly and from the closed formula.
-/

namespace MathlibExtTest.NumberTheory.DivisibilityRunsDivRunCountTwo

-- No tuple in `[-0, 0]^5` has a nonzero first component, so there is no run.
example : MetaMathlibExt.divRunCount 0 2 = 0 := by decide

-- The length-two run count at bound `1`.
example : MetaMathlibExt.divRunCount 1 2 = 104 := by decide

-- The divisor sum at bound `1` is `S(1) = 3`, via the divisor-sum identity.
example : ∑ m ∈ Finset.Icc 1 1, (2 * (1 / m) + 1) = 3 := by
  rw [(MetaMathlibExt.divRunCount_two 1).1]
  decide

-- The closed formula evaluates to the same count at bound `1`.
example : (MetaMathlibExt.divRunCount 1 2 : ℤ) = 104 := by
  rw [(MetaMathlibExt.divRunCount_two 1).2]
  decide

end MathlibExtTest.NumberTheory.DivisibilityRunsDivRunCountTwo
