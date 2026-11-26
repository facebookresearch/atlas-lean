/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisibilityRunsDivRunCountThree

namespace MathlibExtTest.NumberTheory.DivisibilityRunsDivRunCountThree

open MetaMathlibExt

-- No tuple in `[-0, 0]^5` has a nonzero first component, so there is no run.
example : divRunCount 0 3 = 0 := by decide

-- The sixteen length-three runs at bound `1`.
example : divRunCount 1 3 = 16 := by decide

-- The unsymmetrized divisor sum evaluates to the same count at bound `1`.
example : (divRunCount 1 3 : ℤ) = 16 := by
  rw [(divRunCount_three 1).1]
  decide

-- The symmetrized divisor sum evaluates to the same count at bound `1`.
example : (divRunCount 1 3 : ℤ) = 16 := by
  rw [(divRunCount_three 1).2]
  decide

end MathlibExtTest.NumberTheory.DivisibilityRunsDivRunCountThree
