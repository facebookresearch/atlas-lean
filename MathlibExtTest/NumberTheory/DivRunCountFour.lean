/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivRunCountFour

namespace MetaMathlibExt

-- No tuple in `[-0, 0]^5` has a nonzero first component, so there is no run.
example : divRunCount 0 4 = 0 := by decide

-- The four length-four runs at bound `1` are the tuples with `x = y = ±1`,
-- `c = 0` and `b = -a` with `|a| = 1`.
example : divRunCount 1 4 = 4 := by decide

-- The unscaled divisor sum evaluates to the same count at bound `1`.
example : (divRunCount 1 4 : ℤ) = 4 := by
  rw [(divRunCount_four 1).1]
  decide

-- The scaled divisor sum evaluates to the same count at bound `1`.
example : (divRunCount 1 4 : ℤ) = 4 := by
  rw [(divRunCount_four 1).2]
  decide

end MetaMathlibExt
