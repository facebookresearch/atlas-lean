/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivRunCountOne

namespace MetaMathlibExt

-- At bound zero the only candidate has a zero divisor.
example : divRunCount 0 1 = 0 := by decide

-- Count directly from the run predicate at a bound with more than one divisor magnitude.
example : divRunCount 2 1 = 1980 := by decide +kernel

-- The closed formula agrees with that direct count.
example : divRunCount 2 1 = 1980 := by
  rw [divRunCount_one]
  decide

end MetaMathlibExt
