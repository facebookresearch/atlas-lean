/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PerrinZeroUnique

namespace MetaMathlibExt

example : perrinSequence 1 = 0 := (perrin_zero_unique.1 1).2 rfl

example : perrinSequence 0 ≠ 0 := fun h => Nat.zero_ne_one ((perrin_zero_unique.1 0).1 h)

example : perrinNeg 0 = (perrinSequence 0 : ℤ) := perrinNeg_bridge.1

-- Index −27 is in the same zero residue class modulo eight as the term at index one.
example : perrinNeg 27 % 8 = 0 := by decide

example : perrinNeg 27 ≠ 0 := perrin_zero_unique.2 27

end MetaMathlibExt
