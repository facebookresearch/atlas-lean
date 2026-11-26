/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.ParityNotInAC0

/-! # Tests for `CSLibExt.Computability.Complexity.ParityNotInAC0` -/

namespace MetaMathlibExt.Complexity.KeyTheorems.ParityNotInAC0

open Cslib.Complexity.Classes

-- The moved theorem is available with the original statement from the new module alone.
example : parityDec ∉ AC0 := parity_not_in_ac0

-- `AC0` contains every language that depends only on the input length (an existing test), but
-- not parity, so `AC0` is a proper class of decision problems.
example : AC0 ≠ Set.univ := fun h => parity_not_in_ac0 (h ▸ Set.mem_univ _)

-- Parity counts the true entries modulo two, including on the empty word.
example : parityDec [] = false ∧ parityDec [true] = true ∧ parityDec [true, false, true] = false :=
  by decide

end MetaMathlibExt.Complexity.KeyTheorems.ParityNotInAC0
