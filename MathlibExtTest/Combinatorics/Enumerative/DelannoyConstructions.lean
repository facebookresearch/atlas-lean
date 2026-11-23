/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.DelannoyConstructions

namespace MetaMathlibExt.DelannoyConstructions

-- At the first positive column, the sum of consecutive natural numbers is odd.
example (n : ℕ) : n + (n + 1) ≡ 1 [MOD 2] := by
  simpa using choose_add_choose_succ_modEq_two n 1 le_rfl

-- Allowing column zero would give the wrong parity because natural subtraction truncates.
example : ¬ ((0 : ℕ).choose 0 + (0 + 1).choose 0 ≡ (0 : ℕ).choose (0 - 1) [MOD 2]) := by
  decide

end MetaMathlibExt.DelannoyConstructions
