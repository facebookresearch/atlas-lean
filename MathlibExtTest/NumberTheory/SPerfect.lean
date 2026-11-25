/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SPerfect

/-!
# Tests for weighted perfect numbers
-/

namespace MetaMathlibExt

-- The weights on the proper divisors of six can give a negative integer.
example : IsSPerfect {-2, -1} (-6) := by
  refine ⟨by decide, fun d => if d = 2 then -2 else -1, ?_, by decide⟩
  intro d _
  by_cases h : d = 2 <;> simp [h]

example (S : Set ℤ) : ¬ IsSPerfect S 1 := fun h => (by decide : ¬ 1 < (1 : ℤ).natAbs) h.1

end MetaMathlibExt
