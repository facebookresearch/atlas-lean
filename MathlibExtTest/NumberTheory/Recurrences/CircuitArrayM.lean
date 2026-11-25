/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.CircuitArrayM
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

-- The first two entries of row one in Table 3 of Evans and Hendel.
example : circuitArrayM 1 2 = (circuitVar 1 + 8) / (3 * circuitVar 1 + 6) := by
  rw [circuitArrayM_row_one 2 le_rfl]
  norm_num
  congr 1 <;> ring

example : circuitArrayM 1 3 = (circuitVar 1 + 80) / (3 * (circuitVar 1 + 26)) := by
  rw [circuitArrayM_row_one 3 (by decide)]
  norm_num
  congr 1 <;> ring

-- The left boundary in the same third column receives the new variable.
example : circuitArrayM 4 3 = circuitVar 3 := by
  simp [circuitArrayM, circuitArrayOf, circuitGrid, show Even (4 : ℕ) by decide]

end MetaMathlibExt
