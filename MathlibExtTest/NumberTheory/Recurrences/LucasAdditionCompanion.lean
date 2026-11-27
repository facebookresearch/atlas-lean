/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasAdditionCompanion

open MetaMathlibExt

-- The correction term vanishes on the diagonal, including at m = n = 0.
example (P : LucasSequenceParams) (m : ℕ) :
    lucasU P (m + m) = lucasU P m * lucasV P m := by
  simpa [lucasU] using lucasU_add_eq_mul_lucasV_sub P (m := m) le_rfl

-- With an odd exponent and Q = -1 the correction is added, not subtracted.
example : lucasU fibonacciLucasParams (5 + 3) = 21 := by
  rw [lucasU_add_eq_mul_lucasV_sub fibonacciLucasParams (by decide : 3 ≤ 5)]
  decide

-- A repeated characteristic root is allowed, even with a non-unit Q.
example : lucasU ⟨4, 4, by decide⟩ (4 + 2) = 192 := by
  rw [lucasU_add_eq_mul_lucasV_sub _ (by decide : 2 ≤ 4)]
  decide
