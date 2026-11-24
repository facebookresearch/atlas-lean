/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasRecurrenceShift

namespace MetaMathlibExt.lucas_recurrence_add_modEq_of_dvd_lucasU.Tests

-- The shift by five scales the companion sequence by eight, also for a negative modulus.
example (n : ℕ) : lucasV fibonacciLucasParams (n + 5) ≡
    8 * lucasV fibonacciLucasParams n [ZMOD -5] :=
  lucas_recurrence_add_modEq_of_dvd_lucasU fibonacciLucasParams (lucasV fibonacciLucasParams)
    (fun _ => rfl) 5 (-5) (by decide) (by decide) n

-- For P = 0 and Q = 1, U₆ = 0 and U₇ = -1, so the shift gives equality modulo zero.
private def params : LucasSequenceParams := ⟨0, 1, by decide⟩

example (W : ℕ → ℤ) (hW : ∀ n, W (n + 2) = -W n) (n : ℕ) : W (n + 6) = -W n := by
  have h := lucas_recurrence_add_modEq_of_dvd_lucasU params W
    (by simpa [params] using hW) 6 0 (by decide) (by decide) n
  simpa only [Int.modEq_zero_iff, show lucasU params (6 + 1) = -1 by decide, neg_one_mul] using h

end MetaMathlibExt.lucas_recurrence_add_modEq_of_dvd_lucasU.Tests
