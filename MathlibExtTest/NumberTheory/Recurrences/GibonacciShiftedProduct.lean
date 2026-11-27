/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Int.Fib.Basic
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.GibonacciShiftedProduct

/-! # Tests for the shifted product identity for two gibonacci sequences -/

namespace MetaMathlibExt

private def fibReal (j : ℤ) : ℝ := Int.fib j

private def lucasReal (j : ℤ) : ℝ := 2 * fibReal (j + 1) - fibReal j

private theorem fibReal_rec (j : ℤ) : fibReal (j + 2) = fibReal (j + 1) + fibReal j := by
  simp only [fibReal, Int.fib_add_two, Int.cast_add, add_comm]

private theorem lucasReal_rec (j : ℤ) : lucasReal (j + 2) = lucasReal (j + 1) + lucasReal j := by
  unfold lucasReal
  rw [show j + 2 + 1 = (j + 1) + 2 by omega, fibReal_rec (j + 1), fibReal_rec j]
  ring

-- Fibonacci and Lucas have seeds (0, 1) and (2, 1); at (s, k) = (4, -3) all four
-- products are nonzero and combine to 4 on each side.
example :
    fibReal (-3 + 1) * lucasReal (4 + 1) + fibReal (-3 - 2) * lucasReal (4 - 2) = 4 := by
  calc
    _ = 2 * fibReal (-3) * lucasReal 4 + 2 * fibReal (-3 - 1) * lucasReal (4 - 1) :=
      gibonacci_product_shift_identity fibReal lucasReal fibReal_rec lucasReal_rec (s := 4) (k := -3)
    _ = 4 := by norm_num [fibReal, lucasReal, Int.fib]

end MetaMathlibExt
