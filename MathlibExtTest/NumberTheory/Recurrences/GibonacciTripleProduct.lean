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
import MathlibExt.NumberTheory.Recurrences.GibonacciTripleProduct

/-! # Tests for the product recurrence for three gibonacci sequences -/

namespace MetaMathlibExt

private def gib (a b : ℝ) (j : ℤ) : ℝ := a * (Int.fib j : ℝ) + b * (Int.fib (j + 1) : ℝ)

private theorem gib_rec (a b : ℝ) (j : ℤ) : gib a b (j + 2) = gib a b (j + 1) + gib a b j := by
  unfold gib
  rw [show j + 2 + 1 = (j + 1) + 2 by omega, Int.fib_add_two (j + 1), Int.fib_add_two j]
  push_cast
  ring

-- The three seed pairs are distinct and the indices (-4, 2, 5) give nonzero products at every step.
example :
    93 = 3 * gib 1 1 (-4) * gib 3 (-1) 2 * gib (-1) 3 5 +
        6 * gib 1 1 (-4 - 1) * gib 3 (-1) (2 - 1) * gib (-1) 3 (5 - 1) -
        3 * gib 1 1 (-4 - 2) * gib 3 (-1) (2 - 2) * gib (-1) 3 (5 - 2) -
        gib 1 1 (-4 - 3) * gib 3 (-1) (2 - 3) * gib (-1) 3 (5 - 3) := by
  calc
    (93 : ℝ) = gib 1 1 (-4 + 1) * gib 3 (-1) (2 + 1) * gib (-1) 3 (5 + 1) := by
      norm_num [gib, Int.fib]
    _ = _ := gibonacci_triple_product_recurrence (gib 1 1) (gib 3 (-1)) (gib (-1) 3)
      (gib_rec 1 1) (gib_rec 3 (-1)) (gib_rec (-1) 3) (-4) 2 5

end MetaMathlibExt
