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
import MathlibExt.NumberTheory.Recurrences.GibonacciTripleProductSeed

/-! # Tests for the seed expansion of a triple gibonacci product -/

namespace MetaMathlibExt

private def gib (a b : ℝ) (j : ℤ) : ℝ := a * (Int.fib j : ℝ) + b * (Int.fib (j + 1) : ℝ)

private theorem gib_rec (a b : ℝ) (j : ℤ) : gib a b (j + 2) = gib a b (j + 1) + gib a b j := by
  unfold gib
  rw [show j + 2 + 1 = (j + 1) + 2 by omega, Int.fib_add_two (j + 1), Int.fib_add_two j]
  push_cast
  ring

-- Three distinct seed pairs, with indices `(k, r, s) = (-3, 2, 4)` of mixed sign; no factor
-- vanishes. The theorem rewrites the product side to the seed side, and `norm_num` evaluates
-- the seed side to `90`.
example :
    gib 1 3 (4 + 1) * gib 2 1 (2 + 1) * gib (-1) 2 (-3 + 1) +
        gib 1 3 4 * gib 2 1 2 * gib (-1) 2 (-3) -
        gib 1 3 (4 - 1) * gib 2 1 (2 - 1) * gib (-1) 2 (-3 - 1) = 90 := by
  calc
    _ = gib 1 3 0 * gib 2 1 0 * gib (-1) 2 (-3 + 2 + 4 - 2) +
          (gib 1 3 0 * gib 2 1 1 + gib 1 3 1 * gib 2 1 0) * gib (-1) 2 (-3 + 2 + 4 - 1) +
          gib 1 3 1 * gib 2 1 1 * gib (-1) 2 (-3 + 2 + 4) :=
      (gibonacci_triple_product_seed_identity (gib 1 3) (gib 2 1) (gib (-1) 2)
        (gib_rec 1 3) (gib_rec 2 1) (gib_rec (-1) 2) (-3) 2 4).symm
    _ = 90 := by norm_num [gib, Int.fib]

end MetaMathlibExt
