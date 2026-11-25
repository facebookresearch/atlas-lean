/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FibonacciCompanionCompositionSum
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace MetaMathlibExt

-- The boundary case has a negative integer power in the Gibonacci prefactor.
example :
    (-1 / 3 : ℚ) ^ (1 : ℕ) * ∑ c : Composition 1,
      ∏ i : Fin c.length, (5 * (c.blocksFun i : ℚ) - 10) = 5 / 3 := by
  rw [← fib_add_three_companion_composition_sum 1 (by decide)]
  norm_num [Nat.fib]

-- At n = 3 there are several compositions, and a part of size two has weight zero.
example :
    (-1 / 3 : ℚ) ^ (3 : ℕ) * ∑ c : Composition 3,
      ∏ i : Fin c.length, (5 * (c.blocksFun i : ℚ) - 10) = 40 / 9 := by
  rw [← fib_add_three_companion_composition_sum 3 (by decide)]
  norm_num [Nat.fib]

end MetaMathlibExt
