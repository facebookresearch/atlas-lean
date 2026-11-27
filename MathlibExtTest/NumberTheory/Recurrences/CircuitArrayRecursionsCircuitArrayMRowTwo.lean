/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.CircuitArrayRecursionsCircuitArrayMRowTwo
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathlibExtTest.NumberTheory.Recurrences.CircuitArrayRecursionsCircuitArrayMRowTwo

open MetaMathlibExt

-- Row two at `s = 3`, with the coefficients evaluated.
example : circuitArrayM 2 3 = (9 * circuitVar 1 ^ 2 * circuitVar 2 + 8 * circuitVar 1 ^ 2 +
    36 * circuitVar 1 * circuitVar 2 + 128 * circuitVar 1 + 36 * circuitVar 2 + 512) /
    (26 + circuitVar 1) ^ 2 := by
  rw [(circuitArrayM_row_two).1 3 (by decide)]
  norm_num

-- Row two at `s = 2` recovers the boundary variable `X_2`.
example : circuitArrayM 2 2 = circuitVar 2 := by
  rw [(circuitArrayM_row_two).1 2 le_rfl]
  have hD0 : (3 : FractionRing (MvPolynomial ℕ ℚ)) * 9 ^ ((2:ℕ) - 2) - 1 + circuitVar 1 ≠ 0 := by
    have e : ((2:ℕ) - 2) = 0 := by omega
    rw [e]
    have hns : (1 : FractionRing (MvPolynomial ℕ ℚ)) - circuitVar 1 ≠ 3 * 9 ^ (0:ℕ) := by
      intro hcon
      have hp : 1 - MvPolynomial.X 1 = (3 : MvPolynomial ℕ ℚ) * 9 ^ (0:ℕ) := by
        apply IsFractionRing.injective (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ))
        simpa only [map_sub, map_one, map_mul, map_ofNat, map_pow, circuitVar] using hcon
      have he := congrArg (MvPolynomial.eval (fun _ => (1 : ℚ))) hp
      simp at he
    intro hcon
    apply hns
    linear_combination -hcon
  rw [div_eq_iff (pow_ne_zero 2 hD0)]
  norm_num
  ring

end MathlibExtTest.NumberTheory.Recurrences.CircuitArrayRecursionsCircuitArrayMRowTwo
