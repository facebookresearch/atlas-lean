/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.LuckyCarFactorialMoments

/-! # Tests for the factorial moments of lucky cars -/

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted.expected_descFactorial_luckyCount

open MetaMathlibExt Polynomial

private def twoCarMomentNumerator (ℓ : ℕ) : ℕ :=
  ∑ f ∈ Finset.univ.filter (fun f : Fin 2 → Fin 2 => IsParkingFunction 2 f),
    (luckyCount f).descFactorial ℓ

private theorem evaluatedMoment (ℓ : ℕ) :
    (derivative^[ℓ] (luckyGenPoly 2)).eval 1 / ((↑(2 : ℕ) : ℚ) + 1) ^ (2 - 1) =
      (twoCarMomentNumerator ℓ : ℚ) / 3 := by
  rw [← expected_descFactorial_luckyCount 2 ℓ (hn := by decide),
    twoCarMomentNumerator, Nat.cast_sum]
  norm_num

-- The zeroth moment is one.
example : (derivative^[0] (luckyGenPoly 2)).eval 1 / ((↑(2 : ℕ) : ℚ) + 1) ^ (2 - 1) = 1 := by
  rw [evaluatedMoment, show twoCarMomentNumerator 0 = 3 by decide]
  norm_num

-- Of the three parking functions, two have two lucky cars and one has one.
example : (derivative^[2] (luckyGenPoly 2)).eval 1 / ((↑(2 : ℕ) : ℚ) + 1) ^ (2 - 1) = 4 / 3 := by
  rw [evaluatedMoment, show twoCarMomentNumerator 2 = 4 by decide]
  norm_num

-- Moments above the number of cars vanish.
example : (derivative^[3] (luckyGenPoly 2)).eval 1 / ((↑(2 : ℕ) : ℚ) + 1) ^ (2 - 1) = 0 := by
  rw [evaluatedMoment, show twoCarMomentNumerator 3 = 0 by decide]
  norm_num

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted.expected_descFactorial_luckyCount
