/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.LuckyCarFactorialMoments

/-! # Tests for the factorial moments and generating polynomial of lucky cars -/

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

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt Polynomial

-- The empty parking function contributes the constant term at n = 0.
example : luckyGenPoly 0 = 1 := by
  have h : Fintype.card {f : Fin 0 → Fin 0 // IsParkingFunction 0 f ∧ luckyCount f = 0} = 1 :=
    by decide
  simp [luckyGenPoly_eq_sum, h]

-- Enumerating the three two-car parking functions gives zero, one and two in the three fibers.
example : luckyGenPoly 2 = X + 2 * X ^ 2 := by
  have h0 : Fintype.card {f : Fin 2 → Fin 2 // IsParkingFunction 2 f ∧ luckyCount f = 0} = 0 :=
    by decide
  have h1 : Fintype.card {f : Fin 2 → Fin 2 // IsParkingFunction 2 f ∧ luckyCount f = 1} = 1 :=
    by decide
  have h2 : Fintype.card {f : Fin 2 → Fin 2 // IsParkingFunction 2 f ∧ luckyCount f = 2} = 2 :=
    by decide
  norm_num [luckyGenPoly_eq_sum, Finset.sum_range_succ, h0, h1, h2]

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted
