/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FinCases
import MathlibExt.NumberTheory.Digits.KaprekarTwoMaximalCycles

/-! # Tests for two Kaprekar cycles of projective-order length -/

open Function MetaMathlibExt

-- The smallest odd base in the theorem has projective order nine.
example : 18 ≤ ((kaprekarFourDigitStates 19).filter fun d =>
    minimalPeriod (kaprekarFourDigitStep 19) d = 9).card := by
  have horder : projectiveOrderTwo 19 = 9 :=
    projectiveOrderTwo_eq_of (by decide) (by decide) (by decide)
  simpa only [horder] using two_mul_projectiveOrderTwo_le_card_kaprekar_cycles 19
    (by decide) (by decide)

-- A composite base attains the shortest projective order allowed by the proof.
example : 10 ≤ ((kaprekarFourDigitStates 33).filter fun d =>
    minimalPeriod (kaprekarFourDigitStep 33) d = 5).card := by
  have horder : projectiveOrderTwo 33 = 5 :=
    projectiveOrderTwo_eq_of (by decide) (by decide) (by decide)
  simpa only [horder] using two_mul_projectiveOrderTwo_le_card_kaprekar_cycles 33
    (by decide) (by decide)

private theorem minimalPeriod_eq_of_check {B p : ℕ} {d : ℕ × ℕ} (hp : 0 < p)
    (hfix : (kaprekarFourDigitStep B)^[p] d = d)
    (hprev : ∀ n : Fin p, n.val ≠ 0 → (kaprekarFourDigitStep B)^[n.val] d ≠ d) :
    minimalPeriod (kaprekarFourDigitStep B) d = p := by
  have hper : IsPeriodicPt (kaprekarFourDigitStep B) p d := hfix
  refine le_antisymm (hper.minimalPeriod_le hp) (le_of_not_gt fun hlt => ?_)
  exact hprev ⟨_, hlt⟩ (hper.minimalPeriod_pos hp).ne' iterate_minimalPeriod

-- Independently check the two constructed orbits in base 33, including disjointness.
example : minimalPeriod (kaprekarFourDigitStep 33) (3, 1) = 5 ∧
    minimalPeriod (kaprekarFourDigitStep 33) (5, 3) = 5 ∧
    ∀ n : Fin 5, (kaprekarFourDigitStep 33)^[n.val] (3, 1) ≠ (5, 3) := by
  refine ⟨minimalPeriod_eq_of_check (by decide) ?_ ?_,
    minimalPeriod_eq_of_check (by decide) ?_ ?_, ?_⟩
  all_goals
    (try (intro n; fin_cases n)) <;>
      simp [iterate_succ_apply', kaprekarFourDigitStep, List.insertionSort_cons,
        List.orderedInsert_cons]

-- At the excluded base 17, the distance-two pair is antipodal and has half the order.
example : minimalPeriod (kaprekarFourDigitStep 17) (5, 3) = 2 := by
  refine minimalPeriod_eq_of_check (by decide) ?_ ?_
  all_goals
    (try (intro n; fin_cases n)) <;>
      simp [iterate_succ_apply', kaprekarFourDigitStep, List.insertionSort_cons,
        List.orderedInsert_cons]
