/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ExtendedContinuant

/-! # Tests for extended continuants and the westbound matrix product -/

open MetaMathlibExt

-- A forward continuant at a nonzero start index uses both consecutive terms.
example : extendedContinuant id 1 2 = 7 := by decide

-- The smallest product consists of the single factor at index -1.
example (x : ℤ → ℤ) :
    !![extendedContinuant x (-2) 0, extendedContinuant x (-3) 1;
       extendedContinuant x (-3) 0, extendedContinuant x (-4) 1] =
      !![0, 1; 1, -x (-1)] := by
  simpa [List.ofFn_succ] using (extendedContinuant_westbound_matrix_prod x 1 (by decide)).symm

-- Distinct off-diagonal entries detect a reversal of the two factors.
example :
    !![extendedContinuant id (-3) 0, extendedContinuant id (-4) 1;
       extendedContinuant id (-4) 0, extendedContinuant id (-5) 1] =
      !![1, 1; 2, 3] :=
  (extendedContinuant_westbound_matrix_prod id 2 (by decide)).symm.trans (by decide)

-- Reflecting order 2 crosses to the backward branch and shifts the start four places.
example (x : ℤ → ℤ) (h : ℤ) :
    extendedContinuant x 2 h = -extendedContinuant x (-6) (h + 4) := by
  simpa [add_assoc] using extendedContinuant_neg_order x h (-2)

-- Reflecting order -7 gives the forward continuant on the terms 3, 4, 5, 6.
example : extendedContinuant id (-7) 8 = 421 :=
  (extendedContinuant_neg_order id 8 7).trans (by decide)

-- At order -4 every factor lies on the backward branch, and the sign is (-1)^(-3) = -1.
example (x : ℤ → ℤ) :
    extendedContinuant x (-4) 0 * extendedContinuant x (-6) 1 -
      extendedContinuant x (-5) 1 * extendedContinuant x (-5) 0 = -1 := by
  simpa [Int.negOnePow_odd 3 ⟨1, rfl⟩] using extendedContinuant_det x (-4)

-- Every raw convergent K_n(x)_0 / K_{n-1}(x)_1 is in lowest terms, also for negative orders.
example (x : ℤ → ℤ) (n : ℤ) :
    IsCoprime (extendedContinuant x n 0) (extendedContinuant x (n - 1) 1) :=
  ⟨((n + 1).negOnePow : ℤ) * extendedContinuant x (n - 2) 1,
    -((n + 1).negOnePow : ℤ) * extendedContinuant x (n - 1) 0, by
      linear_combination ((n + 1).negOnePow : ℤ) * extendedContinuant_det x n +
        Int.units_coe_mul_self (n + 1).negOnePow⟩

-- At shift two, the first pair can agree: for x = id and z₀ = 1 it is (1, 1).
-- The theorem then forces a mismatch at a positive index.
example (z : ℤ → ℤ) (hz : z 0 = 1) :
    ¬ ∀ i : ℕ, 0 < i →
      extendedContinuant id (-(i : ℤ) - 2 - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant id (-(i : ℤ) - 2 - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1 := by
  intro h
  apply not_silent_of_even id z 2 (by decide)
  intro i
  cases i with
  | zero =>
    change extendedContinuant id (-3) 0 = extendedContinuant z 0 0 ∧
      extendedContinuant id (-4) 1 = extendedContinuant z (-1) 1
    rw [extendedContinuant_zero, extendedContinuant_neg_one, hz]
    decide
  | succ i => exact h (i + 1) (Nat.succ_pos i)

namespace MetaMathlibExt.silentTerms_table_five_mod_six

private def tableSequence (i : ℤ) : ℤ :=
  if i ≤ -4 then (if (-i) % 3 = 2 then -1 else 1)
  else if i = -3 then 4 else if i = -2 then 1 else if i = -1 then -1 else 3

-- At the first admissible order, c₁ = 1 and c₂ = 0 give a zero numerator.
example :
    -1 + extendedContinuant tableSequence 5 (-7) +
      3 * extendedContinuant tableSequence 6 (-7) = 0 := by
  have h := silentTerms_table_five_mod_six tableSequence 11 (by decide) (by decide)
    1 0 (by decide) (by decide) (by decide) (by decide) (by
      intro m hm _
      simp [tableSequence, show -m ≤ -4 by omega])
  have hnum := h.2
  norm_num [show tableSequence 0 = 3 by decide] at hnum
  exact hnum

-- One six-term block later the denominator is still -1.
example :
    -extendedContinuant tableSequence 12 (-14) - 3 * extendedContinuant tableSequence 13 (-14) =
      -1 := by decide

end MetaMathlibExt.silentTerms_table_five_mod_six

namespace MetaMathlibExt.threeSilent_terms

private def quadratic (i : ℤ) : ℤ := (i + 1) * (i + 2)

-- The first westbound numerator vanishes. The next term is recovered from the denominator.
example (y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant quadratic i 0 = extendedContinuant y i 0 ∧
      extendedContinuant quadratic ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant quadratic (-(i : ℤ) - 4) 0 = extendedContinuant z i 0 ∧
      extendedContinuant quadratic (-(i : ℤ) - 5) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    y 0 = 2 ∧ z 0 = 0 ∧ z 1 = -2 := by
  obtain ⟨he, hw⟩ := threeSilent_terms quadratic y z heast hwest (by decide)
  have h₂ := hw 2 (by decide)
  have h₃ := hw 3 (by decide)
  norm_num [quadratic] at h₂ h₃
  exact ⟨(he 0).symm, by omega, by omega⟩

end MetaMathlibExt.threeSilent_terms
