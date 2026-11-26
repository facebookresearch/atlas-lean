/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ExtendedContinuantExtendedContinuantBennettNat

/-!
# Tests for Bennett's continuant identity

These tests derive a left-end recurrence and evaluate a continuant using Bennett's identity.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 2 (after G. T. Bennett, 1939).
-/

namespace MathlibExtTest.NumberTheory.ExtendedContinuantExtendedContinuantBennettNat

open MetaMathlibExt

example (x : ℤ → ℤ) (n : ℕ) :
    extendedContinuant x ((n : ℤ) - 2) 0 =
      x 0 * extendedContinuant x ((n : ℤ) - 3) 1 +
        extendedContinuant x ((n : ℤ) - 4) 2 := by
  have h := extendedContinuant_bennett_nat x 0 1 2 n
  norm_num [Int.negOnePow_odd 3 ⟨1, rfl⟩, Int.negOnePow_even 2 ⟨1, rfl⟩,
    extendedContinuant_neg_one, (extendedContinuant_neg_three_to_six x 2).2.1] at h
  ring_nf at h ⊢
  linear_combination -h

example : extendedContinuant id 3 0 = 7 := by
  have h := extendedContinuant_bennett_nat id 0 1 2 5
  norm_num [Int.negOnePow_odd 3 ⟨1, rfl⟩, Int.negOnePow_even 2 ⟨1, rfl⟩,
    extendedContinuant_neg_one, (extendedContinuant_neg_three_to_six id 2).2.1] at h
  have h₁ : extendedContinuant id 1 2 = 7 := by decide
  rw [h₁] at h
  linear_combination -h

end MathlibExtTest.NumberTheory.ExtendedContinuantExtendedContinuantBennettNat
