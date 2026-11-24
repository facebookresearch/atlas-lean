/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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
