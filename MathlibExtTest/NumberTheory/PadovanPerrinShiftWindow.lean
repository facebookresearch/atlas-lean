/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PadovanPerrinShiftWindow

open MetaMathlibExt

-- A window starting at 2, with different shifts, gives the first value after it and later values.
example {v w : ℕ → ℤ} (hv : (padovanPerrinRecurrence 1 1 1 2).IsSolution v)
    (hw : (padovanPerrinRecurrence 1 1 1 2).IsSolution w)
    (h₂ : v 3 = w 6) (h₃ : v 4 = w 7) (h₄ : v 5 = w 8) :
    v 6 = w 9 ∧ v 11 = w 14 := by
  have htail := padovanPerrin_shift_eq_of_window 1 1 1 2 hv hw 1 4 2 (by
    intro j hj hj'
    have hj'' : j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hj'' with rfl | rfl | rfl
    · exact h₂
    · exact h₃
    · exact h₄)
  exact ⟨htail 5 (by decide), htail 10 (by decide)⟩

-- At s = 0 and p = 1, only one value is needed even though the two-term formula does not apply.
example {v w : ℕ → ℤ} (hv : (padovanPerrinRecurrence 2 1 1 0).IsSolution v)
    (hw : (padovanPerrinRecurrence 2 1 1 0).IsSolution w) (h : v 3 = w 5) :
    v 8 = w 10 := by
  refine padovanPerrin_shift_eq_of_window 2 1 1 0 hv hw 0 2 3 ?_ 8 (by decide)
  intro j hj hj'
  obtain rfl : j = 3 := by omega
  exact h

-- At order zero the window is empty and the conclusion holds at its starting index.
example {v w : ℕ → ℤ} (hv : (padovanPerrinRecurrence 2 3 0 0).IsSolution v)
    (hw : (padovanPerrinRecurrence 2 3 0 0).IsSolution w) : v 6 = w 9 := by
  refine padovanPerrin_shift_eq_of_window 2 3 0 0 hv hw 2 5 4 ?_ 4 le_rfl
  intro j hj hj'
  omega
