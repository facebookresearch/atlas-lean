/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellThreeOne

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

-- The zeroth power has norm one, but its second coordinate is zero.
example : ¬ ∃ k : ℕ, 1 ≤ k ∧ (⟨1, 0⟩ : ℤ√3) = (⟨2, 1⟩ : ℤ√3) ^ k := by
  intro h
  have hy := ((pell_three_eq_one_positive_solutions_iff_and_recurrence.1 1 0).2 h).2.1
  exact (lt_irrefl (0 : ℤ)) hy

-- Both recurrences at index one give the next positive solution after (7, 4).
example : (⟨2, 1⟩ : ℤ√3) ^ 3 = ⟨26, 15⟩ := by
  obtain ⟨hx₁, hy₁, hx₂, hy₂, hrec⟩ := pell_three_eq_one_positive_solutions_iff_and_recurrence.2
  obtain ⟨hx₃, hy₃⟩ := hrec 1
  rw [hx₂, hx₁] at hx₃
  rw [hy₂, hy₁] at hy₃
  exact Zsqrtd.ext hx₃ hy₃

end MathlibExt.NumberTheory.PowerfulNumbersWanted
