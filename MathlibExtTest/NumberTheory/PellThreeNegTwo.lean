/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellThreeNegTwo

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

-- The conjugate-unit step backwards from the seed gives (−1, 1), outside the positive orbit.
example : ¬ ∃ k : ℕ, (⟨-1, 1⟩ : ℤ√3) = ⟨1, 1⟩ * (⟨2, 1⟩ : ℤ√3) ^ k := by
  intro h
  have hx := ((pell_three_eq_neg_two_positive_solutions_iff_and_recurrence.1 (-1) 1).2 h).1
  omega

-- Apply both recurrences at index zero to recover the first pair after the initial values.
example : (⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ 2 = ⟨19, 11⟩ := by
  obtain ⟨⟨hx₀, hy₀, hx₁, hy₁⟩, hrec⟩ :=
    pell_three_eq_neg_two_positive_solutions_iff_and_recurrence.2
  obtain ⟨hx₂, hy₂⟩ := hrec 0
  rw [hx₁, hx₀] at hx₂
  rw [hy₁, hy₀] at hy₂
  exact Zsqrtd.ext hx₂ hy₂

end MathlibExt.NumberTheory.PowerfulNumbersWanted
