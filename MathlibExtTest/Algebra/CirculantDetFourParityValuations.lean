/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Algebra.CirculantDetFourParityValuations

/-!
# Tests for the powers of two in the four-by-four circulant determinant
-/

namespace MetaMathlibExt

-- All entries even: different and equal parities of the two sums.
example : ∃ t : ℤ, circulantDetFour ![0, -2, 0, 0] = 2 ^ 4 * (2 * t + 1) := by
  have h := (circulantDetFour_two_power_cases 0 (-1) 0 0).1.1 (by decide)
  norm_num at h ⊢
  exact h

example : (2 ^ 8 : ℤ) ∣ circulantDetFour ![6, 2, 0, 0] :=
  (circulantDetFour_two_power_cases 3 1 0 0).1.2 (by decide)

-- All entries odd: different parities, product −1 modulo 4, and equal parities otherwise.
example : ∃ t : ℤ, circulantDetFour ![3, 1, 1, 1] = 2 ^ 4 * (2 * t + 1) :=
  (circulantDetFour_two_power_cases 1 0 0 0).2.1.1 (by decide)

example : ∃ t : ℤ, circulantDetFour ![3, -1, 1, 1] = 2 ^ 7 * (2 * t + 1) := by
  have h := (circulantDetFour_two_power_cases 1 (-1) 0 0).2.1.2.1 (by decide)
  norm_num at h ⊢
  exact h

example : (2 ^ 9 : ℤ) ∣ circulantDetFour ![3, 11, 1, 1] :=
  (circulantDetFour_two_power_cases 1 5 0 0).2.1.2.2 (by decide) (by decide)

example : (2 ^ 9 : ℤ) ∣ circulantDetFour ![5, 1, 1, 1] :=
  (circulantDetFour_two_power_cases 2 0 0 0).2.1.2.2 (by decide) (by decide)

-- Alternating odd entries: both differences odd, then both signs of `w₃ ≡ ±3`.
example : ∃ t : ℤ, circulantDetFour ![2, 3, 0, 1] = 2 ^ 5 * (2 * t + 1) :=
  (circulantDetFour_two_power_cases 1 1 0 0).2.2.1.1 ⟨by decide, by decide⟩

example : ∃ t : ℤ, circulantDetFour ![0, 3, 0, 1] = 2 ^ 6 * (2 * t + 1) :=
  (circulantDetFour_two_power_cases 0 1 0 0).2.2.1.2.1 ⟨by decide, Or.inl (by decide)⟩

example : ∃ t : ℤ, circulantDetFour ![4, 1, 0, 1] = 2 ^ 6 * (2 * t + 1) :=
  (circulantDetFour_two_power_cases 2 0 0 0).2.2.1.2.1 ⟨by decide, Or.inr (by decide)⟩

example : (2 ^ 7 : ℤ) ∣ circulantDetFour ![6, 1, 0, 1] :=
  (circulantDetFour_two_power_cases 3 0 0 0).2.2.1.2.2 (by decide) (by decide)

example : (2 ^ 7 : ℤ) ∣ circulantDetFour ![4, 5, 0, 1] :=
  (circulantDetFour_two_power_cases 2 2 0 0).2.2.1.2.2 (by decide) (by decide)

-- Adjacent odd entries: both signs of `w₄ ≡ ±3`, and both signs of `w₄ ≡ ±1`.
example : ∃ t : ℤ, circulantDetFour ![2, 0, 1, 1] = 2 ^ 4 * (2 * t + 1) :=
  (circulantDetFour_two_power_cases 1 0 0 0).2.2.2.1 (Or.inl (by decide))

example : ∃ t : ℤ, circulantDetFour ![4, 0, 1, 1] = 2 ^ 4 * (2 * t + 1) :=
  (circulantDetFour_two_power_cases 2 0 0 0).2.2.2.1 (Or.inr (by decide))

example : (2 ^ 5 : ℤ) ∣ circulantDetFour ![0, 6, 1, 1] :=
  (circulantDetFour_two_power_cases 0 3 0 0).2.2.2.2 (Or.inr (by decide))

example : (2 ^ 5 : ℤ) ∣ circulantDetFour ![8, 0, 1, 1] :=
  (circulantDetFour_two_power_cases 4 0 0 0).2.2.2.2 (Or.inl (by decide))

end MetaMathlibExt
