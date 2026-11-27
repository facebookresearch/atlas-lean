/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable.BaseShift

/-! # Tests for shifts of the base in long division -/

open MetaMathlibExt

-- For the improper fraction 8/6, the second digits in bases 2 and 8 are 1 and 5.
-- These two digits determine the slope for every base 2 + 6t.
example (t : ℕ) : 8 * (2 + t * 6) ^ 2 / 6 % (2 + t * 6) = 1 + t * 4 := by
  obtain ⟨c, _, h⟩ := digit_add_mul_modulus_eq 8 6 2 1 (by decide) (by decide)
  have h₁ := h 1
  change 5 = 1 + 1 * c at h₁
  have hc : c = 4 := by omega
  subst c
  exact h t

-- At modulus one the bound on the slope forces every shift to preserve the digit.
example (m b j t : ℕ) (hb : 2 ≤ b) :
    m * (b + t) ^ (j + 1) % (b + t) = m * b ^ (j + 1) % b := by
  obtain ⟨c, hc, h⟩ := digit_add_mul_modulus_eq m 1 b j (by decide) hb
  have hzero : c = 0 := by omega
  simpa [hzero] using h t
