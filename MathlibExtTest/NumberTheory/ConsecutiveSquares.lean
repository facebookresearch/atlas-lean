/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConsecutiveSquares

open MetaMathlibExt

-- The 3-4-5 solution has the smallest possible positive denominator.
example : 1 < (2 : ℝ) ∧ (2 : ℝ) < 1 + 2 ^ (1 / 3 : ℝ) + 2 ^ (2 / 3 : ℝ) := by
  convert soCS_ratio_bounds 2 4 5 isSoCSSolution_two_four_five using 1 <;> norm_num

-- A solution with a nonintegral ratio exercises division in ℝ.
example : 1 < (17 / 8 : ℝ) ∧ (17 / 8 : ℝ) < 1 + 2 ^ (1 / 3 : ℝ) + 2 ^ (2 / 3 : ℝ) := by
  have h : IsSoCSSolution 17 34 42 := by norm_num [IsSoCSSolution, SoCSEq]
  convert soCS_ratio_bounds 17 34 42 h using 1 <;> norm_num

-- The singleton set containing the 3-4-5 solution meets the bound for span 3.
example : ({(2, 4, 5)} : Finset (ℤ × ℤ × ℤ)).card ≤ 2 * (3 - 1 : ℤ).toNat := by
  apply soCS_card_le 3 (by norm_num) _
  intro t ht
  rw [Finset.mem_singleton] at ht
  subst ht
  exact ⟨isSoCSSolution_two_four_five, by norm_num⟩

-- The empty set meets the bound for span 2.
example : (∅ : Finset (ℤ × ℤ × ℤ)).card ≤ 2 * (2 - 1 : ℤ).toNat := by
  apply soCS_card_le 2 (by norm_num) _
  intro t ht
  simp at ht

-- Equal endpoints satisfy the polynomial equation and violate the solution inequalities.
example (b : ℤ) : SoCSEq b b b ∧ ¬ IsSoCSSolution b b b := by
  constructor
  · unfold SoCSEq
    ring
  · exact fun h => (lt_irrefl b) h.2.2.1

-- Infinitely many even-span solutions leave one outside every finite set.
example (s : Finset (ℤ × ℤ × ℤ)) :
    ∃ t ∈ {t : ℤ × ℤ × ℤ | IsSoCSSolution t.1 t.2.1 t.2.2 ∧ Even (t.2.2 - t.1)}, t ∉ s :=
  soCS_even_span_infinite.exists_notMem_finset s

-- The solution the even-span family starts from.
example : IsSoCSSolution 59 110 135 ∧ Even ((135 : ℤ) - 59) :=
  ⟨by norm_num [IsSoCSSolution, SoCSEq], by decide⟩
