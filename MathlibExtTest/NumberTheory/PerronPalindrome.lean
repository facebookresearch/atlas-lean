/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.Rat
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.PerronPalindrome

/-! # Tests for Perron's lemma -/

namespace MetaMathlibExt.exists_palindrome_continuedFraction_div

-- At the smallest admissible prime the zero fold rules out the empty palindrome.
example : ∃ qs : List ℕ, 2 ≤ qs.length ∧ qs.reverse = qs ∧
    (5 / 2 : ℚ) = qs.foldr (fun a acc => (a : ℚ) + acc⁻¹) 0 := by
  obtain ⟨qs, ⟨n, hn⟩, hpal, _, hval⟩ :=
    exists_palindrome_continuedFraction_div (p := 5) (x₀ := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨qs, ?_, hpal, hval⟩
  cases qs with
  | nil => norm_num [List.bind_eq_flatMap, List.pure_def] at hval
  | cons q qs => simp only [List.length_cons] at hn ⊢; omega

-- A longer expansion can have internal coefficients equal to one.
example : let qs : List ℕ := [2, 1, 1, 2]
    qs.reverse = qs ∧ (13 / 5 : ℚ) = qs.foldr (fun a acc => (a : ℚ) + acc⁻¹) 0 := by
  norm_num [List.bind_eq_flatMap, List.pure_def, List.reverse_cons]

end MetaMathlibExt.exists_palindrome_continuedFraction_div
