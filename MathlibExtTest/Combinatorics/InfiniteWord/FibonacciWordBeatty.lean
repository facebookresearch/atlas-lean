/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InfiniteWord.FibonacciWordBeatty
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.FibonacciWordBeattyTests

open scoped goldenRatio

-- The first Fibonacci letter is a zero, and the second is not.
example : ∃ m : ℤ, (1 : ℤ) = ⌊m * φ⌋ :=
  (fibonacciWord_beatty_properties.1 1 (by decide)).mp (by decide)

example (m : ℤ) : (2 : ℤ) ≠ ⌊m * φ⌋ := fun h ↦
  (by decide : fibInf (2 - 1) ≠ false)
    ((fibonacciWord_beatty_properties.1 2 (by decide)).mpr ⟨m, h⟩)

-- The gap at −3 tests the two-sided integer claim, independent of word indexing.
example : (∃ m : ℤ, (-2 : ℤ) = ⌊m * φ⌋) ∧ ∃ m : ℤ, (-4 : ℤ) = ⌊m * φ⌋ := by
  apply fibonacciWord_beatty_properties.2.1 (-3)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Int.floor_eq_iff.mp hm.symm
  norm_num at hlo hhi
  by_cases h : m ≤ -2
  · have hφ : (3 : ℝ) / 2 < φ := by
      have hs : (2 : ℝ) < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
      unfold Real.goldenRatio
      linarith
    have hm' : (m : ℝ) ≤ -2 := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_right hm' Real.goldenRatio_pos.le
    linarith
  · have hm' : (-1 : ℝ) ≤ m := by exact_mod_cast (show -1 ≤ m by omega)
    have := mul_le_mul_of_nonneg_right hm' Real.goldenRatio_pos.le
    linarith [Real.goldenRatio_lt_two]

-- An even zero of S gives membership at n/2; an odd zero gives nonmembership at (n+1)/2.
example : ∃ m : ℤ, (1 : ℤ) = ⌊m * φ⌋ := by
  rcases (fibonacciWord_beatty_properties.2.2.1 2 (by decide)).mp (by decide) with h | h
  · exact h.2
  · exact ((by decide : ¬ Odd 2) h.1).elim

example (m : ℤ) : (2 : ℤ) ≠ ⌊m * φ⌋ := by
  rcases (fibonacciWord_beatty_properties.2.2.1 3 (by decide)).mp (by decide) with h | h
  · exact ((by decide : ¬ Even 3) h.1).elim
  · exact h.2 m

-- The fourth letter of T is one, while the second is zero.
example : ∃ m : ℤ, (4 : ℤ) = 2 * ⌊m * φ⌋ - m :=
  (fibonacciWord_beatty_properties.2.2.2 4 (by decide)).mp (by decide)

example (m : ℤ) : (2 : ℤ) ≠ 2 * ⌊m * φ⌋ - m := fun h ↦
  (by decide : wesleyWordT (2 - 1) ≠ true)
    ((fibonacciWord_beatty_properties.2.2.2 2 (by decide)).mpr ⟨m, h⟩)

end MetaMathlibExt.FibonacciWordBeattyTests
