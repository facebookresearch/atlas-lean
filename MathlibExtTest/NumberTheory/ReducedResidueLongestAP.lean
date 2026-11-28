/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReducedResidueLongestAP
import Mathlib.Tactic.IntervalCases

open MetaMathlibExt

-- The progression 1, 5 attains the bound for a composite squarefree modulus.
example : longestAPLengthWithDiff 0 6 4 = 2 := by
  apply le_antisymm
  · exact (longestAPLengthWithDiff_le_gpf_sub_one_of_squarefree 0
      (n := 6) (d := 4) (by decide) (by decide) (by decide +kernel)).trans (by decide +kernel)
  · unfold longestAPLengthWithDiff
    refine le_csSup ⟨6, fun s ⟨b, h⟩ => apLength_le (by decide : 0 < 4) h⟩ ?_
    refine ⟨1, fun i hi => ?_⟩
    interval_cases i <;> decide

-- At the smallest allowed modulus a step equal to the modulus leaves only the term -1.
example : longestAPLengthWithDiff (-2) 2 2 = 1 := by
  apply le_antisymm
  · exact (longestAPLengthWithDiff_le_gpf_sub_one_of_squarefree (-2)
      (n := 2) (d := 2) (by decide) (by decide) Nat.squarefree_two).trans (by decide +kernel)
  · unfold longestAPLengthWithDiff
    refine le_csSup ⟨2, fun s ⟨b, h⟩ => apLength_le (by decide : 0 < 2) h⟩ ?_
    refine ⟨-1, fun i hi => ?_⟩
    interval_cases i
    decide

-- The smallest odd prime gives the two terms -1 and 1.
example : absLeastAPLength 6 = 2 :=
  absLeastAPLength_two_mul_prime (p := 3) (by decide) (by decide)

-- At the excluded prime 2, the same two terms already exceed the proposed bound of 1.
example : 1 < absLeastAPLength 4 := by
  change 2 ≤ longestAPLength (-⌈(4 : ℚ) / 2⌉) 4
  rw [show ⌈(4 : ℚ) / 2⌉ = (2 : ℤ) by norm_num]
  unfold longestAPLength
  refine le_csSup ⟨4, fun _ ⟨_, _, hd, h⟩ => apLength_le hd h⟩ ⟨-1, 2, by decide, ?_⟩
  intro i hi
  interval_cases i <;> decide

-- At the smallest prime in this congruence class the centered window consists of -1 and 1.
example : absLeastAPLength 3 = 2 :=
  absLeastAPLength_prime_of_mod_four_eq_three (p := 3) (hp := by decide) (h4 := rfl)

example : longestAPLength (-2) 3 = 2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro s ⟨b, d, hd, h⟩
    by_contra! hs
    have hmem (i : ℕ) (hi : i < s) : b + i * d = -1 ∨ b + i * d = 1 := by
      have hterm := h i hi
      rwa [show reducedResidueWindow (-2) 3 = {-1, 1} by decide +kernel,
        Finset.mem_insert, Finset.mem_singleton] at hterm
    have h0 := hmem 0 (by omega)
    have h1 := hmem 1 (by omega)
    have h2 := hmem 2 hs
    push_cast at h0 h1 h2
    omega
  · exact (isLeast_longestAPLength_prime_of_mod_four_eq_three (p := 3)
      (by decide) rfl).2 ⟨-2, rfl⟩

-- Modulo seven the centered window contains the length-four progression -3, -1, 1, 3.
example : absLeastAPLength 7 = 4 :=
  absLeastAPLength_prime_of_mod_four_eq_three (p := 7) (hp := by decide) (h4 := rfl)

-- Modulo seven the minimum is attained, and the window starting at one exceeds it.
example : (∃ m, longestAPLength m 7 = 4) ∧ 4 < longestAPLength 0 7 := by
  refine ⟨(isLeast_longestAPLength_prime_of_mod_four_eq_three (p := 7) (by decide) rfl).1, ?_⟩
  change 5 ≤ longestAPLength 0 7
  unfold longestAPLength
  refine le_csSup ⟨7, fun _ ⟨_, _, hd, h⟩ => apLength_le hd h⟩ ⟨1, 1, one_pos, ?_⟩
  intro i hi
  interval_cases i <;> decide
