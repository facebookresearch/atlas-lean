/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Digits.BergmanWordFib

/-!
# Tests for the Bergman expansions of the Fibonacci numbers
-/

open scoped goldenRatio

namespace MetaMathlibExt

-- The Bergman expansion of $F_2 = 1$ is $\{0\}$, of the form $\{t\}$ with $t = 0$.
example : ∃ t : ℤ, ({0} : Finset ℤ) =
    (Finset.range 1).image fun j : ℕ => 4 * (j : ℤ) + t := by
  obtain ⟨t, ht⟩ := (bergmanWord_fib 1 le_rfl).1 {0} (by unfold IsBergmanExpansion; decide)
    (by simpa using basePhiValue_singleton_zero)
  exact ⟨t, ht⟩

-- The Bergman expansion of $F_3 = 2$ is {1, -2}, of the form {t, t + 3}.
example : ∃ t : ℤ, ({1, -2} : Finset ℤ) =
    insert t ((Finset.range 1).image fun j : ℕ => 4 * (j : ℤ) + 3 + t) := by
  obtain ⟨t, ht⟩ := (bergmanWord_fib 1 le_rfl).2 {1, -2} isBergmanExpansion_one_neg_two
    (by rw [basePhiValue_one_neg_two]; norm_num)
  exact ⟨t, ht⟩

-- The Bergman expansion of $F_4 = 3$ is $\{-2, 2\}$, of the form $\{t, t + 4\}$.
example : ∃ t : ℤ, ({-2, 2} : Finset ℤ) =
    (Finset.range 2).image fun j : ℕ => 4 * (j : ℤ) + t := by
  have h1 : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
  have hinv : φ ^ (-2 : ℤ) = 2 - φ := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat, ← inv_pow, h1]
    linear_combination Real.goldenRatio_sq
  have hval : basePhiValue ({-2, 2} : Finset ℤ) = 3 := by
    rw [basePhiValue, Finset.sum_insert (by decide), Finset.sum_singleton, zpow_ofNat, hinv]
    linear_combination Real.goldenRatio_sq
  obtain ⟨t, ht⟩ := (bergmanWord_fib 2 (by norm_num)).1 {-2, 2}
    (by unfold IsBergmanExpansion; decide)
    (by rw [show Nat.fib (2 * 2) = 3 from rfl]; exact hval)
  exact ⟨t, ht⟩

end MetaMathlibExt
