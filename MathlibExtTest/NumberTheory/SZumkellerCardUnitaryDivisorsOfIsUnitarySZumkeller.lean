/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkellerCardUnitaryDivisorsOfIsUnitarySZumkeller
import MathlibExt.NumberTheory.UnitaryDivisorCount

/-! # Tests for unitary divisor counts of unitary s-Zumkeller numbers -/

namespace MathlibExtTest.NumberTheory.SZumkellerCardUnitaryDivisorsOfIsUnitarySZumkeller

open MetaMathlibExt

-- Sixty is unitary s-Zumkeller with least unitary divisor three and eight unitary divisors.
example : 2 ^ 2 < (Nat.unitaryDivisors 60).card := by
  have hq : IsLeast {d | d ∈ Nat.unitaryDivisors 60 ∧ 1 < d} 3 := by
    constructor
    · show 3 ∈ Nat.unitaryDivisors 60 ∧ 1 < 3
      constructor
      · rw [Nat.mem_unitaryDivisors]
        refine ⟨by decide, by decide, by decide⟩
      · norm_num
    · intro b hb
      simp only [Set.mem_ofPred_eq] at hb
      have hub : Nat.unitaryDivisors 60 = {1, 3, 4, 5, 12, 15, 20, 60} := by decide
      rw [hub] at hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      omega
  exact (card_unitaryDivisors_of_isUnitarySZumkeller 60 3 isUnitarySZumkeller_sixty hq).2.1 rfl

-- A unitary s-Zumkeller number with least unitary divisor three has at least three prime factors.
example (n : ℕ) (h : IsUnitarySZumkeller n)
    (hq : IsLeast {d | d ∈ Nat.unitaryDivisors n ∧ 1 < d} 3) :
    3 ≤ n.primeFactors.card := by
  have hcard := (card_unitaryDivisors_of_isUnitarySZumkeller n 3 h hq).2.1 rfl
  have hn : n ≠ 0 := by
    rintro rfl
    rw [Nat.unitaryDivisors_zero, Finset.card_empty] at hcard
    norm_num at hcard
  rw [card_unitaryDivisors n hn] at hcard
  have h2 : 2 < n.primeFactors.card := by
    by_contra hc
    have hc2 : n.primeFactors.card ≤ 2 := by omega
    have hle : 2 ^ n.primeFactors.card ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hc2
    omega
  omega

end MathlibExtTest.NumberTheory.SZumkellerCardUnitaryDivisorsOfIsUnitarySZumkeller
