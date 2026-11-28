/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReducedResidueLongestAPLongestAPLengthMinOfNotSquarefreeOfNotIsPrimePow
import Mathlib.RingTheory.Radical.NatInt

/-! # Tests for `ReducedResidueLongestAPLongestAPLengthMinOfNotSquarefreeOfNotIsPrimePow` -/

namespace MathlibExtTest.NumberTheory.ReducedResidueLongestAPLongestAPLengthMinOfNotSquarefreeOfNotIsPrimePow

open MetaMathlibExt UniqueFactorizationMonoid

-- Modulo 12 the radical quotient and the prime-factor bound are both 2.
example : IsLeast (Set.range fun m : ℤ => longestAPLength m 12) 2 := by
  have hr : radical 12 = 6 := by rw [Nat.radical_eq_prod_primeFactors]; decide +kernel
  have hq : 12 / radical 12 = 2 := by rw [hr]
  have hle : (12 : ℕ).primeFactors.sup id - 1 ≤ 12 / radical 12 := by rw [hr]; decide +kernel
  obtain ⟨⟨_, _⟩, his⟩ := longestAPLength_min_of_not_squarefree_of_not_isPrimePow (n := 12)
    (by decide) (by decide +kernel) (by decide)
  have hleast := his hle
  rw [hq] at hleast
  exact hleast

-- Every window modulo 12 attains at least the radical quotient.
example (m : ℤ) : 2 ≤ longestAPLength m 12 := by
  have hr : radical 12 = 6 := by rw [Nat.radical_eq_prod_primeFactors]; decide +kernel
  have hq : 12 / radical 12 = 2 := by rw [hr]
  obtain ⟨⟨hlb, _⟩, _⟩ := longestAPLength_min_of_not_squarefree_of_not_isPrimePow (n := 12)
    (by decide) (by decide +kernel) (by decide)
  simpa [hq] using hlb m

-- Some window modulo 12 attains at most the maximum of the two bounds.
example : ∃ m : ℤ, longestAPLength m 12 ≤ 2 := by
  have hr : radical 12 = 6 := by rw [Nat.radical_eq_prod_primeFactors]; decide +kernel
  have hq : 12 / radical 12 = 2 := by rw [hr]
  have hle : (12 : ℕ).primeFactors.sup id - 1 ≤ 12 / radical 12 := by rw [hr]; decide +kernel
  obtain ⟨⟨_, hex⟩, _⟩ := longestAPLength_min_of_not_squarefree_of_not_isPrimePow (n := 12)
    (by decide) (by decide +kernel) (by decide)
  obtain ⟨m, hm⟩ := hex
  have hmax : max (12 / radical 12) ((12 : ℕ).primeFactors.sup id - 1) = 2 := by
    rw [max_eq_left hle, hq]
  rw [hmax] at hm
  exact ⟨m, hm⟩

end MathlibExtTest.NumberTheory.ReducedResidueLongestAPLongestAPLengthMinOfNotSquarefreeOfNotIsPrimePow
