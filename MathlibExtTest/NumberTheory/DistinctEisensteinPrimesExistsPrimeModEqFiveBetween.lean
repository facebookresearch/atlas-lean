/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DistinctEisensteinPrimesExistsPrimeModEqFiveBetween

/-!
# Tests of Breusch's theorem for primes congruent to five modulo six

Applications at the lower threshold and at a prime endpoint, and a corollary modulo three.

Source: Elchin Hasanalizade, "Sums of Distinct Eisenstein Primes", *INTEGERS* 24 (2024),
Article A57, Lemma 2 (citing Breusch).
-/

namespace MathlibExtTest.NumberTheory.DistinctEisensteinPrimesExistsPrimeModEqFiveBetween

open MathlibExt.NumberTheory.DistinctEisensteinPrimesWanted

example : Nat.Prime 11 := by
  obtain ⟨p, hp, hlo, hhi, hr⟩ := exists_prime_modEq_five_between 7 (by decide)
  have he : p = 11 := by omega
  simpa [he] using hp

example : Nat.Prime 17 := by
  obtain ⟨p, hp, hlo, hhi, hr⟩ := exists_prime_modEq_five_between 11 (by decide)
  have he : p = 17 := by omega
  simpa [he] using hp

example : ∃ p : ℕ, p.Prime ∧ 100 < p ∧ p < 200 ∧ p % 3 = 2 := by
  obtain ⟨p, hp, hlo, hhi, hr⟩ := exists_prime_modEq_five_between 100 (by decide)
  exact ⟨p, hp, hlo, hhi, by omega⟩

end MathlibExtTest.NumberTheory.DistinctEisensteinPrimesExistsPrimeModEqFiveBetween
