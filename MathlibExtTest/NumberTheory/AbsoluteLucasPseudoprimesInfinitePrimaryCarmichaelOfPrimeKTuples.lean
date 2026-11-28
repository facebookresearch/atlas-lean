/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AbsoluteLucasPseudoprimesInfinitePrimaryCarmichaelOfPrimeKTuples

open MetaMathlibExt

namespace MathlibExtTest.NumberTheory.AbsoluteLucasPseudoprimesInfinitePrimaryCarmichaelOfPrimeKTuples

/-- Assuming the prime k-tuples conjecture as stated in
`MetaMathlibExt.infinite_primary_carmichael_of_primeKTuples`, for every bound `B` there is a
primary Carmichael number `n > B` with exactly three distinct prime factors. -/
theorem exists_primary_carmichael_gt
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite)
    (B : ℕ) :
    ∃ n : ℕ, B < n ∧ 1 < n ∧ ¬ n.Prime ∧
      (∀ a : ℕ, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]) ∧
      n.primeFactors.card = 3 ∧ ∀ p ∈ n.primeFactors, (Nat.digits p n).sum = p := by
  have hinf := infinite_primary_carmichael_of_primeKTuples hk
  have hsub : ¬ {n : ℕ | 1 < n ∧ ¬ n.Prime ∧
      (∀ a : ℕ, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]) ∧
      n.primeFactors.card = 3 ∧ ∀ p ∈ n.primeFactors, (Nat.digits p n).sum = p} ⊆
      ↑(Finset.range (B + 1)) :=
    fun h => hinf (Set.Finite.subset (Finset.finite_toSet _) h)
  rw [Set.not_subset] at hsub
  obtain ⟨n, hnT, hnR⟩ := hsub
  simp only [Set.mem_ofPred_eq] at hnT
  simp only [Finset.mem_coe, Finset.mem_range] at hnR
  have hB : B < n := by omega
  exact ⟨n, hB, hnT.1, hnT.2.1, hnT.2.2.1, hnT.2.2.2.1, hnT.2.2.2.2⟩

end MathlibExtTest.NumberTheory.AbsoluteLucasPseudoprimesInfinitePrimaryCarmichaelOfPrimeKTuples
