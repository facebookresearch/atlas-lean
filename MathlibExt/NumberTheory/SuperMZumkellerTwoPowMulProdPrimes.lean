/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SuperMZumkeller
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.SuperMZumkellerFactorization

/-!
# Super-m-Zumkeller numbers from powers of two and distinct odd primes

For a natural exponent `k` and a finite set `s` of at least three odd primes,
`2^k * ∏ p ∈ s, p` is super-m-Zumkeller. The divisor count is `(k + 1) * 2^s.card`,
including when `k = 0`. Its divisibility by eight gives the result by the factorization criterion.

## References

* Harish Patodia, *Super-m-Zumkeller Numbers*, INTEGERS 26 (2026), Article A79,
  pp. 1–9, Theorem 2 and Corollary 2(ii)
  (<https://math.colgate.edu/~integers/aa79/aa79.pdf>).
* David M. Burton, *Elementary Number Theory*, 7th ed., McGraw-Hill, 2011,
  §6.1, Theorem 6.2(a), p. 105 (the divisor count from the prime factorization).
  Patodia cites the McGraw Hill Education (India) edition of 2012 in Lemma 1.
-/

namespace MathlibExt.NumberTheory.SuperMZumkellerWanted

open ArithmeticFunction

/-- **Powers of $2$ times at least three distinct odd primes are super-m-Zumkeller.** Let $k$ be
a natural number and $S$ a finite set of at least three odd primes. Then $2^k \prod_{p \in S} p$
is super-m-Zumkeller.

The primes are required to be odd because the paper's proof uses that this number has
$(k+1)2^r$ divisors, where $r$ is the number of primes in $S$.

Source: Harish Patodia, "Super-m-Zumkeller Numbers",
Corollary 2(ii). -/
public theorem isSuperMZumkeller_two_pow_mul_prod_primes (k : ℕ)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hs2 : 2 ∉ s)
    (hcard : 3 ≤ s.card) :
    IsSuperMZumkeller ((2 : ℕ) ^ k * ∏ p ∈ s, p) := by
  have hcop : ((2 : ℕ) ^ k).Coprime (∏ p ∈ s, p) := by
    apply Nat.Coprime.pow_left k
    exact Nat.Coprime.prod_right fun p hp ↦
      (Nat.coprime_primes Nat.prime_two (hs p hp)).2 fun h ↦ hs2 (h.symm ▸ hp)
  have hcount : ((2 : ℕ) ^ k * ∏ p ∈ s, p).divisors.card = (k + 1) * 2 ^ s.card := by
    have hprime (p : ℕ) (hp : p ∈ s) : sigma 0 p = 2 := by
      simpa only [pow_one] using sigma_zero_apply_prime_pow (i := 1) (hs p hp)
    rw [← sigma_zero_apply, isMultiplicative_sigma.map_mul_of_coprime hcop,
      sigma_zero_apply_prime_pow Nat.prime_two, isMultiplicative_sigma.map_prod_of_prime s hs,
      Finset.prod_congr rfl hprime, Finset.prod_const]
  have hdvd : 8 ∣ ((2 : ℕ) ^ k * ∏ p ∈ s, p).divisors.card := by
    rw [hcount]
    exact dvd_mul_of_dvd_right (pow_dvd_pow (2 : ℕ) hcard) _
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hpos : 0 < (2 : ℕ) ^ k * ∏ q ∈ s, q :=
    Nat.mul_pos (pow_pos (by decide) _) (Finset.prod_pos fun q hq ↦ (hs q hq).pos)
  have hn : 2 ≤ (2 : ℕ) ^ k * ∏ q ∈ s, q :=
    (hs p hp).two_le.trans (Nat.le_of_dvd hpos
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun q ↦ q) hp) _))
  exact (isSuperMZumkeller_iff _ hn).2 fun p _ ↦
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdvd _) _

end MathlibExt.NumberTheory.SuperMZumkellerWanted
