/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The power of two in an even primitive non-deficient number

For each odd prime divisor `p` of such a number, the proper divisor obtained by multiplying
`p` by half the full power of two is deficient. Its divisor sum bounds that power of two by `p`.
-/

public section

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

private lemma sum_divisors_two_pow_add_one (k : ℕ) :
    (∑ d ∈ (2 ^ k).divisors, d) + 1 = 2 * 2 ^ k := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two, ← pow_succ']
  simpa using geom_sum_mul_add (1 : ℕ) (k + 1)

/-- **The power of 2 in an even primitive non-deficient number is below its radical.** Let $n$
be an even primitive non-deficient number, that is, a positive integer with $\sigma(n) \ge 2n$
all of whose proper divisors $m$ satisfy $\sigma(m) < 2m$, where $\sigma$ is the sum of divisors.
If $2^a$ is the largest power of $2$ dividing $n$ and $R$ is the product of the distinct primes
dividing $n$, then $2^{a+1} < R$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Proposition
(label `evenprimitivenondeficientshaveatightbound`). -/
theorem two_pow_factorization_add_one_lt_radical
    (n : ℕ) (hne : Even n)
    (hn : IsPrimitiveNondeficient n) :
    2 ^ (n.factorization 2 + 1) < ∏ q ∈ n.primeFactors, q := by
  obtain ⟨⟨hn0, hsum⟩, hproper⟩ := hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.prime_two.factorization_pos_of_dvd hn0 hne.two_dvd).ne'
  change n.factorization 2 = k + 1 at hk
  let m := ordCompl[2] n
  have hm : 0 < m := Nat.ordCompl_pos 2 hn0
  have hfactor : 2 ^ (k + 1) * m = n := by
    rw [← hk]
    exact Nat.ordProj_mul_ordCompl_eq_self n 2
  have hm1 : m ≠ 1 := by
    intro h
    rw [h, mul_one] at hfactor
    rw [← hfactor] at hsum
    have := sum_divisors_two_pow_add_one (k + 1)
    omega
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
  have hodd : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two hn0
  have hp2 : p ≠ 2 := fun heq => hodd (heq ▸ hpm)
  -- Twice the divisor used below still divides n, so primitivity applies even if m = p.
  have hdvd : 2 * (2 ^ k * p) ∣ n := by
    rw [← hfactor, ← mul_assoc, ← pow_succ']
    exact Nat.mul_dvd_mul_left _ hpm
  have hpos := Nat.mul_pos (by positivity : 0 < 2 ^ k) hp.pos
  have hlt : 2 ^ k * p < n := by
    have := Nat.le_of_dvd hn0.bot_lt hdvd
    omega
  have hdef := hproper (2 ^ k * p)
    (Nat.mem_divisors.mpr ⟨(dvd_mul_left _ _).trans hdvd, hn0⟩) hlt
  have hc := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  rw [(hc.pow_left k).sum_divisors_mul, hp.sum_divisors, ← mul_assoc,
    ← sum_divisors_two_pow_add_one, mul_add, add_mul, one_mul, mul_one] at hdef
  have hpow : 2 ^ (k + 1) < p := by
    obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
    rw [pow_succ']
    have := sum_divisors_two_pow_add_one k
    omega
  have hp_le : p ≤ ∏ q ∈ m.primeFactors, q :=
    Finset.single_le_prod (fun q hq => (Nat.prime_of_mem_primeFactors hq).one_lt.le)
      (hp.mem_primeFactors hpm hm.ne')
  rw [hk, ← hfactor, Nat.primeFactors_mul (by positivity) hm.ne',
    Nat.primeFactors_prime_pow (Nat.succ_ne_zero k) Nat.prime_two, Finset.singleton_union,
    Finset.prod_insert (fun h => hodd (Nat.dvd_of_mem_primeFactors h)), pow_succ' 2 (k + 1)]
  exact Nat.mul_lt_mul_of_pos_left (hpow.trans_le hp_le) (by decide)

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted
