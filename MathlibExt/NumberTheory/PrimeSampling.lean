/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Size
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.Chebyshev
public import MathlibExt.NumberTheory.PrimeCounting.ChebyshevThetaBounds
public import MathlibExt.Probability.ProbabilityMassFunction.Uniform

/-!
# Sampling `n`-bit primes

RSA key generation needs uniformly random `n`-bit primes, produced by the prime generation
algorithm of Katz-Lindell, *Introduction to Modern Cryptography*, 2nd ed., §8.2.1, Algorithm 8.31.
This file provides the finite set of `n`-bit primes, the fact that it is nonempty, and the uniform
distribution on it.

This distribution is not the parameter distribution of ElGamal or Diffie-Hellman. Those schemes
are parameterized by a group-generation algorithm `𝒢` returning a cyclic group `G` of order `q`
with generator `g` (Katz-Lindell, 2nd ed., §8.3.2), and their key generation samples exponents
uniformly from `ℤ_q`. Nothing there makes `q` uniform over the `n`-bit primes; a finite-field
instantiation of `𝒢` needs further constraints on the group order (e.g. `q ∣ p - 1` for prime
`p`, §8.3.3). Do not model `𝒢` with `Nat.uniformNBitPrime`.

## Main definitions

* `Nat.nBitPrimes n`: the primes `p` with `2 ^ (n - 1) ≤ p < 2 ^ n`, i.e. with exactly `n` binary
  digits (`Nat.mem_nBitPrimes_iff_size`).
* `Nat.uniformNBitPrime n hn`: the uniform `PMF` on `Nat.nBitPrimes n` for `2 ≤ n`.

## Main results

* `Nat.exists_prime_Ioo_two_pow`: for `2 ≤ n` there is a prime strictly between `2 ^ (n - 1)`
  and `2 ^ n`. This is Mathlib's Bertrand postulate (`Nat.exists_prime_lt_and_le_two_mul`)
  applied at `2 ^ (n - 1)`; the bound `2 ≤ n` is sharp (`Nat.nBitPrimes_one`).
* `Nat.nBitPrimes_nonempty`: there is an `n`-bit prime for every `2 ≤ n`.
* `Nat.support_uniformNBitPrime`: the sampler's support is exactly the `n`-bit primes, and
  `Nat.support_uniformNBitPrime_eq_Ioo` states it with the open interval for `3 ≤ n`.
* `Nat.theta_sub_theta_le_card_nBitPrimes_mul`, `Nat.card_nBitPrimes_mul_log_gt`: a lower bound
  on the number of `n`-bit primes, from the explicit Chebyshev bounds on `θ`
  (`MetaMathlibExt.chebyshev_theta_explicit_bounds`). Its main term is
  `0.8 A · 2 ^ (n - 1)` with `A ≈ 0.9213`, so the fraction of `n`-bit integers that are prime is at
  least `0.8 A / (n log 2) ≈ 1.06 / n` up to `O(n ^ 2 / 2 ^ (n / 2))` error terms.
* `Nat.primeCounting_two_pow_mul_log_ge`: the Chebyshev lower bound
  `π(2 ^ n) ≥ 2 ^ n / n - log(2 ^ n + 1) / (n log 2)`, from Mathlib's `Chebyshev.psi_ge`.
  `π(2 ^ n)` counts the primes `≤ 2 ^ n`.
* `Nat.card_primesBelow_two_pow_mul_log_ge`: the same bound on the number of primes `< 2 ^ n`, for
  `2 ≤ n`. Divided by `2 ^ n`, it bounds the probability that a uniform integer in `[0, 2 ^ n)` is
  prime, which is what makes rejection sampling efficient. The probability reading needs `2 ≤ n`:
  at `n = 1` the endpoint `2 = 2 ^ 1` is prime and counted by `π(2)`, but a uniform integer in
  `{0, 1}` is never prime; at `n = 0` the division by `n log 2` is undefined.

## Implementation notes

The `PMF` is `PMF.uniformFinset` from `MathlibExt.Probability.ProbabilityMassFunction.Uniform`
(in the pinned Mathlib, `PMF.uniformOfFinset` is a deprecated alias for the measure
`MeasureTheory.Measure.uniformOfFinset`, and `MathlibExt` may not import CSLib's
`Cslib.Probability.PMF.uniformOfFinset`). Its mass function is the same one CSLib uses, so a
CSLibExt keygen can rewrite between the two.

Katz-Lindell 2nd ed. Theorem 8.32 states the clean form "at least a `1 / (3n)` fraction of
`n`-bit integers is prime, for every `n > 1`". `Nat.card_nBitPrimes_mul_log_gt` implies it for
all large `n`, but turning its error terms into an explicit threshold (plus a finite check below
it) is not done here.
-/

@[expose] public section

open Finset

namespace Nat

/-- The `n`-bit primes: primes `p` with `2 ^ (n - 1) ≤ p < 2 ^ n`. These are the outputs of the
prime generation algorithm of Katz-Lindell, 2nd ed., §8.2.1, Algorithm 8.31, which samples
`p = 1 ‖ p'` for a uniform `p' ∈ {0,1}^(n-1)` and keeps it when `p` is prime. -/
def nBitPrimes (n : ℕ) : Finset ℕ :=
  (Ico (2 ^ (n - 1)) (2 ^ n)).filter Nat.Prime

/-- Membership in `Nat.nBitPrimes` (Katz-Lindell, 2nd ed., §8.2.1). -/
theorem mem_nBitPrimes {n p : ℕ} :
    p ∈ nBitPrimes n ↔ p.Prime ∧ 2 ^ (n - 1) ≤ p ∧ p < 2 ^ n := by
  simp only [nBitPrimes, mem_filter, mem_Ico]
  tauto

/-- An `n`-bit prime is a prime whose binary representation has exactly `n` digits
(Katz-Lindell, 2nd ed., §8.2.1). -/
theorem mem_nBitPrimes_iff_size {n p : ℕ} : p ∈ nBitPrimes n ↔ p.Prime ∧ p.size = n := by
  rw [mem_nBitPrimes]
  refine and_congr_right fun hp => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [zero_tsub, pow_zero, size_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩; omega
    · rintro rfl; exact absurd hp Nat.not_prime_zero
  · rw [le_antisymm_iff, size_le, ← lt_size (m := n - 1)]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

/-- Every element of `Nat.nBitPrimes n` is prime. -/
theorem prime_of_mem_nBitPrimes {n p : ℕ} (h : p ∈ nBitPrimes n) : p.Prime :=
  (mem_nBitPrimes.1 h).1

/-- There is no `1`-bit prime: the hypothesis `2 ≤ n` in `Nat.nBitPrimes_nonempty` is sharp. -/
theorem nBitPrimes_one : nBitPrimes 1 = ∅ := by
  decide

/-- For `n ≠ 2`, the `n`-bit primes are exactly the primes in the open interval
`(2 ^ (n - 1), 2 ^ n)`, because `2 ^ (n - 1)` is prime only for `n = 2`. -/
theorem nBitPrimes_eq_filter_Ioo {n : ℕ} (hn : n ≠ 2) :
    nBitPrimes n = (Ioo (2 ^ (n - 1)) (2 ^ n)).filter Nat.Prime := by
  ext p
  simp only [mem_nBitPrimes, mem_filter, mem_Ioo]
  constructor
  · rintro ⟨hp, h1, h2⟩
    refine ⟨⟨lt_of_le_of_ne h1 fun he => hn ?_, h2⟩, hp⟩
    subst he
    have := ((Nat.Prime.pow_eq_iff hp).1 rfl).2
    omega
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, h1.le, h2⟩

/-- **Bertrand's postulate on a dyadic interval.** For `2 ≤ n` there is a prime `p` with
`2 ^ (n - 1) < p < 2 ^ n`. This is Mathlib's `Nat.exists_prime_lt_and_le_two_mul` at
`2 ^ (n - 1)`; Katz-Lindell, 2nd ed., §8.2.1 uses it (in the quantitative form of Theorem 8.32)
to show that Algorithm 8.31 succeeds. -/
theorem exists_prime_Ioo_two_pow {n : ℕ} (hn : 2 ≤ n) :
    ∃ p, p.Prime ∧ 2 ^ (n - 1) < p ∧ p < 2 ^ n := by
  obtain ⟨p, hp, hlt, hle⟩ := exists_prime_lt_and_le_two_mul (2 ^ (n - 1)) (by positivity)
  have h2n : 2 * 2 ^ (n - 1) = 2 ^ n := by
    rw [← pow_succ']; congr 1; omega
  rw [h2n] at hle
  refine ⟨p, hp, hlt, lt_of_le_of_ne hle fun he => ?_⟩
  subst he
  have := ((Nat.Prime.pow_eq_iff hp).1 rfl).2
  omega

/-- There is an `n`-bit prime for every `2 ≤ n` (Katz-Lindell, 2nd ed., §8.2.1). -/
theorem nBitPrimes_nonempty {n : ℕ} (hn : 2 ≤ n) : (nBitPrimes n).Nonempty := by
  obtain ⟨p, hp, h1, h2⟩ := exists_prime_Ioo_two_pow hn
  exact ⟨p, mem_nBitPrimes.2 ⟨hp, h1.le, h2⟩⟩

/-- The number of `n`-bit primes is positive for every `2 ≤ n`. -/
theorem card_nBitPrimes_pos {n : ℕ} (hn : 2 ≤ n) : 0 < (nBitPrimes n).card :=
  Finset.card_pos.2 (nBitPrimes_nonempty hn)

/-- The uniform distribution on the `n`-bit primes, the output distribution of Katz-Lindell,
2nd ed., §8.2.1, Algorithm 8.31 conditioned on success. RSA key generation (§11.5) samples its
primes this way. It is not a model of the group-generation algorithm `𝒢` that parameterizes
ElGamal and Diffie-Hellman (§8.3.2): those sample exponents in a supplied group, and its order
need not be uniform over the `n`-bit primes. -/
noncomputable def uniformNBitPrime (n : ℕ) (hn : 2 ≤ n) : PMF ℕ :=
  PMF.uniformFinset (nBitPrimes n) (nBitPrimes_nonempty hn)

/-- The probability mass of `Nat.uniformNBitPrime` (`PMF.uniformFinset_apply`). -/
theorem uniformNBitPrime_apply {n : ℕ} (hn : 2 ≤ n) (p : ℕ) :
    uniformNBitPrime n hn p =
      if p ∈ nBitPrimes n then ((nBitPrimes n).card : ENNReal)⁻¹ else 0 := by
  rw [uniformNBitPrime, PMF.uniformFinset_apply]
  congr

/-- Every `n`-bit prime has probability `1 / #(n-bit primes)` under `Nat.uniformNBitPrime`. -/
theorem uniformNBitPrime_apply_of_mem {n p : ℕ} (hn : 2 ≤ n) (hp : p ∈ nBitPrimes n) :
    uniformNBitPrime n hn p = ((nBitPrimes n).card : ENNReal)⁻¹ := by
  simp [uniformNBitPrime_apply, hp]

/-- Anything other than an `n`-bit prime has probability `0` under `Nat.uniformNBitPrime`. -/
theorem uniformNBitPrime_apply_of_notMem {n p : ℕ} (hn : 2 ≤ n) (hp : p ∉ nBitPrimes n) :
    uniformNBitPrime n hn p = 0 := by
  simp [uniformNBitPrime_apply, hp]

/-- The support of `Nat.uniformNBitPrime n` is exactly the set of `n`-bit primes. -/
theorem support_uniformNBitPrime {n : ℕ} (hn : 2 ≤ n) :
    (uniformNBitPrime n hn).support = {p | p.Prime ∧ 2 ^ (n - 1) ≤ p ∧ p < 2 ^ n} := by
  ext p
  rw [PMF.mem_support_iff, uniformNBitPrime_apply, Set.mem_ofPred_eq, ← mem_nBitPrimes]
  split_ifs with h
  · simp only [ne_eq, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, not_false_eq_true, h]
  · simp only [ne_eq, not_true_eq_false, h]

/-- For `3 ≤ n`, the support of `Nat.uniformNBitPrime n` is exactly the set of primes in the open
interval `(2 ^ (n - 1), 2 ^ n)`. -/
theorem support_uniformNBitPrime_eq_Ioo {n : ℕ} (hn : 3 ≤ n) :
    (uniformNBitPrime n (by omega)).support = {p | p.Prime ∧ 2 ^ (n - 1) < p ∧ p < 2 ^ n} := by
  ext p
  have h := Finset.ext_iff.1 (nBitPrimes_eq_filter_Ioo (n := n) (by omega)) p
  rw [support_uniformNBitPrime, Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← mem_nBitPrimes, h,
    mem_filter, mem_Ioo]
  tauto

/-- Every sample of `Nat.uniformNBitPrime` is prime. -/
theorem prime_of_mem_support_uniformNBitPrime {n p : ℕ} (hn : 2 ≤ n)
    (hp : p ∈ (uniformNBitPrime n hn).support) : p.Prime := by
  rw [support_uniformNBitPrime] at hp
  exact hp.1

open scoped Chebyshev in
/-- The `log`-weighted count of primes in `(2 ^ (n - 1), 2 ^ n]`, `θ(2 ^ n) - θ(2 ^ (n - 1))`, is at
most `#(n-bit primes) · log(2 ^ n)`. This turns lower bounds on Chebyshev's `θ` into lower
bounds on the number of `n`-bit primes (Katz-Lindell, 2nd ed., Theorem 8.32). -/
theorem theta_sub_theta_le_card_nBitPrimes_mul {n : ℕ} (hn : 2 ≤ n) :
    θ ((2 : ℝ) ^ n) - θ ((2 : ℝ) ^ (n - 1)) ≤ (nBitPrimes n).card * (n * Real.log 2) := by
  have hcast : ∀ k : ℕ, (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) := fun k => by push_cast; rfl
  rw [hcast n, hcast (n - 1), Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log]
  have hle : 2 ^ (n - 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsub : primesLE (2 ^ (n - 1)) ⊆ primesLE (2 ^ n) := fun p hp => by
    rw [mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hle, hp.2⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hsd : primesLE (2 ^ n) \ primesLE (2 ^ (n - 1)) ⊆ nBitPrimes n := fun p hp => by
    rw [Finset.mem_sdiff, mem_primesLE, mem_primesLE] at hp
    obtain ⟨⟨hpb, hp⟩, hpa⟩ := hp
    have hpa' : 2 ^ (n - 1) < p := by
      by_contra h
      exact hpa ⟨not_lt.1 h, hp⟩
    refine mem_nBitPrimes.2 ⟨hp, hpa'.le, lt_of_le_of_ne hpb fun he => ?_⟩
    subst he
    have := ((Nat.Prime.pow_eq_iff hp).1 rfl).2
    omega
  calc ∑ p ∈ primesLE (2 ^ n) \ primesLE (2 ^ (n - 1)), Real.log p
      ≤ ∑ p ∈ nBitPrimes n, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsd fun p _ _ => Real.log_natCast_nonneg p
    _ ≤ (nBitPrimes n).card • Real.log ((2 ^ n : ℕ) : ℝ) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
        have hp' := mem_nBitPrimes.1 hp
        exact Real.log_le_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2.le)
    _ = (nBitPrimes n).card * (n * Real.log 2) := by
        rw [nsmul_eq_mul]
        push_cast
        rw [Real.log_pow]

/-- **Density of `n`-bit primes.** An explicit lower bound on the number of `n`-bit primes for
`2 ≤ n`, obtained from `Nat.theta_sub_theta_le_card_nBitPrimes_mul` and Chebyshev's explicit
bounds on `θ` (`MetaMathlibExt.chebyshev_theta_explicit_bounds`) at `2 ^ n` and `2 ^ (n - 1)`.
With `y = 2 ^ (n - 1)`, the left side is `0.8 A y - O(√y)`, where `A ≈ 0.9213` is Chebyshev's
constant; this is the quantitative content of Katz-Lindell, 2nd ed., Theorem 8.32 for large `n`. -/
theorem card_nBitPrimes_mul_log_gt {n : ℕ} (hn : 2 ≤ n) :
    let A : ℝ :=
      Real.log (((2 : ℝ) ^ ((1 / 2 : ℝ)) * (3 : ℝ) ^ ((1 / 3 : ℝ)) *
        (5 : ℝ) ^ ((1 / 5 : ℝ))) / (30 : ℝ) ^ ((1 / 30 : ℝ)))
    let y : ℝ := 2 ^ (n - 1)
    (A * (2 * y) - (12 / 5 : ℝ) * A * Real.sqrt (2 * y) -
        (5 / (8 * Real.log 6)) * (Real.log (2 * y)) ^ 2 - (15 / 4 : ℝ) * Real.log (2 * y) - 3) -
      ((6 / 5 : ℝ) * A * y - A * Real.sqrt y + (5 / (4 * Real.log 6)) * (Real.log y) ^ 2 +
        (5 / 2 : ℝ) * Real.log y + 2) <
      (nBitPrimes n).card * (n * Real.log 2) := by
  intro A y
  have h2y : (2 : ℝ) * y = 2 ^ n := by
    have hn' : n = (n - 1) + 1 := by omega
    conv_rhs => rw [hn']
    rw [pow_succ]
    ring
  have hy1 : (1 : ℝ) < y := one_lt_pow₀ (by norm_num) (by omega)
  have hlo := (MetaMathlibExt.chebyshev_theta_explicit_bounds (2 * y) (by linarith)).2
  have hhi := (MetaMathlibExt.chebyshev_theta_explicit_bounds y hy1).1
  have hmain := theta_sub_theta_le_card_nBitPrimes_mul hn
  rw [← h2y] at hmain
  linarith

/-- **Chebyshev lower bound at a power of two.** `π(2 ^ n) · (n log 2) ≥ 2 ^ n log 2 -
log(2 ^ n + 1)`, where `π(2 ^ n)` counts the primes `≤ 2 ^ n`. It combines Mathlib's
`Chebyshev.psi_ge` and `Chebyshev.psi_le_primeCounting_mul_log`, and holds for every `n`. This is
the global form of the density bound behind Katz-Lindell, 2nd ed., Theorem 8.32; the bound for the
dyadic interval alone is not proved here. It is not by itself a statement about uniform integers
below `2 ^ n`: at `n = 1` it counts the prime `2`, which `{0, 1}` does not contain. For that
reading use `Nat.card_primesBelow_two_pow_mul_log_ge`, which assumes `2 ≤ n`. -/
theorem primeCounting_two_pow_mul_log_ge (n : ℕ) :
    (2 : ℝ) ^ n * Real.log 2 - Real.log (2 ^ n + 1) ≤ (2 ^ n).primeCounting * (n * Real.log 2) := by
  have h1 := Chebyshev.psi_ge (2 ^ n)
  have h2 := Chebyshev.psi_le_primeCounting_mul_log (2 ^ n)
  push_cast at h1 h2
  rw [Real.log_pow] at h2
  linarith

/-- For `2 ≤ n`, the primes `< 2 ^ n` and the primes `≤ 2 ^ n` have the same count, because
`2 ^ n` is not prime. This fails at `n = 1`: `π(2) = 1` but no natural below `2` is prime. -/
theorem card_primesBelow_two_pow {n : ℕ} (hn : 2 ≤ n) :
    (primesBelow (2 ^ n)).card = (2 ^ n).primeCounting := by
  have h : ¬ (2 ^ n).Prime := fun hp => by
    have := ((Nat.Prime.pow_eq_iff hp).1 rfl).2
    omega
  rw [primesBelow_card_eq_primeCounting', primeCounting, primeCounting', count_succ]
  simp [h]

/-- **Probability that a uniform `n`-bit-or-shorter integer is prime.** For `2 ≤ n`, the number of
primes in `[0, 2 ^ n)` satisfies `#primes · (n log 2) ≥ 2 ^ n log 2 - log(2 ^ n + 1)`, so a
uniform integer below `2 ^ n` is prime with probability at least
`1 / n - log(2 ^ n + 1) / (n 2 ^ n log 2)` (the density bound behind Katz-Lindell, 2nd ed.,
Theorem 8.32). The hypothesis `2 ≤ n` is needed: at `n = 1` the left side is
`2 log 2 - log 3 = log (4 / 3) > 0` (a claimed probability of about `0.2075`), while no integer
below `2` is prime. -/
theorem card_primesBelow_two_pow_mul_log_ge {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) ^ n * Real.log 2 - Real.log (2 ^ n + 1) ≤
      (primesBelow (2 ^ n)).card * (n * Real.log 2) := by
  rw [card_primesBelow_two_pow hn]
  exact primeCounting_two_pow_mul_log_ge n

end Nat
