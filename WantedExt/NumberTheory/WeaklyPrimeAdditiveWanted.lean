/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Weakly prime-additive numbers of length 4

Statements from Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*,
INTEGERS 24 (2024), Article A9 (definitions and assumption `(*)` read from arXiv:1903.10668v2).
Lemma 1 (Fermat–Euler) is Mathlib's `Nat.ModEq.pow_totient`, and Theorem 3 (Dirichlet) is
Mathlib's `Nat.infinite_setOfPred_prime_and_eq_mod`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Sums of powers of distinct prime divisors.** For natural numbers $n$ and $t$, $n$ is a sum
of positive powers of $t$ distinct prime divisors of $n$ when there are a set $s$ of $t$ distinct
primes, each dividing $n$, and positive integers $e_p$ for $p \in s$ such that
$n = \sum_{p \in s} p^{e_p}$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition (after Erdős and Hegyvári). -/
public def IsPrimeDivisorPowerSum (n t : ℕ) : Prop :=
  ∃ s : Finset ℕ, s.card = t ∧ (∀ p ∈ s, p.Prime ∧ p ∣ n) ∧
    ∃ e : ℕ → ℕ, (∀ p ∈ s, 0 < e p) ∧ n = ∑ p ∈ s, p ^ e p

/-- **Weakly prime-additive numbers.** A natural number $n$ is weakly prime-additive if it has at
least two distinct prime divisors and is a sum $n = \sum_{p \in s} p^{e_p}$ of positive powers
$p^{e_p}$, $e_p \ge 1$, over some set $s$ of distinct prime divisors of $n$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public def IsWeaklyPrimeAdditive (n : ℕ) : Prop :=
  2 ≤ n.primeFactors.card ∧ ∃ t, IsPrimeDivisorPowerSum n t

/-- **Weakly prime-additive length.** For a natural number $n$, the length $\kappa_n$ is the least
$t$ such that $n$ is a sum of positive powers of $t$ distinct prime divisors of $n$, and
$\kappa_n = 0$ when $n$ has no such representation.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public noncomputable def weaklyPrimeAdditiveLength (n : ℕ) : ℕ :=
  sInf {t | IsPrimeDivisorPowerSum n t}

/-- **Thirty is a sum of powers of three of its prime divisors.** The number $30$ is a sum of
positive powers of three distinct prime divisors of $30$, namely $30 = 2 + 3 + 5^2$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public theorem isPrimeDivisorPowerSum_thirty : IsPrimeDivisorPowerSum 30 3 := by
  refine ⟨{2, 3, 5}, by decide, ?_, fun p => if p = 5 then 2 else 1, ?_, by decide⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨Nat.prime_two, by norm_num⟩
    · exact ⟨Nat.prime_three, by norm_num⟩
    · exact ⟨Nat.prime_five, by norm_num⟩
  · intro p _
    dsimp only
    split_ifs <;> norm_num

/-- **Thirty is weakly prime-additive.** The number $30$ is weakly prime-additive.

Indeed, $30$ has the distinct prime divisors $2$, $3$, $5$ and $30 = 2 + 3 + 5^2$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public theorem isWeaklyPrimeAdditive_thirty : IsWeaklyPrimeAdditive 30 := by
  refine ⟨?_, 3, isPrimeDivisorPowerSum_thirty⟩
  have h : ({2, 3} : Finset ℕ) ⊆ (30 : ℕ).primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by norm_num, by norm_num⟩
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by norm_num, by norm_num⟩
  simpa using Finset.card_le_card h

/-- **The length is at most the size of any representation.** For natural numbers $n$ and $t$,
if $n$ is a sum of positive powers of $t$ distinct prime divisors of $n$, then the length
$\kappa_n$ of $n$ is at most $t$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition (minimality of `κ_n`). -/
public theorem weaklyPrimeAdditiveLength_le {n t : ℕ} (h : IsPrimeDivisorPowerSum n t) :
    weaklyPrimeAdditiveLength n ≤ t :=
  Nat.sInf_le h

/-- **Weakly prime-additive multiples of length four.** Assume $(\ast)$: for all natural numbers
$a$, $f$, $g$ with $1 \le a \le f$, $\gcd(a, f) = 1$ and $4 \mid f$, and $g$ an odd prime dividing
$f$ with Jacobi symbol $\left(\frac{g}{a}\right) = -1$, there is a prime $\ell \equiv a \pmod f$
such that $g$ is a primitive root modulo $\ell$. Then for every positive integer $m$ there are
infinitely many weakly prime-additive numbers $n$ with $m \mid n$ and length $\kappa_n = 4$.

The paper states $(\ast)$ with the Kronecker symbol; since $a$ is coprime to $f$ and $4 \mid f$,
$a$ is odd, so it is the Jacobi symbol.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 1. -/
public theorem_wanted infinite_weaklyPrimeAdditive_length_four_dvd
    (hstar : ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
      g ∣ f → jacobiSym g a = -1 →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1))
    (m : ℕ) (hm : 0 < m) :
    {n : ℕ | m ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 4}.Infinite

/-- **Primes completing a four-term prime-power divisibility.** Assume $(\ast)$: for all natural
numbers $a$, $f$, $g$ with $1 \le a \le f$, $\gcd(a, f) = 1$ and $4 \mid f$, and $g$ an odd prime
dividing $f$ with Jacobi symbol $\left(\frac{g}{a}\right) = -1$, there is a prime
$\ell \equiv a \pmod f$ such that $g$ is a primitive root modulo $\ell$. Let $p$, $q$, $r$ be
distinct odd primes, at least one of which is congruent to $3$ or $5$ modulo $8$. Then there are
infinitely many primes $s$, distinct from $p$, $q$ and $r$, for each of which there are
infinitely many quadruples $(e_1, e_2, e_3, e_4)$ of positive integers with
$pqrs \mid p^{e_1} + q^{e_2} + r^{e_3} + s^{e_4}$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 2. -/
public theorem_wanted infinite_primes_dvd_four_prime_power_sum
    (hstar : ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
      g ∣ f → jacobiSym g a = -1 →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1))
    (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp2 : Odd p) (hq2 : Odd q) (hr2 : Odd r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hmod : p % 8 = 3 ∨ p % 8 = 5 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ r % 8 = 3 ∨ r % 8 = 5) :
    {s : ℕ | s.Prime ∧ s ≠ p ∧ s ≠ q ∧ s ≠ r ∧
      {x : ℕ × ℕ × ℕ × ℕ | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2 ∧
        p * q * r * s ∣ p ^ x.1 + q ^ x.2.1 + r ^ x.2.2.1 + s ^ x.2.2.2}.Infinite}.Infinite

/-- **Fang–Chen theorem on shortest weakly prime-additive multiples.** For every positive integer
$m$, there are infinitely many weakly prime-additive numbers $n$ with $m \mid n$ and length
$\kappa_n = 3$ if and only if $8 \nmid m$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 5 (Fang and Chen, Corollary 1.1). -/
public theorem_wanted infinite_shortest_weaklyPrimeAdditive_dvd_iff (m : ℕ) (hm : 0 < m) :
    {n : ℕ | m ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 3}.Infinite ↔
      ¬ 8 ∣ m

/-- **Weakly prime-additive multiples of length at most four.** Assume $(\ast)$: for all natural
numbers $a$, $f$, $g$ with $1 \le a \le f$, $\gcd(a, f) = 1$ and $4 \mid f$, and $g$ an odd prime
dividing $f$ with Jacobi symbol $\left(\frac{g}{a}\right) = -1$, there is a prime
$\ell \equiv a \pmod f$ such that $g$ is a primitive root modulo $\ell$. Then for every positive
integer $m$ there are infinitely many weakly prime-additive numbers $n$ with $m \mid n$ and
length $\kappa_n \le 4$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 6. -/
public theorem_wanted infinite_weaklyPrimeAdditive_length_le_four_dvd
    (hstar : ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
      g ∣ f → jacobiSym g a = -1 →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1))
    (m : ℕ) (hm : 0 < m) :
    {n : ℕ | m ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n ≤ 4}.Infinite

end

end MetaMathlibExt
