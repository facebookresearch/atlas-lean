/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.WeaklyPrimeAdditive

/-!
# Weakly prime-additive numbers of length 4

Statements from Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*,
INTEGERS 24 (2024), Article A9 (definitions and assumption `(*)` read from arXiv:1903.10668v2).
Lemma 1 (Fermat–Euler) is Mathlib's `Nat.ModEq.pow_totient`, and Theorem 3 (Dirichlet) is
Mathlib's `Nat.infinite_setOfPred_prime_and_eq_mod`.
-/

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
