/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Order.Ring.Int

/-!
# The equations `(-1)^α pˣ + (-1)^β (2ᵏ(2p - 1))ʸ = z²` for prime pairs `(p, 2p - 1)`

Statements from Jing Zhang and Yuan Li, *On the Equation
(-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024),
Article A64. All unknowns `x`, `y`, `z` are non-negative integers; equations with a
subtraction are read in `ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Prime powers one less than a square.** Let $p$ be a prime. Then non-negative integers $x$
and $y$ satisfy $p^x + 1 = y^2$ if and only if $(p, x, y) = (2, 3, 3)$ or $(p, x, y) = (3, 1, 2)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 2. -/
theorem_wanted prime_pow_add_one_eq_sq_iff {p : ℕ} (hp : p.Prime) (x y : ℕ) :
    p ^ x + 1 = y ^ 2 ↔ (p, x, y) = (2, 3, 3) ∨ (p, x, y) = (3, 1, 2)

/-- **Squares of the form $1 + (2^k(2p - 1))^y$ for prime pairs.** Let $p$ be an odd prime such
that $2p - 1$ is prime, and let $k \ge 1$ be an integer. Then non-negative integers $y$ and $z$
satisfy $1 + (2^k(2p - 1))^y = z^2$ if and only if $k = 4$, $p = 3$, $y = 1$ and $z = 9$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 4. -/
theorem_wanted one_add_two_pow_mul_pow_eq_sq_iff {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : (2 * p - 1).Prime) (hk : 1 ≤ k) (y z : ℕ) :
    1 + (2 ^ k * (2 * p - 1)) ^ y = z ^ 2 ↔ (k, p, y, z) = (4, 3, 1, 9)

/-- **Terai's conjecture when $c$ is prime and $b \equiv \pm 5 \pmod 8$.** Let $a, b, c$ be
natural numbers with $a^2 + b^2 = c^2$, $\gcd(a, b, c) = 1$, $b \equiv \pm 5 \pmod 8$ (that is,
$b$ is $3$ or $5$ modulo $8$) and $c$ prime. Then for all positive integers $x, y, z$, the
equation $x^2 + b^y = c^z$ holds if and only if $(x, y, z) = (a, 2, 2)$.

This case of the conjecture is due to Yuan and Wang. Terai's conjecture (the paper's Conjecture 1)
also assumes $a$ even, which follows here since $b$ is odd.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 6 and Conjecture 1. -/
theorem_wanted terai_pythagorean_of_prime_of_mod_eight {a b c : ℕ} (habc : a ^ 2 + b ^ 2 = c ^ 2)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1) (hb : b % 8 = 3 ∨ b % 8 = 5) (hc : c.Prime)
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 2 + b ^ y = c ^ z ↔ (x, y, z) = (a, 2, 2)

/-- **Integer points on three Mordell curves.** The integer solutions of $y^2 = x^3 - 2$ are
exactly $(x, y) = (3, 5)$ and $(3, -5)$, the integer solutions of $y^2 = x^3 - 18$ are exactly
$(x, y) = (3, 3)$ and $(3, -3)$, and $y^2 = x^3 - 162$ has no integer solutions.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 7 (quoted from the LMFDB). -/
theorem_wanted mordell_curves_two_eighteen_one_six_two_integer_points :
    (∀ x y : ℤ, y ^ 2 = x ^ 3 - 2 ↔ x = 3 ∧ (y = 5 ∨ y = -5)) ∧
      (∀ x y : ℤ, y ^ 2 = x ^ 3 - 18 ↔ x = 3 ∧ (y = 3 ∨ y = -3)) ∧
      ∀ x y : ℤ, y ^ 2 ≠ x ^ 3 - 162

/-- **Solutions of $3^x = y^2 + 2$.** For natural numbers $x, y$, we have $3^x = y^2 + 2$ if and
only if $(x, y)$ is $(1, 1)$ or $(3, 5)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 8. -/
theorem_wanted three_pow_eq_sq_add_two_iff (x y : ℕ) :
    3 ^ x = y ^ 2 + 2 ↔ (x, y) = (1, 1) ∨ (x, y) = (3, 5)

/-- **Solutions of $2x^2 + 1 = 3^y$.** For natural numbers $x, y$, we have $2x^2 + 1 = 3^y$ if and
only if $(x, y)$ is $(0, 0)$, $(1, 1)$, $(2, 2)$ or $(11, 5)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 9. -/
theorem_wanted two_mul_sq_add_one_eq_three_pow_iff (x y : ℕ) :
    2 * x ^ 2 + 1 = 3 ^ y ↔
      (x, y) = (0, 0) ∨ (x, y) = (1, 1) ∨ (x, y) = (2, 2) ∨ (x, y) = (11, 5)

/-- **Squares of the form $p^x + (2p - 1)^y$ for prime pairs.** Let $p$ be an odd prime such that
$2p - 1$ is prime. Then non-negative integers $x$, $y$ and $z$ satisfy $p^x + (2p - 1)^y = z^2$
if and only if $p = 3$ and $(x, y, z) = (1, 0, 2)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 1. -/
theorem_wanted prime_pair_pow_add_pow_eq_sq_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : (2 * p - 1).Prime) (x y z : ℕ) :
    p ^ x + (2 * p - 1) ^ y = z ^ 2 ↔ (p, x, y, z) = (3, 1, 0, 2)

/-- **No squares of the form $p^x + (2^{2k+1}(2p - 1))^y$ for prime pairs with
$p \equiv 5, 7 \pmod 8$.** Let $p$ be a prime with $p \equiv 5 \pmod 8$ or $p \equiv 7 \pmod 8$
such that $2p - 1$ is prime. Then for all non-negative integers $k$, $x$, $y$ and $z$,
$p^x + (2^{2k+1}(2p - 1))^y \ne z^2$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 2. -/
theorem_wanted prime_pair_pow_add_two_pow_odd_mul_pow_ne_sq {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7) (k x y z : ℕ) :
    p ^ x + (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y ≠ z ^ 2

/-- **Squares of the form $p^x + (2^{2k}(2p - 1))^y$ for prime pairs.** Let $p$ be a prime with
$p \equiv 3 \pmod 4$ such that $2p - 1$ is prime, and let $k \ge 1$ be an integer. Then
non-negative integers $x$, $y$ and $z$ satisfy $p^x + (2^{2k}(2p - 1))^y = z^2$ if and only if
either $p = 3$ and $(x, y, z) = (1, 0, 2)$, or $p = 3$, $k = 2$ and $(x, y, z) = (0, 1, 9)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 3. -/
theorem_wanted prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff {p k : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp4 : p % 4 = 3) (hk : 1 ≤ k) (x y z : ℕ) :
    p ^ x + (2 ^ (2 * k) * (2 * p - 1)) ^ y = z ^ 2 ↔
      (p, x, y, z) = (3, 1, 0, 2) ∨ (p, k, x, y, z) = (3, 2, 0, 1, 9)

/-- **Squares of the form $(2p - 1)^x - p^y$ for prime pairs.** Let $p$ be a prime with
$p \equiv 3 \pmod 4$ such that $2p - 1$ is prime. Then non-negative integers $x$, $y$ and $z$
satisfy $(2p - 1)^x - p^y = z^2$ if and only if $(x, y, z) = (0, 0, 0)$, or $p = 3$ and
$(x, y, z) = (2, 2, 4)$, or $p = 2t^2 + 1$ for some non-negative integer $t$ and
$(x, y, z) = (1, 0, 2t)$.

In the last family the two primes are $p = 2t^2 + 1$ and $2p - 1 = 4t^2 + 1$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 4. -/
theorem_wanted prime_pair_pow_sub_pow_eq_sq_iff {p : ℕ} (hp : p.Prime) (hq : (2 * p - 1).Prime)
    (hp4 : p % 4 = 3) (x y z : ℕ) :
    (2 * (p : ℤ) - 1) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) ∨ (p, x, y, z) = (3, 2, 2, 4) ∨
        ∃ t : ℕ, p = 2 * t ^ 2 + 1 ∧ x = 1 ∧ y = 0 ∧ z = 2 * t

/-- **Squares of the form $(2^{2k}(2p - 1))^x - p^y$ for prime pairs.** Let $p$ be a prime with
$p \equiv 3 \pmod 4$ such that $2p - 1$ is prime, and let $k \ge 1$ be an integer. Then
non-negative integers $x$, $y$ and $z$ satisfy $(2^{2k}(2p - 1))^x - p^y = z^2$ if and only if
$(x, y, z) = (0, 0, 0)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 6. -/
theorem_wanted prime_pair_two_pow_even_mul_pow_sub_pow_eq_sq_iff {p k : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp4 : p % 4 = 3) (hk : 1 ≤ k) (x y z : ℕ) :
    ((2 : ℤ) ^ (2 * k) * (2 * p - 1)) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2 ↔ (x, y, z) = (0, 0, 0)

/-- **Squares of the form $(2^{2k+1}(2p - 1))^x - p^y$ for prime pairs.** Let $p$ be a prime with
$p \equiv 5 \pmod 8$ such that $2p - 1$ is prime, and let $k$ be a non-negative integer. Then
non-negative integers $x$, $y$ and $z$ satisfy $(2^{2k+1}(2p - 1))^x - p^y = z^2$ if and only if
$(x, y, z) = (0, 0, 0)$, or $k = 0$, $x = 1$, $y = 0$ and $4p = z^2 + 3$.

In the last case the two primes are $p = (z^2 + 3)/4$ and $2p - 1 = (z^2 + 1)/2$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 7. -/
theorem_wanted prime_pair_two_pow_odd_mul_pow_sub_pow_eq_sq_iff {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp8 : p % 8 = 5) (k x y z : ℕ) :
    ((2 : ℤ) ^ (2 * k + 1) * (2 * p - 1)) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) ∨ (4 * p = z ^ 2 + 3 ∧ k = 0 ∧ x = 1 ∧ y = 0)

/-- **Squares of the form $p^x - (2^{2k+1}(2p - 1))^y$ for prime pairs.** Let $p$ be a prime with
$p \equiv 3 \pmod 8$ such that $2p - 1$ is prime, and let $k$ be a non-negative integer. Then
non-negative integers $x$, $y$ and $z$ satisfy $p^x - (2^{2k+1}(2p - 1))^y = z^2$ if and only if
$(x, y, z) = (0, 0, 0)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 9. -/
theorem_wanted prime_pair_pow_sub_two_pow_odd_mul_pow_eq_sq_iff {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp8 : p % 8 = 3) (k x y z : ℕ) :
    (p : ℤ) ^ x - ((2 : ℤ) ^ (2 * k + 1) * (2 * p - 1)) ^ y = (z : ℤ) ^ 2 ↔ (x, y, z) = (0, 0, 0)

/-- **The exponential equations for the prime pair (2, 3).** The six equations
$(-1)^\alpha 2^x + (-1)^\beta (2^k \cdot 3)^y = z^2$ with $\alpha, \beta, k \in \{0, 1\}$ and
$\alpha\beta = 0$ have exactly the following solutions in natural numbers $x, y, z$, where the
equations are read in the integers. The equation $2^x + 3^y = z^2$ holds if and only if
$(x, y, z)$ is $(0, 1, 2)$, $(3, 0, 3)$ or $(4, 2, 5)$. The equation $2^x - 3^y = z^2$ holds if
and only if $(x, y, z)$ is $(0, 0, 0)$, $(1, 0, 1)$ or $(2, 1, 1)$. The equation
$-2^x + 3^y = z^2$ holds if and only if $(x, y, z)$ is $(0, 0, 0)$, $(1, 1, 1)$, $(1, 3, 5)$,
$(3, 2, 1)$ or $(5, 4, 7)$. The equation $2^x + 6^y = z^2$ holds if and only if $(x, y, z)$ is
$(3, 0, 3)$ or $(6, 2, 10)$. The equation $2^x - 6^y = z^2$ holds if and only if $(x, y, z)$ is
$(0, 0, 0)$ or $(1, 0, 1)$. The equation $-2^x + 6^y = z^2$ holds if and only if $(x, y, z)$ is
$(0, 0, 0)$, $(1, 1, 2)$, $(5, 2, 2)$, $(9, 4, 28)$ or $(5, 5, 88)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 10. -/
theorem_wanted two_pow_three_pow_six_pow_eq_sq_solutions :
    (∀ x y z : ℕ, (2 : ℤ) ^ x + 3 ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 1, 2) ∨ (x, y, z) = (3, 0, 3) ∨ (x, y, z) = (4, 2, 5)) ∧
    (∀ x y z : ℕ, (2 : ℤ) ^ x - 3 ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) ∨ (x, y, z) = (1, 0, 1) ∨ (x, y, z) = (2, 1, 1)) ∧
    (∀ x y z : ℕ, -(2 : ℤ) ^ x + 3 ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) ∨ (x, y, z) = (1, 1, 1) ∨ (x, y, z) = (1, 3, 5) ∨
        (x, y, z) = (3, 2, 1) ∨ (x, y, z) = (5, 4, 7)) ∧
    (∀ x y z : ℕ, (2 : ℤ) ^ x + 6 ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (3, 0, 3) ∨ (x, y, z) = (6, 2, 10)) ∧
    (∀ x y z : ℕ, (2 : ℤ) ^ x - 6 ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) ∨ (x, y, z) = (1, 0, 1)) ∧
    (∀ x y z : ℕ, -(2 : ℤ) ^ x + 6 ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) ∨ (x, y, z) = (1, 1, 2) ∨ (x, y, z) = (5, 2, 2) ∨
        (x, y, z) = (9, 4, 28) ∨ (x, y, z) = (5, 5, 88))

/-- **Solutions of $2 + 7^y = z^2$.** For natural numbers $y, z$, we have $2 + 7^y = z^2$ if and
only if $(y, z) = (1, 3)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 11. -/
theorem_wanted two_add_seven_pow_eq_sq_iff (y z : ℕ) : 2 + 7 ^ y = z ^ 2 ↔ (y, z) = (1, 3)

end

end MetaMathlibExt
