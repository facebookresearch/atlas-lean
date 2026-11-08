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

/-- For a prime `p`, the only non-negative solutions of `pˣ + 1 = y²` are `(p, x, y) = (2, 3, 3)`
and `(3, 1, 2)`.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 2. -/
theorem_wanted prime_pow_add_one_eq_sq_iff {p : ℕ} (hp : p.Prime) (x y : ℕ) :
    p ^ x + 1 = y ^ 2 ↔ (p, x, y) = (2, 3, 3) ∨ (p, x, y) = (3, 1, 2)

/-- If `p` and `2p - 1` are odd primes and `k ≥ 1`, then `1 + (2ᵏ(2p - 1))ʸ = z²` has the unique
non-negative solution `(k, p, y, z) = (4, 3, 1, 9)`.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 4. -/
theorem_wanted one_add_two_pow_mul_pow_eq_sq_iff {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : (2 * p - 1).Prime) (hk : 1 ≤ k) (y z : ℕ) :
    1 + (2 ^ k * (2 * p - 1)) ^ y = z ^ 2 ↔ (k, p, y, z) = (4, 3, 1, 9)

/-- Terai's conjecture for primitive Pythagorean triples with `b ≡ ±5 (mod 8)` and `c` prime
(Yuan–Wang): if `a² + b² = c²`, `gcd(a, b, c) = 1`, `b ≡ ±5 (mod 8)` and `c` is prime, then
`x² + bʸ = cᶻ` has the unique positive solution `(x, y, z) = (a, 2, 2)`. Terai's conjecture
(the paper's Conjecture 1) also assumes `a` even, which follows here since `b` is odd.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 6 and Conjecture 1. -/
theorem_wanted terai_pythagorean_of_prime_of_mod_eight {a b c : ℕ} (habc : a ^ 2 + b ^ 2 = c ^ 2)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1) (hb : b % 8 = 3 ∨ b % 8 = 5) (hc : c.Prime)
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 2 + b ^ y = c ^ z ↔ (x, y, z) = (a, 2, 2)

/-- Integer points: `y² = x³ - 2` only at `(3, ±5)`, `y² = x³ - 18` only at `(3, ±3)`, and
`y² = x³ - 162` has none.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 7 (quoted from the LMFDB). -/
theorem_wanted mordell_curves_two_eighteen_one_six_two_integer_points :
    (∀ x y : ℤ, y ^ 2 = x ^ 3 - 2 ↔ x = 3 ∧ (y = 5 ∨ y = -5)) ∧
      (∀ x y : ℤ, y ^ 2 = x ^ 3 - 18 ↔ x = 3 ∧ (y = 3 ∨ y = -3)) ∧
      ∀ x y : ℤ, y ^ 2 ≠ x ^ 3 - 162

/-- The only non-negative solutions of `3ˣ = y² + 2` are `(x, y) = (1, 1)` and `(3, 5)`.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 8. -/
theorem_wanted three_pow_eq_sq_add_two_iff (x y : ℕ) :
    3 ^ x = y ^ 2 + 2 ↔ (x, y) = (1, 1) ∨ (x, y) = (3, 5)

/-- The only non-negative solutions of `2x² + 1 = 3ʸ` are `(x, y) = (0, 0)`, `(1, 1)`, `(2, 2)`,
`(11, 5)`.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 9. -/
theorem_wanted two_mul_sq_add_one_eq_three_pow_iff (x y : ℕ) :
    2 * x ^ 2 + 1 = 3 ^ y ↔
      (x, y) = (0, 0) ∨ (x, y) = (1, 1) ∨ (x, y) = (2, 2) ∨ (x, y) = (11, 5)

/-- If `p` and `2p - 1` are odd primes, then `pˣ + (2p - 1)ʸ = z²` has the unique non-negative
solution `(p, x, y, z) = (3, 1, 0, 2)`.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 1. -/
theorem_wanted prime_pair_pow_add_pow_eq_sq_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : (2 * p - 1).Prime) (x y z : ℕ) :
    p ^ x + (2 * p - 1) ^ y = z ^ 2 ↔ (p, x, y, z) = (3, 1, 0, 2)

/-- If `p` and `2p - 1` are primes with `p ≡ 5, 7 (mod 8)`, then for every `k ≥ 0`,
`pˣ + (2^{2k+1}(2p - 1))ʸ = z²` has no non-negative solutions.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 2. -/
theorem_wanted prime_pair_pow_add_two_pow_odd_mul_pow_ne_sq {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7) (k x y z : ℕ) :
    p ^ x + (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y ≠ z ^ 2

/-- If `p` and `2p - 1` are primes with `p ≡ 3 (mod 4)` and `k ≥ 1`, then the non-negative
solutions of `pˣ + (2^{2k}(2p - 1))ʸ = z²` are `(p, x, y, z) = (3, 1, 0, 2)` (any `k`) and
`(p, k, x, y, z) = (3, 2, 0, 1, 9)`.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 3. -/
theorem_wanted prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff {p k : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp4 : p % 4 = 3) (hk : 1 ≤ k) (x y z : ℕ) :
    p ^ x + (2 ^ (2 * k) * (2 * p - 1)) ^ y = z ^ 2 ↔
      (p, x, y, z) = (3, 1, 0, 2) ∨ (p, k, x, y, z) = (3, 2, 0, 1, 9)

/-- If `p` and `2p - 1` are primes with `p ≡ 3 (mod 4)`, then the non-negative solutions of
`(2p - 1)ˣ - pʸ = z²` are `(x, y, z) = (0, 0, 0)`, `(p, x, y, z) = (3, 2, 2, 4)`, and
`(p, x, y, z) = (2t² + 1, 1, 0, 2t)` for `t ∈ ℕ` (then `2t² + 1` and `4t² + 1` are the given
primes and `2t² + 1 ≡ 3 (mod 4)`).

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 4. -/
theorem_wanted prime_pair_pow_sub_pow_eq_sq_iff {p : ℕ} (hp : p.Prime) (hq : (2 * p - 1).Prime)
    (hp4 : p % 4 = 3) (x y z : ℕ) :
    (2 * (p : ℤ) - 1) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) ∨ (p, x, y, z) = (3, 2, 2, 4) ∨
        ∃ t : ℕ, p = 2 * t ^ 2 + 1 ∧ x = 1 ∧ y = 0 ∧ z = 2 * t

/-- If `p` and `2p - 1` are primes with `p ≡ 3 (mod 4)` and `k ≥ 1`, then
`(2^{2k}(2p - 1))ˣ - pʸ = z²` has the unique non-negative solution `(x, y, z) = (0, 0, 0)`.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 6. -/
theorem_wanted prime_pair_two_pow_even_mul_pow_sub_pow_eq_sq_iff {p k : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp4 : p % 4 = 3) (hk : 1 ≤ k) (x y z : ℕ) :
    ((2 : ℤ) ^ (2 * k) * (2 * p - 1)) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2 ↔ (x, y, z) = (0, 0, 0)

/-- If `p` and `2p - 1` are primes with `p ≡ 5 (mod 8)` and `k ≥ 0`, then the non-negative
solutions of `(2^{2k+1}(2p - 1))ˣ - pʸ = z²` are `(x, y, z) = (0, 0, 0)` and
`(p, k, x, y, z) = ((t² + 3)/4, 0, 1, 0, t)` for `t ∈ ℕ` (then `(t² + 3)/4` and `(t² + 1)/2` are
the given primes and `(t² + 3)/4 ≡ 5 (mod 8)`).

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 7. -/
theorem_wanted prime_pair_two_pow_odd_mul_pow_sub_pow_eq_sq_iff {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp8 : p % 8 = 5) (k x y z : ℕ) :
    ((2 : ℤ) ^ (2 * k + 1) * (2 * p - 1)) ^ x - (p : ℤ) ^ y = (z : ℤ) ^ 2 ↔
      (x, y, z) = (0, 0, 0) ∨ (4 * p = z ^ 2 + 3 ∧ k = 0 ∧ x = 1 ∧ y = 0)

/-- If `p` and `2p - 1` are primes with `p ≡ 3 (mod 8)` and `k ≥ 0`, then
`pˣ - (2^{2k+1}(2p - 1))ʸ = z²` has the unique non-negative solution `(x, y, z) = (0, 0, 0)`.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 9. -/
theorem_wanted prime_pair_pow_sub_two_pow_odd_mul_pow_eq_sq_iff {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp8 : p % 8 = 3) (k x y z : ℕ) :
    (p : ℤ) ^ x - ((2 : ℤ) ^ (2 * k + 1) * (2 * p - 1)) ^ y = (z : ℤ) ^ 2 ↔ (x, y, z) = (0, 0, 0)

/-- The six equations `(-1)^α 2ˣ + (-1)^β (2ᵏ · 3)ʸ = z²` with `α, β, k ∈ {0, 1}`, `αβ = 0`, have
exactly the listed non-negative solutions `(x, y, z)`.

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

/-- The only non-negative solution of `2 + 7ʸ = z²` is `(y, z) = (1, 3)`.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 11. -/
theorem_wanted two_add_seven_pow_eq_sq_iff (y z : ℕ) : 2 + 7 ^ y = z ^ 2 ↔ (y, z) = (1, 3)

end

end MetaMathlibExt
