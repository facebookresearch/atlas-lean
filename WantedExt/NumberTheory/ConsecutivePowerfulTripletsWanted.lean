/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Prime.Defs

namespace MetaMathlibExt

@[expose] public section

/-- Coprime splitting: if `R * S = p ^ 2 * C ^ 3` for a prime `p` and
`gcd(R, S) = 1`, then one of `R`, `S` is a perfect cube and the other is `p ^ 2`
times a perfect cube.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 1
(`integers-2025-A103-lem-1`). -/
public theorem_wanted cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_eq_one
    {p : ℕ} (hp : p.Prime) {R S C : ℤ} (h : R * S = (p : ℤ) ^ 2 * C ^ 3)
    (hg : Int.gcd R S = 1) :
    ∃ C₁ C₂ : ℤ, (R = C₁ ^ 3 ∧ S = (p : ℤ) ^ 2 * C₂ ^ 3) ∨
      (R = (p : ℤ) ^ 2 * C₁ ^ 3 ∧ S = C₂ ^ 3)

/-- Prime-gcd splitting: if `R * S = p ^ 2 * C ^ 3` for a prime `p` and
`g = gcd(R, S)` is prime, then for some integers `C₁`, `C₂` either
`(R, S) = (g C₁³, g C₂³)`, or `{R, S} = {g C₁³, g² p² C₂³}`, or
`{R, S} = {g p² C₁³, g² C₂³}` (unordered pairs written out in both orders).

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 1
(`integers-2025-A103-lem-1`). -/
public theorem_wanted cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_prime
    {p : ℕ} (hp : p.Prime) {R S C : ℤ} (h : R * S = (p : ℤ) ^ 2 * C ^ 3)
    (hg : (Int.gcd R S).Prime) :
    ∃ C₁ C₂ : ℤ,
      (R = (Int.gcd R S : ℤ) * C₁ ^ 3 ∧ S = (Int.gcd R S : ℤ) * C₂ ^ 3) ∨
      (R = (Int.gcd R S : ℤ) * C₁ ^ 3 ∧
        S = (Int.gcd R S : ℤ) ^ 2 * (p : ℤ) ^ 2 * C₂ ^ 3) ∨
      (S = (Int.gcd R S : ℤ) * C₁ ^ 3 ∧
        R = (Int.gcd R S : ℤ) ^ 2 * (p : ℤ) ^ 2 * C₂ ^ 3) ∨
      (R = (Int.gcd R S : ℤ) * (p : ℤ) ^ 2 * C₁ ^ 3 ∧
        S = (Int.gcd R S : ℤ) ^ 2 * C₂ ^ 3) ∨
      (S = (Int.gcd R S : ℤ) * (p : ℤ) ^ 2 * C₁ ^ 3 ∧
        R = (Int.gcd R S : ℤ) ^ 2 * C₂ ^ 3)

/-- The equation `u² + u + 1 = 3 v³` has exactly the integer solutions
`(-2, 1)` and `(1, 1)`, and `u² - u + 1 = 3 v³` has exactly `(2, 1)` and
`(-1, 1)`.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 2
(`integers-2025-A103-lem-2`). -/
public theorem_wanted sq_add_add_one_eq_three_mul_cube_iff (u v : ℤ) :
    (u ^ 2 + u + 1 = 3 * v ^ 3 ↔ (u, v) = (-2, 1) ∨ (u, v) = (1, 1)) ∧
      (u ^ 2 - u + 1 = 3 * v ^ 3 ↔ (u, v) = (2, 1) ∨ (u, v) = (-1, 1))

/-- `u² + u + 1` is a perfect cube exactly for `u ∈ {-19, -1, 0, 18}`, and
`u² - u + 1` is a perfect cube exactly for `u ∈ {-18, 0, 1, 19}`.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 3
(`integers-2025-A103-lem-3`). -/
public theorem_wanted sq_add_add_one_eq_cube_iff (u : ℤ) :
    ((∃ v : ℤ, u ^ 2 + u + 1 = v ^ 3) ↔ u = -19 ∨ u = -1 ∨ u = 0 ∨ u = 18) ∧
      ((∃ v : ℤ, u ^ 2 - u + 1 = v ^ 3) ↔ u = -18 ∨ u = 0 ∨ u = 1 ∨ u = 19)

/-- For every integer `x`, `gcd(x - 1, x² + x + 1) = gcd(x - 1, 3)` and
`gcd(x + 1, x² - x + 1) = gcd(x + 1, 3)`.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 4
(`integers-2025-A103-lem-4`). -/
public theorem_wanted gcd_sub_one_sq_add_add_one (x : ℤ) :
    Int.gcd (x - 1) (x ^ 2 + x + 1) = Int.gcd (x - 1) 3 ∧
      Int.gcd (x + 1) (x ^ 2 - x + 1) = Int.gcd (x + 1) 3

/-- `u³ - v³ = 2` has the unique integer solution `(1, -1)`, and `u³ - v³ = 1`
has exactly the integer solutions `(1, 0)` and `(0, -1)`.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 5
(`integers-2025-A103-lem-5`). -/
public theorem_wanted cube_sub_cube_eq_two_or_one_iff (u v : ℤ) :
    (u ^ 3 - v ^ 3 = 2 ↔ (u, v) = (1, -1)) ∧
      (u ^ 3 - v ^ 3 = 1 ↔ (u, v) = (1, 0) ∨ (u, v) = (0, -1))

/-- The only integer solutions of `u³ - 2 v³ = 1` are `(1, 0)` and `(-1, -1)`.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 7
(`integers-2025-A103-lem-7`). -/
public theorem_wanted cube_sub_two_mul_cube_eq_one_iff (u v : ℤ) :
    u ^ 3 - 2 * v ^ 3 = 1 ↔ (u, v) = (1, 0) ∨ (u, v) = (-1, -1)

/-- For `d ∈ {4, 18, 36}`, the equation `u³ - d v³ = 1` has the unique integer
solution `(1, 0)`.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 8
(`integers-2025-A103-lem-8`). -/
public theorem_wanted cube_sub_mul_cube_eq_one_iff_of_mem {d : ℤ}
    (hd : d = 4 ∨ d = 18 ∨ d = 36) (u v : ℤ) :
    u ^ 3 - d * v ^ 3 = 1 ↔ (u, v) = (1, 0)

/-- There are no integers `x, a, b` and primes `p, q` with `x³ - 1 = p² a³` and
`x³ + 1 = q² b³`; as in the paper, `x`, `a`, `b` range over all integers (no
positivity assumption).

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Theorem 1
(`integers-2025-A103-thm-1`). -/
public theorem_wanted not_cube_sub_one_eq_prime_sq_mul_cube_and_cube_add_one
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (x a b : ℤ) :
    ¬ (x ^ 3 - 1 = (p : ℤ) ^ 2 * a ^ 3 ∧ x ^ 3 + 1 = (q : ℤ) ^ 2 * b ^ 3)

/-- For primes `p, q` and integers `x`, `a` with `a ≠ 0`,
`x⁶ - 1 ≠ p² q² a³`.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Corollary 1
(`integers-2025-A103-cor-1`). -/
public theorem_wanted pow_six_sub_one_ne_prime_sq_mul_prime_sq_mul_cube
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (x a : ℤ) (ha : a ≠ 0) :
    x ^ 6 - 1 ≠ (p : ℤ) ^ 2 * (q : ℤ) ^ 2 * a ^ 3

end

end MetaMathlibExt
