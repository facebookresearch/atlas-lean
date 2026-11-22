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

/-- **Splitting $RS = p^2 C^3$ when $R$ and $S$ are coprime.** Let $p$ be a prime and let $R$,
$S$, $C$ be integers with $RS = p^2 C^3$ and $\gcd(R, S) = 1$. Then there are integers $C_1$,
$C_2$ such that either $R = C_1^3$ and $S = p^2 C_2^3$, or $R = p^2 C_1^3$ and $S = C_2^3$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 1
(`integers-2025-A103-lem-1`). -/
public theorem_wanted cube_split_of_mul_eq_prime_sq_mul_cube_of_gcd_eq_one
    {p : ℕ} (hp : p.Prime) {R S C : ℤ} (h : R * S = (p : ℤ) ^ 2 * C ^ 3)
    (hg : Int.gcd R S = 1) :
    ∃ C₁ C₂ : ℤ, (R = C₁ ^ 3 ∧ S = (p : ℤ) ^ 2 * C₂ ^ 3) ∨
      (R = (p : ℤ) ^ 2 * C₁ ^ 3 ∧ S = C₂ ^ 3)

/-- **Splitting $RS = p^2 C^3$ when $\gcd(R, S)$ is prime.** Let $p$ be a prime and let $R$, $S$,
$C$ be integers with $RS = p^2 C^3$ such that $g = \gcd(R, S)$ is prime. Then there are
integers $C_1$, $C_2$ such that one of the following holds: $R = g C_1^3$ and $S = g C_2^3$;
or $R = g C_1^3$ and $S = g^2 p^2 C_2^3$; or $S = g C_1^3$ and $R = g^2 p^2 C_2^3$; or
$R = g p^2 C_1^3$ and $S = g^2 C_2^3$; or $S = g p^2 C_1^3$ and $R = g^2 C_2^3$.

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

/-- **Integer solutions of $u^2 \pm u + 1 = 3v^3$.** For all integers $u$ and $v$,
$u^2 + u + 1 = 3v^3$ if and only if $(u, v) = (-2, 1)$ or $(u, v) = (1, 1)$, and
$u^2 - u + 1 = 3v^3$ if and only if $(u, v) = (2, 1)$ or $(u, v) = (-1, 1)$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 2
(`integers-2025-A103-lem-2`). -/
public theorem_wanted sq_add_add_one_eq_three_mul_cube_iff (u v : ℤ) :
    (u ^ 2 + u + 1 = 3 * v ^ 3 ↔ (u, v) = (-2, 1) ∨ (u, v) = (1, 1)) ∧
      (u ^ 2 - u + 1 = 3 * v ^ 3 ↔ (u, v) = (2, 1) ∨ (u, v) = (-1, 1))

/-- **When $u^2 \pm u + 1$ is a cube.** For every integer $u$, $u^2 + u + 1$ is the cube of an
integer if and only if $u \in \{-19, -1, 0, 18\}$, and $u^2 - u + 1$ is the cube of an integer
if and only if $u \in \{-18, 0, 1, 19\}$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 3
(`integers-2025-A103-lem-3`). -/
public theorem_wanted sq_add_add_one_eq_cube_iff (u : ℤ) :
    ((∃ v : ℤ, u ^ 2 + u + 1 = v ^ 3) ↔ u = -19 ∨ u = -1 ∨ u = 0 ∨ u = 18) ∧
      ((∃ v : ℤ, u ^ 2 - u + 1 = v ^ 3) ↔ u = -18 ∨ u = 0 ∨ u = 1 ∨ u = 19)

/-- **The gcd of $x \mp 1$ and $x^2 \pm x + 1$.** For every integer $x$,
$\gcd(x - 1, x^2 + x + 1) = \gcd(x - 1, 3)$ and $\gcd(x + 1, x^2 - x + 1) = \gcd(x + 1, 3)$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 4
(`integers-2025-A103-lem-4`). -/
public theorem_wanted gcd_sub_one_sq_add_add_one (x : ℤ) :
    Int.gcd (x - 1) (x ^ 2 + x + 1) = Int.gcd (x - 1) 3 ∧
      Int.gcd (x + 1) (x ^ 2 - x + 1) = Int.gcd (x + 1) 3

/-- **Integer solutions of $u^3 - v^3 = 2$ and $u^3 - v^3 = 1$.** For all integers $u$ and $v$,
$u^3 - v^3 = 2$ if and only if $(u, v) = (1, -1)$, and $u^3 - v^3 = 1$ if and only if
$(u, v) = (1, 0)$ or $(u, v) = (0, -1)$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 5
(`integers-2025-A103-lem-5`). -/
public theorem_wanted cube_sub_cube_eq_two_or_one_iff (u v : ℤ) :
    (u ^ 3 - v ^ 3 = 2 ↔ (u, v) = (1, -1)) ∧
      (u ^ 3 - v ^ 3 = 1 ↔ (u, v) = (1, 0) ∨ (u, v) = (0, -1))

/-- **Integer solutions of $u^3 - 2v^3 = 1$.** For all integers $u$ and $v$, $u^3 - 2v^3 = 1$ if
and only if $(u, v) = (1, 0)$ or $(u, v) = (-1, -1)$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 7
(`integers-2025-A103-lem-7`). -/
public theorem_wanted cube_sub_two_mul_cube_eq_one_iff (u v : ℤ) :
    u ^ 3 - 2 * v ^ 3 = 1 ↔ (u, v) = (1, 0) ∨ (u, v) = (-1, -1)

/-- **Integer solutions of $u^3 - d v^3 = 1$ for $d \in \{4, 18, 36\}$.** Let $d$ be one of the
integers $4$, $18$, $36$. For all integers $u$ and $v$, $u^3 - d v^3 = 1$ if and only if
$(u, v) = (1, 0)$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 8
(`integers-2025-A103-lem-8`). -/
public theorem_wanted cube_sub_mul_cube_eq_one_iff_of_mem {d : ℤ}
    (hd : d = 4 ∨ d = 18 ∨ d = 36) (u v : ℤ) :
    u ^ 3 - d * v ^ 3 = 1 ↔ (u, v) = (1, 0)

/-- **$x^3 - 1$ and $x^3 + 1$ are not both a prime square times a cube.** There are no primes
$p$, $q$ and integers $x$, $a$, $b$ with $x^3 - 1 = p^2 a^3$ and $x^3 + 1 = q^2 b^3$.

As in the paper, $x$, $a$, $b$ range over all integers, with no positivity assumption.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Theorem 1
(`integers-2025-A103-thm-1`). -/
public theorem_wanted not_cube_sub_one_eq_prime_sq_mul_cube_and_cube_add_one
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (x a b : ℤ) :
    ¬ (x ^ 3 - 1 = (p : ℤ) ^ 2 * a ^ 3 ∧ x ^ 3 + 1 = (q : ℤ) ^ 2 * b ^ 3)

/-- **$x^6 - 1$ is not $p^2 q^2$ times a nonzero cube.** For all primes $p$, $q$ and all integers
$x$ and $a$ with $a \ne 0$, $x^6 - 1 \ne p^2 q^2 a^3$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Corollary 1
(`integers-2025-A103-cor-1`). -/
public theorem_wanted pow_six_sub_one_ne_prime_sq_mul_prime_sq_mul_cube
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (x a : ℤ) (ha : a ≠ 0) :
    x ^ 6 - 1 ≠ (p : ℤ) ^ 2 * (q : ℤ) ^ 2 * a ^ 3

end

end MetaMathlibExt
