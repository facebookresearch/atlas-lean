/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Lemma 2 (`MetaMathlibExt.sq_add_add_one_eq_three_mul_cube_iff`) is proved in
`MathlibExt.NumberTheory.SqAddAddOneEqThreeMulCube`. Lemma 4
(`MetaMathlibExt.gcd_sub_one_sq_add_add_one`) is proved in
`MathlibExt.NumberTheory.CubeFactorGCD`. Lemma 5 (`MetaMathlibExt.cube_sub_cube_eq_two_or_one_iff`)
is proved in `MathlibExt.NumberTheory.CubeSubCube`. Lemma 8
(`MetaMathlibExt.cube_sub_mul_cube_eq_one_iff_of_mem`) is proved in
`MathlibExt.NumberTheory.CubeSubMulCube`.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.NumberTheory.CoprimePrimeSquareCubeSplit
public import MathlibExt.NumberTheory.CubeFactorGCD
public import MathlibExt.NumberTheory.CubeSubCube
public import MathlibExt.NumberTheory.CubeSubMulCube
public import MathlibExt.NumberTheory.CubeSubTwoMulCube
public import MathlibExt.NumberTheory.PrimeGCDCubeSplit
public import MathlibExt.NumberTheory.SqAddAddOneEqThreeMulCube

namespace MetaMathlibExt

@[expose] public section

/-- **When $u^2 \pm u + 1$ is a cube.** For every integer $u$, $u^2 + u + 1$ is the cube of an
integer if and only if $u \in \{-19, -1, 0, 18\}$, and $u^2 - u + 1$ is the cube of an integer
if and only if $u \in \{-18, 0, 1, 19\}$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 3
(`integers-2025-A103-lem-3`). -/
public theorem_wanted sq_add_add_one_eq_cube_iff (u : ℤ) :
    ((∃ v : ℤ, u ^ 2 + u + 1 = v ^ 3) ↔ u = -19 ∨ u = -1 ∨ u = 0 ∨ u = 18) ∧
      ((∃ v : ℤ, u ^ 2 - u + 1 = v ^ 3) ↔ u = -18 ∨ u = 0 ∨ u = 1 ∨ u = 19)

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
