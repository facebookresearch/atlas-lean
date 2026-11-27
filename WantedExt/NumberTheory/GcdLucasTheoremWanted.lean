/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational
public import MathlibExt.NumberTheory.ChoosePowMulModEq
public import MathlibExt.NumberTheory.ExistsUniqueRadicalExpansionCoeffs
public import MathlibExt.NumberTheory.GcdPowAddNegOnePow
public import MathlibExt.NumberTheory.PrimeDvdChoosePowMulPowMul
public import MathlibExt.NumberTheory.PrimeDvdOfDvdRadicalCoeffsGcd
public import MathlibExt.NumberTheory.PrimeDvdPowAddOfDvdRadicalCoeffsGcd
public import MathlibExt.NumberTheory.RadicalCoefficientCommonPrime
public import MathlibExt.NumberTheory.RadicalCoefficientGcdStep
public import MathlibExt.NumberTheory.GcdLucasTheoremGcdRadicalExpansionCoeffsEqOne
public import MathlibExt.NumberTheory.GcdLucasTheoremGcdSqrtExpansionCoeffs

/-!
# Greatest common divisors of radical-expansion coefficients and Lucas's theorem

Statements from John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2. Write
`(u + v^{1/N})^n = a_{n,0} + a_{n,1} v^{1/N} + ⋯ + a_{n,N-1} v^{(N-1)/N}` with integer
coefficients; the statements below take the coefficient family as a hypothesis-constrained
function, as the paper does, with `v^{1/N}` the real `Real.rpow` root and `v^{i/N}` its
`i`-th power. Lucas's theorem itself is Mathlib's `Choose.choose_modEq_prod_range_choose_nat`;
Corollaries 12 and 13 follow from `Choose.choose_modEq_choose_mod_mul_choose_div_nat` in a few
lines and are not restated.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Gcd of the coefficients of $(u + v^{1/p})^n$ for an odd prime $p$.** Let $p$ be an odd
prime, let $u, v$ be coprime positive integers such that $\theta = v^{1/p}$, the positive real
$p$-th root of $v$, is irrational, and let $a_{n,i}$ (for natural $n$ and $0 \le i \le p - 1$) be
integers with $(u + \theta)^n = \sum_{i=0}^{p-1} a_{n,i} \theta^i$ for every $n \ge 1$. Write
$D_n$ for the nonnegative greatest common divisor of $a_{n,0}, \dots, a_{n,p-1}$. Then:
(a) if $p \nmid u^p + v$, then $D_n = 1$ for every $n \ge 1$;
(b) if $u^p + v = mp$ for a natural number $m$ with $p \nmid m$, then $D_{np+i} = p^n$ for all
natural numbers $n, i$ with $i \le p - 1$ and $np + i \ge 1$;
(c) if $p^2 \mid u^p + v$, then $D_{n(p-1)+i} = p^n$ for all natural numbers $n, i$ with
$1 \le i \le p - 1$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Theorem 18
(`jis-2025-25.2.2-thm-18`). -/
public theorem_wanted gcd_prime_root_expansion_coeffs {p u v : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hu : 0 < u) (hv : 0 < v) (huv : u.Coprime v)
    (hirr : Irrational ((v : ℝ) ^ (1 / (p : ℝ)))) (a : ℕ → Fin p → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (p : ℝ))) ^ n =
      ∑ i : Fin p, (a n i : ℝ) * ((v : ℝ) ^ (1 / (p : ℝ))) ^ (i : ℕ)) :
    (¬p ∣ u ^ p + v → ∀ n, 1 ≤ n → Finset.univ.gcd (a n) = 1) ∧
    (∀ m : ℕ, u ^ p + v = m * p → ¬p ∣ m → ∀ n i : ℕ, i ≤ p - 1 → 1 ≤ n * p + i →
      Finset.univ.gcd (a (n * p + i)) = (p : ℤ) ^ n) ∧
    (p ^ 2 ∣ u ^ p + v → ∀ n i : ℕ, 1 ≤ i → i ≤ p - 1 →
      Finset.univ.gcd (a (n * (p - 1) + i)) = (p : ℤ) ^ n)

/-- **Coprime coefficients when $u^N + (-1)^{N+1} v$ is coprime to $N$.** Let $N \ge 2$, let
$u, v$ be coprime natural numbers such that $x^N - v$ is irreducible over $\mathbb{Q}$, let
$\theta = v^{1/N}$ be the nonnegative real $N$-th root of $v$, and let $a_{n,i}$ (for natural $n$
and $0 \le i \le N - 1$) be integers with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$
for every $n \ge 1$. If $u^N + (-1)^{N+1} v$ and $N$ are coprime integers, then for every
$n \ge 1$ the greatest common divisor of $a_{n,0}, \dots, a_{n,N-1}$ is $1$.

The paper assumes $N \ge 4$; the cases $N = 2, 3$ also hold, while $N = 1$ fails.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Corollary 9
(`jis-2025-25.2.2-cor-9`). -/
public theorem_wanted gcd_radical_expansion_coeffs_eq_one_of_coprime {N u v : ℕ} (hN : 2 ≤ N)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (hM : IsCoprime ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) (N : ℤ)) (n : ℕ) (hn : 1 ≤ n) :
    Finset.univ.gcd (a n) = 1

end

end MetaMathlibExt
