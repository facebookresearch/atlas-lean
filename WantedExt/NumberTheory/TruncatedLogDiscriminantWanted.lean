/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Discriminants of truncated logarithmic polynomials

Statements from Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39 (arXiv:2401.14138).
`F_n(x) = 1 + x + x²/2 + ⋯ + xⁿ/n`, `L_n = lcm(1, …, n)`, `F̃_n = L_n F_n ∈ ℤ[x]`,
and `𝒫_n = ∏ F̃_n(θ)` over the roots `θ` of `F_n' = 1 + x + ⋯ + x^{n-1}` (the
source's Equation (5)), here the resultant `Res(1 + x + ⋯ + x^{n-1}, F̃_n)`; by
`Polynomial.resultant_eq_prod_eval` this is that product, since
`1 + x + ⋯ + x^{n-1}` is monic. The discriminant is Mathlib's
`Polynomial.discr`. "Not in `ℚ^{×2}`" is stated as `¬ IsSquare`; the two agree
because these discriminants are nonzero.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Truncated logarithmic polynomial.** For a natural number $n$, the truncated logarithmic
polynomial is $F_n(x) = 1 + x + \frac{x^2}{2} + \dots + \frac{x^n}{n} \in \mathbb{Q}[x]$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public noncomputable def truncatedLogPolynomial (n : ℕ) : ℚ[X] :=
  1 + ∑ j ∈ Finset.Icc 1 n, C ((j : ℚ)⁻¹) * X ^ j

/-- **Least common multiple of $1, \dots, n$.** For a natural number $n$, $L_n$ is the least common
multiple $\operatorname{lcm}(1, 2, \dots, n)$ of the integers from $1$ to $n$; in particular
$L_0 = 1$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public def truncatedLogLcm (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

/-- **Least common multiple of $1, 2, 3, 4$.** The least common multiple of the integers from $1$
to $4$ is $L_4 = \operatorname{lcm}(1, 2, 3, 4) = 12$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public theorem truncatedLogLcm_four : truncatedLogLcm 4 = 12 := by
  decide

/-- **Scaled truncated logarithmic polynomial.** For a natural number $n$, let
$L_n = \operatorname{lcm}(1, 2, \dots, n)$. The scaled truncated logarithmic polynomial is the
integer polynomial $\tilde F_n(x) = L_n + \sum_{j=1}^{n} (L_n / j)\, x^j$, where each quotient
$L_n / j$ is an integer.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public noncomputable def scaledTruncatedLogPolynomial (n : ℕ) : ℤ[X] :=
  C (truncatedLogLcm n : ℤ) + ∑ j ∈ Finset.Icc 1 n, C ((truncatedLogLcm n / j : ℕ) : ℤ) * X ^ j

/-- **The scaled truncated logarithmic polynomial is $L_n F_n$.** For a natural number $n$, let
$L_n = \operatorname{lcm}(1, 2, \dots, n)$, let $F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the
truncated logarithmic polynomial and let $\tilde F_n \in \mathbb{Z}[x]$ be the scaled truncated
logarithmic polynomial. Mapping the coefficients of $\tilde F_n$ from $\mathbb{Z}$ to
$\mathbb{Q}$ gives the polynomial $L_n F_n$ in $\mathbb{Q}[x]$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public theorem map_scaledTruncatedLogPolynomial (n : ℕ) :
    (scaledTruncatedLogPolynomial n).map (Int.castRingHom ℚ) =
      C (truncatedLogLcm n : ℚ) * truncatedLogPolynomial n := by
  simp only [scaledTruncatedLogPolynomial, truncatedLogPolynomial, Polynomial.map_add,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, mul_add, mul_one,
    Finset.mul_sum]
  refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun j hj => ?_)
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj0 : (j : ℚ) ≠ 0 := by positivity
  have hdvd : j ∣ truncatedLogLcm n := Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) hj
  rw [← mul_assoc, ← C_mul]
  congr 2
  simp only [eq_intCast, Int.cast_natCast]
  rw [Nat.cast_div hdvd hj0, div_eq_mul_inv]

/-- **Resultant product for truncated logarithmic polynomials.** For a natural number $n$, let
$F_n(x) = 1 + x + \frac{x^2}{2} + \dots + \frac{x^n}{n}$, let
$L_n = \operatorname{lcm}(1, \dots, n)$, and let $\tilde F_n = L_n F_n \in \mathbb{Z}[x]$. The
integer $\mathcal{P}_n$ is the resultant $\operatorname{Res}(1 + x + \dots + x^{n-1}, \tilde F_n)$.
For $n \ge 1$ the polynomial $1 + x + \dots + x^{n-1} = F_n'$ is monic, so
$\mathcal{P}_n = \prod_{\theta} \tilde F_n(\theta)$, the product over the roots $\theta$ of $F_n'$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Equation (5). -/
public noncomputable def truncatedLogResultantProduct (n : ℕ) : ℤ :=
  resultant (∑ k ∈ Finset.range n, (X : ℤ[X]) ^ k) (scaledTruncatedLogPolynomial n)

/-- **Auxiliary product for truncated logarithmic discriminants.** For a natural number $m$, let
$f_m(x) = \sum_{k=0}^{m-1} x^k$ and $g_m(x) = c_m + \sum_{j=1}^{m-1} \frac{x^j}{j}$ in
$\mathbb{Q}[x]$, where $c_m = \frac{1}{m}$ for $m \ge 1$ and $c_0 = 0$. The rational number $X(m)$
is the resultant $\operatorname{Res}(f_m, g_m)$. For $m \ge 1$, since $f_m$ is monic with roots
$\omega^k$ for $1 \le k \le m-1$, where $\omega$ is a primitive $m$-th root of unity, this is
$X(m) = \prod_{k=1}^{m-1} g_m(\omega^k)$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 4. -/
public noncomputable def truncatedLogAuxProduct (m : ℕ) : ℚ :=
  resultant (∑ k ∈ Finset.range m, (X : ℚ[X]) ^ k)
    (C ((m : ℚ)⁻¹) + ∑ j ∈ Finset.Icc 1 (m - 1), C ((j : ℚ)⁻¹) * X ^ j)

/-- **Auxiliary product at $m = 1$.** The auxiliary product $X(m)$ takes the value $X(1) = 1$ at
$m = 1$; it is an empty product.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 4. -/
public theorem truncatedLogAuxProduct_one : truncatedLogAuxProduct 1 = 1 := by
  simp [truncatedLogAuxProduct]

/-- **Resultant product at $n = 1$.** The resultant product satisfies $\mathcal{P}_1 = 1$; it is an
empty product.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Equation (5). -/
public theorem truncatedLogResultantProduct_one : truncatedLogResultantProduct 1 = 1 := by
  simp [truncatedLogResultantProduct]

/-- **Exceptional primes for truncated logarithmic discriminants.** For a natural number $m$, the
exceptional set $E_m$ is the set of primes $\ell$ with $m\ell \equiv 1 \pmod 4$ such that the
$\ell$-adic valuation of the auxiliary product $X(m)$ is positive or the $\ell$-adic valuation of
the harmonic number $Y(m) = H_m = 1 + \frac{1}{2} + \dots + \frac{1}{m}$ is positive.

The source's display joins the two valuation conditions with "and", but its text ("all prime
divisors of $X(m)$ and $Y(m)$") and its table ($E_3 = \{11\}$ with $11 \nmid X(3) = 13/36$) use
the union.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 4. -/
public def truncatedLogExceptionalPrimes (m : ℕ) : Set ℕ :=
  {ℓ | ℓ.Prime ∧ (0 < padicValRat ℓ (truncatedLogAuxProduct m) ∨
    0 < padicValRat ℓ (_root_.harmonic m)) ∧ m * ℓ % 4 = 1}

/-- **Positivity of the resultant product.** For every natural number $n \ge 1$, the resultant
product $\mathcal{P}_n$ is a positive integer.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Lemma 1
(`integers-2025-A39-lem-1`). -/
public theorem_wanted truncatedLogResultantProduct_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < truncatedLogResultantProduct n

/-- **Nonsquare discriminants of $F_n$ for positive $n \equiv 0, 2, 3 \pmod 4$.** Let
$F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic polynomial and let
$n \ge 1$ be a natural number with $n \equiv 0$, $2$ or $3 \pmod 4$. Then the discriminant of
$F_n$ is not a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Proposition 1
(`integers-2025-A39-prop-1`). -/
public theorem_wanted not_isSquare_discr_truncatedLog_of_mod_four {n : ℕ} (hn : 1 ≤ n)
    (h : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3) :
    ¬ IsSquare (truncatedLogPolynomial n).discr

/-- **Nonsquare discriminants of truncated logarithmic polynomials.** Let
$F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic polynomial and let
$n \ge 1$. If $n \equiv 0$, $2$ or $3 \pmod 4$, or if $n \equiv 1 \pmod 4$ and $n = p^e$ for a
prime $p$ and an odd $e$, then the discriminant of $F_n$ is not a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 1
(`integers-2025-A39-thm-1`). -/
public theorem_wanted not_isSquare_discr_truncatedLog {n : ℕ} (hn : 1 ≤ n)
    (h : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3 ∨
      (n % 4 = 1 ∧ ∃ p e : ℕ, p.Prime ∧ Odd e ∧ n = p ^ e)) :
    ¬ IsSquare (truncatedLogPolynomial n).discr

/-- **An odd prime $p$ does not divide $\mathcal{P}_{p^{2e}}$.** Let $p$ be an odd prime, let
$e \ge 1$, and let $\mathcal{P}_n$ be the truncated logarithmic resultant product. Then $p$ does
not divide $\mathcal{P}_{p^{2e}}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 2
(`integers-2025-A39-thm-2`). -/
public theorem_wanted not_dvd_truncatedLogResultantProduct_of_even_power {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    ¬ (p : ℤ) ∣ truncatedLogResultantProduct (p ^ (2 * e))

/-- **Finiteness of square discriminants of $F_{mq}$ with $mq \equiv 1 \pmod 4$.** Let
$F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic polynomial and let
$m \ge 1$ be a natural number. Then there are only finitely many primes $q$ with
$mq \equiv 1 \pmod 4$ such that the discriminant of $F_{mq}$ is a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 3
(`integers-2025-A39-thm-3`). -/
public theorem_wanted finite_primes_isSquare_discr_truncatedLog {m : ℕ} (hm : 1 ≤ m) :
    {q : ℕ | q.Prime ∧ m * q % 4 = 1 ∧ IsSquare (truncatedLogPolynomial (m * q)).discr}.Finite

/-- **A prime $p \equiv 1 \pmod 4$ does not divide $\mathcal{P}_{p^e}$.** Let $p$ be a prime with
$p \equiv 1 \pmod 4$, let $e \ge 1$, and let $\mathcal{P}_n$ be the truncated logarithmic
resultant product. Then $p$ does not divide $\mathcal{P}_{p^e}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 4
(`integers-2025-A39-thm-4`). -/
public theorem_wanted not_dvd_truncatedLogResultantProduct_of_prime_power {p e : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (he : 1 ≤ e) :
    ¬ (p : ℤ) ∣ truncatedLogResultantProduct (p ^ e)

/-- **Discriminants of $F_{p^e}$ for primes $p \equiv 1 \pmod 4$.** Let $p$ be a prime with
$p \equiv 1 \pmod 4$, let $e \ge 1$, let $F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the
truncated logarithmic polynomial and let $\mathcal{P}_n$ be the truncated logarithmic resultant
product. If $e$ is odd, the discriminant of $F_{p^e}$ is not a square in $\mathbb{Q}$. If $e$ is
even, the discriminant of $F_{p^e}$ is not a square in $\mathbb{Q}$ if and only if the integer
$\mathcal{P}_{p^e}$ is not a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Corollary 1
(`integers-2025-A39-cor-1`). -/
public theorem_wanted discr_truncatedLog_prime_power {p e : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (he : 1 ≤ e) :
    (Odd e → ¬ IsSquare (truncatedLogPolynomial (p ^ e)).discr) ∧
      (Even e → (¬ IsSquare (truncatedLogPolynomial (p ^ e)).discr ↔
        ¬ IsSquare ((truncatedLogResultantProduct (p ^ e) : ℤ) : ℚ)))

/-- **Nonsquare discriminants of $F_{mq}$ for non-exceptional primes $q > m$.** Let $m$ be a
natural number, let $E_m$ be the set of exceptional primes for truncated logarithmic
discriminants, and let $F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic
polynomial. If $q$ is a prime with $q \notin E_m$, $q > m$ and $mq \equiv 1 \pmod 4$, then the
discriminant of $F_{mq}$ is not a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 5
(`integers-2025-A39-thm-5`). -/
public theorem_wanted not_isSquare_discr_truncatedLog_mul_prime {m q : ℕ} (hq : q.Prime)
    (hE : q ∉ truncatedLogExceptionalPrimes m) (hmq : m < q) (h4 : m * q % 4 = 1) :
    ¬ IsSquare (truncatedLogPolynomial (m * q)).discr

/-- **Nonsquare discriminants of $F_{3q}$, $F_{5q}$ and $F_{7q}$.** Let
$F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic polynomial. For every
prime $q$, if $n = 3q$, $n = 5q$ or $n = 7q$, then the discriminant of $F_n$ is not a square in
$\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Proposition 2
(`integers-2025-A39-prop-2`). -/
public theorem_wanted not_isSquare_discr_truncatedLog_three_five_seven_mul {q n : ℕ}
    (hq : q.Prime) (hn : n = 3 * q ∨ n = 5 * q ∨ n = 7 * q) :
    ¬ IsSquare (truncatedLogPolynomial n).discr

end

end MetaMathlibExt
