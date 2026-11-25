/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import MathlibExt.NumberTheory.CotangentPowerSums

namespace MetaMathlibExt

@[expose] public section

/-- **Cotangent powers through cotangent derivatives.** Let $c_{r,j}$ be Girstmair's cotangent
power coefficients and $\cot^{(m)}$ the $m$-th derivative of the real cotangent function. For
every natural number $r \ge 1$ and every real number $x$ with $\sin x \ne 0$,
$$(i \cot x)^r = \frac{(-1)^r + 1}{2} + \sum_{j=1}^{r} c_{r,j} \, i^j \cot^{(j-1)}(x).$$

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Proposition 1 (`integers-2025-A63-prop-1`). -/
public theorem_wanted I_mul_cot_pow_eq_sum_iteratedDeriv_cot (r : ℕ) (hr : 1 ≤ r) (x : ℝ)
    (hx : Real.sin x ≠ 0) :
    (Complex.I * Real.cot x) ^ r = ((-1) ^ r + 1) / 2 +
      ∑ j ∈ Finset.Icc 1 r, (cotangentPowerCoeff r j : ℂ) * Complex.I ^ j *
        ((iteratedDeriv (j - 1) Real.cot x : ℝ) : ℂ)

/-- **Girstmair's cotangent power sums, odd case.** Let $n \ge 2$, let $r$ be odd, and let $\chi$
be a complex Dirichlet character modulo $n$ with $\chi(-1) = -1$. Let $f$ be the conductor of
$\chi$, $\chi_f$ the primitive character modulo $f$ attached to $\chi$, and $c_{r,j}$
Girstmair's cotangent power coefficients. Write
$\tau(\overline{\chi_f}) = \sum_{k=1}^{f} \overline{\chi_f(k)} e^{2 \pi i k/f}$ for the Gauss sum
and $B_{j,\chi_f} = f^{j-1} \sum_{k=1}^{f} B_j(k/f) \chi_f(k)$, where $B_j$ is the $j$-th
Bernoulli polynomial. Then
$$\sum_{k} \overline{\chi(k)} \left(i \cot \frac{\pi k}{n}\right)^r = -\tau(\overline{\chi_f})
\sum_{j} \frac{c_{r,j} (2n)^j}{j f^j}
\prod_{p \mid n} \Bigl(1 - \frac{\overline{\chi_f(p)}}{p^j}\Bigr) B_{j,\chi_f},$$
where $k$ runs over $1 \le k \le n$ with $\gcd(k, n) = 1$, $j$ runs over the odd numbers with
$1 \le j \le r$, and $p$ runs over the primes dividing $n$.

The left side is $\tau(\overline{\chi_f})$ times the character coordinate
$y(\chi \mid i^r \cot^r(\pi/n))$ of the source, defined by Equation (3), since
$\sigma_k(i^r \cot^r(\pi/n)) = i^r \cot^r(\pi k/n)$ (Equation (4)).

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Theorem 1, first case (`integers-2025-A63-thm-1`). -/
public theorem_wanted sum_conj_dirichletCharacter_mul_I_mul_cot_pow_of_odd {n : ℕ} (hn : 2 ≤ n)
    {r : ℕ} (hr : Odd r) (χ : DirichletCharacter ℂ n) (hχ : χ (-1) = -1) :
    ∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n),
        starRingEnd ℂ (χ k) * (Complex.I * Real.cot (Real.pi * k / n)) ^ r =
      (∑ k ∈ Finset.Icc 1 χ.conductor, starRingEnd ℂ (χ.primitiveCharacter k) *
          Complex.exp (2 * Real.pi * Complex.I * k / χ.conductor)) *
        -∑ j ∈ (Finset.Icc 1 r).filter Odd,
          (cotangentPowerCoeff r j : ℂ) * (2 * n : ℂ) ^ j / (j * (χ.conductor : ℂ) ^ j) *
            (∏ p ∈ n.primeFactors,
              (1 - starRingEnd ℂ (χ.primitiveCharacter p) / (p : ℂ) ^ j)) *
            ((χ.conductor : ℂ) ^ (j - 1) * ∑ k ∈ Finset.Icc 1 χ.conductor,
              (((Polynomial.bernoulli j).eval ((k : ℚ) / χ.conductor) : ℚ) : ℂ) *
                χ.primitiveCharacter k)

open Classical in
/-- **Girstmair's cotangent power sums, even case.** Let $n \ge 2$, let $r \ge 2$ be even, and let
$\chi$ be a complex Dirichlet character modulo $n$ with $\chi(-1) = 1$. Let $f$ be the conductor
of $\chi$, $\chi_f$ the primitive character modulo $f$ attached to $\chi$, and $c_{r,j}$
Girstmair's cotangent power coefficients. Write
$\tau(\overline{\chi_f}) = \sum_{k=1}^{f} \overline{\chi_f(k)} e^{2 \pi i k/f}$ for the Gauss sum,
$B_{j,\chi_f} = f^{j-1} \sum_{k=1}^{f} B_j(k/f) \chi_f(k)$, where $B_j$ is the $j$-th Bernoulli
polynomial, and $\varepsilon_\chi = \varphi(n)$ if $\chi$ is the principal character modulo $n$
and $\varepsilon_\chi = 0$ otherwise. Then
$$\sum_{k} \overline{\chi(k)} \left(i \cot \frac{\pi k}{n}\right)^r = \tau(\overline{\chi_f}) \,
\Bigl(\varepsilon_\chi + \sum_{j} \frac{c_{r,j} (2n)^j}{j f^j}
\prod_{p \mid n} \Bigl(1 - \frac{\overline{\chi_f(p)}}{p^j}\Bigr) B_{j,\chi_f}\Bigr),$$
where $k$ runs over $1 \le k \le n$ with $\gcd(k, n) = 1$, $j$ runs over the even numbers with
$1 \le j \le r$, and $p$ runs over the primes dividing $n$.

The left side is $\tau(\overline{\chi_f})$ times the character coordinate
$y(\chi \mid i^r \cot^r(\pi/n))$ of the source (Equation (3)), and $\varepsilon_\chi$ is
$y(\chi \mid 1)$ (Equation (11)).

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Theorem 1, second case (`integers-2025-A63-thm-1`). -/
public theorem_wanted sum_conj_dirichletCharacter_mul_I_mul_cot_pow_of_even {n : ℕ} (hn : 2 ≤ n)
    {r : ℕ} (hr0 : r ≠ 0) (hr : Even r) (χ : DirichletCharacter ℂ n) (hχ : χ (-1) = 1) :
    ∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n),
        starRingEnd ℂ (χ k) * (Complex.I * Real.cot (Real.pi * k / n)) ^ r =
      (∑ k ∈ Finset.Icc 1 χ.conductor, starRingEnd ℂ (χ.primitiveCharacter k) *
          Complex.exp (2 * Real.pi * Complex.I * k / χ.conductor)) *
        ((if χ = 1 then (n.totient : ℂ) else 0) +
          ∑ j ∈ (Finset.Icc 1 r).filter Even,
            (cotangentPowerCoeff r j : ℂ) * (2 * n : ℂ) ^ j / (j * (χ.conductor : ℂ) ^ j) *
              (∏ p ∈ n.primeFactors,
                (1 - starRingEnd ℂ (χ.primitiveCharacter p) / (p : ℂ) ^ j)) *
              ((χ.conductor : ℂ) ^ (j - 1) * ∑ k ∈ Finset.Icc 1 χ.conductor,
                (((Polynomial.bernoulli j).eval ((k : ℚ) / χ.conductor) : ℚ) : ℂ) *
                  χ.primitiveCharacter k))

/-- **Cotangent power coefficients through even Bernoulli numbers.** Let $c_{r,j}$ be
Girstmair's cotangent power coefficients and $B_m$ the $m$-th Bernoulli number. For natural
numbers $j$ and $r$ with $1 \le j \le r$ and $j \equiv r \pmod 2$,
$$c_{r,j} = \frac{(-1)^{r+1} 2^{r-j}}{(j-1)!} \, d_{r,j},$$
where
$$d_{r,j} = \sum_{(j_1, \dots, j_r)} \prod_{t=1}^{r} \frac{B_{2 j_t}}{(2 j_t)!}$$
and the sum runs over all $r$-tuples $(j_1, \dots, j_r)$ of natural numbers with
$j + 2 j_1 + \dots + 2 j_r = r$. This is Theorem 2 of the source, relating $c_{r,j}$ to the
coefficients $d_{r,j}$ of the earlier literature (Equations (13) and (15)).

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Theorem 2 with Equations (13) and (15) (`integers-2025-A63-thm-2`). -/
public theorem_wanted cotangentPowerCoeff_eq_bernoulli_tuple_sum {r j : ℕ} (hj : 1 ≤ j)
    (hjr : j ≤ r) (hpar : j % 2 = r % 2) :
    cotangentPowerCoeff r j =
      (-1) ^ (r + 1) * 2 ^ (r - j) / ((j - 1).factorial : ℚ) *
        ∑ a ∈ Finset.Nat.antidiagonalTuple r ((r - j) / 2),
          ∏ t, bernoulli (2 * a t) / ((2 * a t).factorial : ℚ)

end

end MetaMathlibExt
