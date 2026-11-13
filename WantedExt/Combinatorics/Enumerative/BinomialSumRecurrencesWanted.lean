/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Data.Nat.Fib.Basic

/-!
# Recurrences for step-`k` sums of binomial coefficients and Riordan arrays

Statements from Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial
Coefficients and Some Generalizations*, Journal of Integer Sequences 27 (2024),
Article 24.3.4. Corollary 3 is already proved as
`Polynomial.exists_polynomial_multiple_supported_on_multiples`
(`MathlibExt/Algebra/Polynomial/SupportedMultiple.lean`).
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Finite window criterion for linear recurrences.** Let $R$ be a commutative ring, let
$x, A, a : \mathbb{N} \to R$ and let $r, s, N \in \mathbb{N}$. Suppose that
$x_n = \sum_{i=1}^{r} A_i x_{n-i}$ for all $n \ge r$, that $N \ge r + s - 1$, and that
$x_n = \sum_{i=1}^{s} a_i x_{n-i}$ for all $n$ with $s \le n \le N$. Then
$x_n = \sum_{i=1}^{s} a_i x_{n-i}$ for all $n \ge s$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 1. -/
public theorem_wanted linearRecurrence_of_finite_window {R : Type*} [CommRing R]
    (x A a : ℕ → R) (r s N : ℕ)
    (hA : ∀ n, r ≤ n → x n = ∑ i ∈ Finset.Icc 1 r, A i * x (n - i))
    (hN : r + s - 1 ≤ N)
    (ha : ∀ n, s ≤ n → n ≤ N → x n = ∑ i ∈ Finset.Icc 1 s, a i * x (n - i)) :
    ∀ n, s ≤ n → x n = ∑ i ∈ Finset.Icc 1 s, a i * x (n - i)

/-- **Roots-of-unity products of integer polynomials.** Let $f \in \mathbb{Z}[x]$ have degree
$r$, let $k > 0$ be a natural number and let $\omega = e^{2\pi i/k}$. Then there are
$G, T \in \mathbb{Z}[x]$ such that $G(x) = f(\omega x) f(\omega^2 x) \cdots f(\omega^{k-1} x)$
as polynomials over $\mathbb{C}$, $T$ has degree $r$, and $f(x) G(x) = T(x^k)$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 2. -/
public theorem_wanted rootsOfUnity_product_mul_eq_comp_pow (f : ℤ[X]) (r k : ℕ) (hk : 0 < k)
    (hf : f.degree = r) :
    ∃ G T : ℤ[X],
      G.map (Int.castRingHom ℂ) =
        ∏ j ∈ Finset.Ico 1 k,
          (f.map (Int.castRingHom ℂ)).comp
            (C (Complex.exp (2 * Real.pi * Complex.I / k) ^ j) * X) ∧
      T.natDegree = r ∧ f * G = T.comp (X ^ k)

/-- **Step sums along a Riordan array.** Let $K$ be a field, let $g, h \in K[[x]]$ with
$h(0) = 0$, and write $d(n, m) = [x^n]\, g(x) h(x)^m$. Then for all natural numbers $k > 1$,
$p < k$ and $n$,
$\sum_{j=0}^{n} d(n, kj + p) = [x^n]\, g(x) h(x)^p (1 - h(x)^k)^{-1}$.

Since $h(0) = 0$, $d(n, m) = 0$ for $m > n$, so the left side is the full sum over all
$j \ge 0$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 5. -/
public theorem_wanted riordan_stepSum_coeff {K : Type*} [Field K] (g h : PowerSeries K)
    (hh : PowerSeries.constantCoeff h = 0) (k p : ℕ) (hk : 1 < k) (hp : p < k) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff n (g * h ^ (k * j + p)) =
      PowerSeries.coeff n (g * h ^ p * (1 - h ^ k)⁻¹)

/-- **Window criterion for step sums of binomial coefficients.** Let $\alpha, k, \gamma, p, s$
be natural numbers with $\alpha > 1$, $k > 1$, $\gamma \ge 1$ and $p < k$, and let
$\delta_1, \delta_2, \ldots$ be integers. For $n \in \mathbb{N}$ let $c(n)$ be the sum of
$\binom{\alpha n}{m}$ over all $m$ with $0 \le m \le \alpha n$ and
$m \equiv \gamma n + p \pmod{k}$, that is, $c(n) = \sum_{j \in \mathbb{Z}}
\binom{\alpha n}{\gamma n + p + kj}$. If $c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n$
with $s \le n \le k^2 + s - 1$, then $c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n \ge s$.

The coefficients $\delta_i$ need only work for this one residue $p$; the source's hypothesis,
with one family $\delta_i$ for every $p$, is a special case.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 8. -/
public theorem_wanted binomialStepSum_recurrence_of_window (α k γ p s : ℕ) (hα : 1 < α)
    (hk : 1 < k) (hγ : 1 ≤ γ) (hp : p < k) (δ : ℕ → ℤ) :
    let c : ℕ → ℤ := fun n =>
      ∑ m ∈ (Finset.range (α * n + 1)).filter (fun m => m % k = (γ * n + p) % k),
        ((α * n).choose m : ℤ)
    (∀ n, s ≤ n → n ≤ k ^ 2 + s - 1 → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)) →
      ∀ n, s ≤ n → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)

/-- **Window criterion for shifted step sums of binomial coefficients.** Let
$\alpha, \beta, k, \gamma, p, s$ be natural numbers with $\alpha > 1$, $k > 1$, $\gamma > 1$ and
$p < k$, and let $\delta_1, \delta_2, \ldots$ be integers. For $n \in \mathbb{N}$ let $c(n)$ be
the sum of $\binom{\alpha n + \beta}{m}$ over all $m$ with $0 \le m \le \alpha n + \beta$ and
$m \equiv \gamma n + p \pmod{k}$, that is,
$c(n) = \sum_{j \in \mathbb{Z}} \binom{\alpha n + \beta}{\gamma n + p + kj}$. If
$c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n$ with $s \le n \le k^2 + s - 1$, then
$c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n \ge s$.

The coefficients $\delta_i$ need only work for this one residue $p$; the source's hypothesis,
with one family $\delta_i$ for every $p$, is a special case.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Theorem 9. -/
public theorem_wanted shiftedBinomialStepSum_recurrence_of_window (α β k γ p s : ℕ)
    (hα : 1 < α) (hk : 1 < k) (hγ : 1 < γ) (hp : p < k) (δ : ℕ → ℤ) :
    let c : ℕ → ℤ := fun n =>
      ∑ m ∈ (Finset.range (α * n + β + 1)).filter (fun m => m % k = (γ * n + p) % k),
        ((α * n + β).choose m : ℤ)
    (∀ n, s ≤ n → n ≤ k ^ 2 + s - 1 → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)) →
      ∀ n, s ≤ n → c n = ∑ i ∈ Finset.Icc 1 s, δ i * c (n - i)

/-- **Step sums of a rational Riordan array satisfy a common recurrence.** Let
$g_1, g_2, h_1, h_2 \in \mathbb{Z}[x]$ with $g_2(0) = h_1(0) = h_2(0) = 1$, let $\nu \ge 1$ and
$k \ge 1$ be natural numbers, and in $\mathbb{Q}[[x]]$ let $g = g_1/g_2$ and
$h = x^\nu h_1/h_2$. For $p, n \in \mathbb{N}$ let
$a_p(n) = \sum_{j=0}^{n} [x^n]\, g h^{kj+p}$. Then there are $r \in \mathbb{N}$ and integers
$\alpha_1, \ldots, \alpha_r$ such that $a_p(n) = \sum_{i=1}^{r} \alpha_i a_p(n - i)$ for every
$p < k$ and every $n \ge r$.

Since $h$ has no constant term, $[x^n]\, g h^m = 0$ for $m > n$, so $a_p(n)$ is the full sum
over all $j \ge 0$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4,
Proposition 11. -/
public theorem_wanted rationalRiordan_stepSum_linearRecurrence (g₁ g₂ h₁ h₂ : ℤ[X]) (ν : ℕ)
    (hg₂ : g₂.eval 0 = 1) (hh₁ : h₁.eval 0 = 1) (hh₂ : h₂.eval 0 = 1) (hν : 1 ≤ ν)
    (k : ℕ) (hk : 0 < k) :
    let toQ : ℤ[X] → PowerSeries ℚ := fun q => ((q.map (Int.castRingHom ℚ)) : PowerSeries ℚ)
    let g : PowerSeries ℚ := toQ g₁ * (toQ g₂)⁻¹
    let h : PowerSeries ℚ := PowerSeries.X ^ ν * toQ h₁ * (toQ h₂)⁻¹
    let a : ℕ → ℕ → ℚ := fun p n =>
      ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff n (g * h ^ (k * j + p))
    ∃ (r : ℕ) (αs : ℕ → ℤ), ∀ p < k, ∀ n, r ≤ n →
      a p n = ∑ i ∈ Finset.Icc 1 r, (αs i : ℚ) * a p (n - i)

/-- **Alternating step-five sums of Catalan's triangle are Fibonacci numbers.** For natural
numbers $n$ and $k$ let $d(n, k) = \frac{k + 1}{n + 1} \binom{2(n + 1)}{n - k}$ if $k \le n$,
and $d(n, k) = 0$ if $k > n$. Let $F_m$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then
for every $n \in \mathbb{N}$,
$\sum_{j=0}^{n} \bigl(d(n, 5j + 1) - d(n, 5j + 2)\bigr) = F_{2n}$ and
$\sum_{j=0}^{n} \bigl(d(n, 5j) - d(n, 5j + 3)\bigr) = F_{2n+1}$.

The numbers $d(n, k)$ form Catalan's triangle (OEIS A039598), the Riordan array $(g, xg)$ with
$g(x) = (1 - 2x - \sqrt{1 - 4x})/(2x^2)$; since $d(n, m) = 0$ for $m > n$, the sums are the full
sums over all $j \ge 0$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4,
Proposition 13. -/
public theorem_wanted catalanTriangle_stepFive_sub_eq_fib (n : ℕ) :
    let d : ℕ → ℕ → ℚ := fun n k =>
      if k ≤ n then (k + 1 : ℚ) / (n + 1) * ((2 * (n + 1)).choose (n - k) : ℚ) else 0
    ∑ j ∈ Finset.range (n + 1), (d n (5 * j + 1) - d n (5 * j + 2)) = Nat.fib (2 * n) ∧
      ∑ j ∈ Finset.range (n + 1), (d n (5 * j) - d n (5 * j + 3)) = Nat.fib (2 * n + 1)

end

end MetaMathlibExt
