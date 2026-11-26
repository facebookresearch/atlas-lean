/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.SquareSplittingConvolution.DivisorProperties
public import MathlibExt.NumberTheory.SquareSplittingConvolution.MoebiusInversion
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitDivisorCountLSeries
public import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitMoebiusFormula
public import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitTotientFormula
public import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitConvInverseOfIsMultiplicative
public import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitMoebiusSupportDensity

namespace MetaMathlibExt

@[expose] public section

open Filter Topology Asymptotics

/-- **Ring axioms for the square-splitting convolution.** For all complex arithmetic functions
$f$, $g$ and $h$, the square-splitting convolution $\star$ satisfies $f \star g = g \star f$,
$(f \star g) \star h = f \star (g \star h)$, $f \star (g + h) = f \star g + f \star h$ and
$\varepsilon \star f = f$, where $\varepsilon$ is the arithmetic function with $\varepsilon(1) = 1$
and $\varepsilon(n) = 0$ for $n \ne 1$.

With pointwise addition, these identities make the complex arithmetic functions a commutative ring
under $\star$ with identity $\varepsilon$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 2
(`integers-2026-A56-thm-2`). -/
public theorem_wanted squareSplitConv_commRing_axioms (f g h : ArithmeticFunction ℂ) :
    squareSplitConv f g = squareSplitConv g f ∧
      squareSplitConv (squareSplitConv f g) h = squareSplitConv f (squareSplitConv g h) ∧
      squareSplitConv f (g + h) = squareSplitConv f g + squareSplitConv f h ∧
      squareSplitConv 1 f = f

/-- **Square-splitting convolution as a bivariate Dirichlet convolution.** Let $\star$ be the
square-splitting convolution. For all complex arithmetic functions $f$ and $g$, every squarefree
natural number $u$ and every natural number $v \ge 1$,
$$(f \star g)(u v^2) = \sum_{u_1 \mid u} \sum_{v_1 \mid v} f(u_1 v_1^2)\, g((u/u_1)(v/v_1)^2).$$
Moreover, for every function $F : \mathbb{N} \times \mathbb{N} \to \mathbb{C}$ there is exactly
one complex arithmetic function $f$ with $f(u v^2) = F(u, v)$ for every squarefree $u$ and every
$v \ge 1$.

Thus $f \mapsto \big((u, v) \mapsto f(u v^2)\big)$ is a bijection from complex arithmetic functions
onto functions on $\{(u, v) : u \text{ squarefree},\ v \ge 1\}$, and it turns $\star$ into the
bivariate Dirichlet convolution
$(\Phi \odot \Psi)(u, v) = \sum_{u_1 \mid u} \sum_{v_1 \mid v} \Phi(u_1, v_1)\, \Psi(u/u_1, v/v_1)$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 2
(`integers-2026-A56-thm-2`). -/
public theorem_wanted squareSplitConv_bivariate_iso :
    (∀ (f g : ArithmeticFunction ℂ) (u v : ℕ), Squarefree u → 0 < v →
      squareSplitConv f g (u * v ^ 2) =
        ∑ u₁ ∈ u.divisors, ∑ v₁ ∈ v.divisors,
          f (u₁ * v₁ ^ 2) * g ((u / u₁) * (v / v₁) ^ 2)) ∧
    ∀ F : ℕ → ℕ → ℂ, ∃! f : ArithmeticFunction ℂ,
      ∀ u v, Squarefree u → 0 < v → f (u * v ^ 2) = F u v

/-- **Average order of the square-splitting totient function.** Let $A(n)$ be the set of
square-splitting divisors of $n$, and let $\varphi_\star$ be any integer-valued arithmetic function
with $\sum_{d \in A(n)} \varphi_\star(d) = n$ for every $n \ge 1$. Then the product
$M = \prod_p \left(1 - \frac{1}{p^2} + \frac{(p-1)^2}{p^5}\right)$ converges absolutely, that is,
$\sum_p \left|\frac{(p-1)^2}{p^5} - \frac{1}{p^2}\right| < \infty$, and for every
$0 < \varepsilon < 1/2$,
$$\sum_{1 \le n \le x} \varphi_\star(n) = \frac{M}{2}\,x^2 + O(x^{1+\varepsilon})
\quad (x \to \infty).$$

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 8
(`integers-2026-A56-thm-8`). -/
public theorem_wanted squareSplitTotient_sum_asymptotic (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) :
    Summable (fun p : Nat.Primes =>
      |-(1 / ((p : ℕ) : ℝ) ^ 2) + (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5|) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (φ n : ℝ) -
        (∏' p : Nat.Primes,
          (1 - 1 / ((p : ℕ) : ℝ) ^ 2 + (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5)) / 2 * x ^ 2)
        =O[atTop] fun x => x ^ (1 + ε)

/-- **Partial-sum asymptotics for a Riemann zeta quotient times a Dirichlet series.** Let
$f, g : \mathbb{N} \to \mathbb{C}$ and let $\sigma_0 < 1/2$ be a real number. Suppose that the
Dirichlet series $G(s) = \sum_{n \ge 1} g(n) n^{-s}$ converges absolutely for
$\operatorname{Re} s > \sigma_0$, that $G(1) \ne 0$, and that for every complex $s$ with
$\operatorname{Re} s > 1$ the Dirichlet series $F(s) = \sum_{n \ge 1} f(n) n^{-s}$ converges
absolutely and $F(s) = \zeta(s)^2 G(s) / \zeta(2s)$, where $\zeta$ is the Riemann zeta
function. Then, as the real number $x$ tends to infinity,
$$
\sum_{1 \le n \le x} f(n) = \frac{G(1)}{\zeta(2)}\, x \log x +
\frac{G(1)}{\zeta(2)} \left(2\gamma - 1 + \frac{G'(1)}{G(1)} -
\frac{2\zeta'(2)}{\zeta(2)}\right) x + O\big(x^{1/2} (\log x)^3\big),
$$
where $\gamma$ is the Euler–Mascheroni constant and $G'$, $\zeta'$ are complex derivatives.

The hypothesis $G(1) \ne 0$ is added so that the quotient $G'(1)/G(1)$ is meaningful.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Lemma 1
(`integers-2026-A56-lem-1`). -/
public theorem_wanted sum_asymptotic_of_LSeries_eq_zeta_sq_div_zeta_two_mul (f g : ℕ → ℂ)
    {σ₀ : ℝ} (hσ₀ : σ₀ < 1 / 2) (hg : ∀ s : ℂ, σ₀ < s.re → LSeriesSummable g s)
    (hf : ∀ s : ℂ, 1 < s.re →
      LSeriesSummable f s ∧ LSeries f s = riemannZeta s ^ 2 / riemannZeta (2 * s) * LSeries g s)
    (hG1 : LSeries g 1 ≠ 0) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n -
        (LSeries g 1 / riemannZeta 2 * x * Real.log x +
          LSeries g 1 / riemannZeta 2 * (2 * Real.eulerMascheroniConstant - 1 +
            deriv (LSeries g) 1 / LSeries g 1 - 2 * deriv riemannZeta 2 / riemannZeta 2) * x))
      =O[atTop] fun x => x ^ (1 / 2 : ℝ) * Real.log x ^ 3

/-- **Average order of the square-splitting divisor function.** Let $\tau^\star(n) = |A(n)|$ be
the number of elements of the square-splitting divisor set $A(n)$, let $\gamma$ be the
Euler–Mascheroni constant, and let $A_\tau = \prod_p (1 - 1/(p+1)^2)$ and
$B_\tau = 6 \sum_p \log p / ((p-1)(p+1)(p+2))$, where $p$ runs over the primes. Then, as the real
number $x$ tends to infinity,
$\sum_{1 \le n \le x} \tau^\star(n) - A_\tau x \log x - A_\tau (2\gamma - 1 - B_\tau - c) x$ is
$O(x^{1/2} (\log x)^3)$, where $c = 2\zeta'(2)/\zeta(2)$.

These constants are the ones forced by the Dirichlet series of $\tau^\star$: with
$H(s) = \prod_p (1 - 3p^{-2s} + 2p^{-3s})$, one has $A_\tau = \zeta(2)^2 H(1)$ and
$-B_\tau - 2\zeta'(2)/\zeta(2) = 4\zeta'(2)/\zeta(2) + H'(1)/H(1)$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 10
(`integers-2026-A56-thm-10`). -/
public theorem_wanted squareSplitDivisorCount_sum_asymptotic :
    let Aτ : ℝ := ∏' p : Nat.Primes, (1 - 1 / (((p : ℕ) : ℝ) + 1) ^ 2)
    let Bτ : ℝ := 6 * ∑' p : Nat.Primes, Real.log (p : ℕ) /
      ((((p : ℕ) : ℝ) - 1) * (((p : ℕ) : ℝ) + 1) * (((p : ℕ) : ℝ) + 2))
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((squareSplitDivisors n).card : ℝ) -
        (Aτ * x * Real.log x + Aτ * (2 * Real.eulerMascheroniConstant - 1 - Bτ -
          2 * (deriv riemannZeta 2 / riemannZeta 2).re) * x))
      =O[atTop] fun x => x ^ (1 / 2 : ℝ) * Real.log x ^ 3

/-- **A square-splitting divisor function and its Euler product.** Let
$\alpha \in \mathbb{C}$, let $\sigma_\beta(m) = \sum_{d \mid m} d^\beta$ for $\beta \in \mathbb{C}$
(complex powers), and let $f(n) = \sigma_\alpha(u(n))\,\sigma_{2\alpha}(v(n))$, where $u(n)$ is
the product of the primes dividing $n$ to an odd power and $v(n)$ is the positive integer with
$n = u(n)\,v(n)^2$. Then $f(1) = 1$ and $f(mn) = f(m)\,f(n)$ for all coprime $m$ and $n$. For
every prime $p$ and every $b \ge 0$, $f(p^{2b}) = \sum_{j=0}^{b} p^{2j\alpha}$ and
$f(p^{2b+1}) = (1 + p^\alpha) \sum_{j=0}^{b} p^{2j\alpha}$. For every complex $s$ with
$\operatorname{Re} s > \max(1, 1 + \operatorname{Re} \alpha)$, for every prime $p$
$$\sum_{k \ge 0} \frac{f(p^k)}{p^{ks}}
= \frac{1 + p^{-s} + p^{-(s-\alpha)}}{(1 - p^{-2s})(1 - p^{-(2s-2\alpha)})},$$
the series $\sum_{n \ge 1} f(n)\,n^{-s}$ converges absolutely, and
$$\sum_{n \ge 1} \frac{f(n)}{n^s}
= \zeta(2s)\,\zeta(2s - 2\alpha) \prod_p \left(1 + p^{-s} + p^{-(s-\alpha)}\right).$$

The paper identifies $f$ with its divisor function $\sigma_{\star,\alpha}$; that identification is
not part of this statement.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 6
(`integers-2026-A56-thm-6`). -/
public theorem_wanted squareSplitSigma_multiplicative_eulerProduct (α : ℂ) :
    let σ : ℂ → ℕ → ℂ := fun β m => ∑ d ∈ m.divisors, (d : ℂ) ^ β
    let f : ℕ → ℂ := fun n => σ α (squareSplitU n) * σ (2 * α) (squareSplitV n)
    f 1 = 1 ∧ (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) ∧
    (∀ p : ℕ, p.Prime → ∀ b : ℕ,
      f (p ^ (2 * b)) = ∑ j ∈ Finset.range (b + 1), (p : ℂ) ^ (2 * j * α) ∧
      f (p ^ (2 * b + 1)) =
        (1 + (p : ℂ) ^ α) * ∑ j ∈ Finset.range (b + 1), (p : ℂ) ^ (2 * j * α)) ∧
    ∀ s : ℂ, max 1 (1 + α.re) < s.re →
      (∀ p : ℕ, p.Prime →
        HasSum (fun k : ℕ => f (p ^ k) * (p : ℂ) ^ (-(k * s)))
          ((1 + (p : ℂ) ^ (-s) + (p : ℂ) ^ (-(s - α))) /
            ((1 - (p : ℂ) ^ (-(2 * s))) * (1 - (p : ℂ) ^ (-(2 * s - 2 * α)))))) ∧
      LSeriesSummable f s ∧
      LSeries f s = riemannZeta (2 * s) * riemannZeta (2 * s - 2 * α) *
        ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s) + ((p : ℕ) : ℂ) ^ (-(s - α)))

end

end MetaMathlibExt
