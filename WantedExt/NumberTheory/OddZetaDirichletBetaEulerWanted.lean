/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.Analysis.Ramanujan.Part1Ch7DirichletBeta

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/-- **Zeta series over odd denominators.** Let $\zeta$ be the Riemann zeta function. For every
natural number $k \ge 2$, the series $\sum_{n \ge 0} 1/(2n+1)^k$ converges in $\mathbb{C}$ and
$$\sum_{n=0}^{\infty} \frac{1}{(2n+1)^k} = \Bigl(1 - \frac{1}{2^k}\Bigr) \zeta(k).$$

The source writes this as $\sum_{n \ge 1} 1/(2n-1)^k = (1 - 2^{-k}) \zeta(k)$ for integers
$k > 1$.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 2, Equation (11)
(`integers-2025-A50-prop-2`), citing its reference [20]. -/
public theorem_wanted hasSum_one_div_odd_pow (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun n : ℕ => 1 / (2 * (n : ℂ) + 1) ^ k) ((1 - 1 / 2 ^ k) * riemannZeta k)

/-- **Dirichlet beta at odd positive integers.** Let $\beta$ be the Dirichlet $L$-function of the
nontrivial character modulo $4$, which for $\operatorname{Re} s > 1$ is the series
$\beta(s) = \sum_{n \ge 1} (-1)^{n-1}/(2n-1)^s$, and let $E_0 = 1, E_2 = -1, E_4 = 5,
E_6 = -61, \dots$ be the even-index Euler numbers. Then for every natural number $m$,
$$\beta(2m+1) = \frac{\pi^{2m+1} \, |E_{2m}|}{2^{2m+2} \, (2m)!}.$$

For example $\beta(1) = \pi/4$, $\beta(3) = \pi^3/32$, $\beta(5) = 5\pi^5/1536$ and
$\beta(7) = 61\pi^7/184320$. With $k = 2m+2$ this is the source's Equation (12),
$\beta(k-1) = (\pi/2)^{k-1} |E_{k-2}| / (2 (k-2)!)$ for even $k \ge 2$. At $s = 1$ the series
converges only conditionally, and its sum is the value of the $L$-function there.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 3, Equation (12)
(`integers-2025-A50-prop-3`), citing its references [3], [6]. -/
public theorem_wanted dirichletBeta_two_mul_add_one (m : ℕ) :
    chapter7DirichletBeta (2 * m + 1) =
      (Real.pi : ℂ) ^ (2 * m + 1) * ((|chapter5EulerEven m| : ℤ) : ℂ) /
        (2 ^ (2 * m + 2) * ((2 * m).factorial : ℂ))

/-- **Integrals of powers of $\sin x / x$.** For every natural number $k \ge 1$, the improper
integral $\lim_{R \to \infty} \int_0^R (\sin x / x)^k \, dx$ exists and
$$
\lim_{R \to \infty} \int_0^R \Bigl(\frac{\sin x}{x}\Bigr)^k dx =
\frac{\pi}{2^k (k-1)!} \sum_{i=0}^{\lfloor k/2 \rfloor} (-1)^i \binom{k}{i} (k-2i)^{k-1}.
$$

For $k = 1$ the integral converges only conditionally, hence the limit over $R$.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Theorem 1 (`integers-2025-A50-thm-1`). -/
public theorem_wanted tendsto_integral_sinc_pow (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, (Real.sin x / x) ^ k) Filter.atTop
      (nhds (Real.pi * ((∑ i ∈ Finset.range (k / 2 + 1),
          (-1 : ℝ) ^ i * (k.choose i : ℝ) * ((k : ℝ) - 2 * i) ^ (k - 1)) /
        (2 ^ k * ((k - 1).factorial : ℝ)))))

/-- **Sums of powers of $\sin(nt)/n$.** Let $k \ge 1$ be a natural number, suppose that the
limit $L = \lim_{R \to \infty} \int_0^R (\sin x / x)^k \, dx$ exists, and let $t$ be a real
number with $0 < t < 2\pi$ if $k = 1$ and $0 \le t \le 2\pi/k$ if $k \ge 2$. Then the partial
sums of $\sum_{n \ge 1} \sin^k(nt)/n^k$ converge and
$$\sum_{n=1}^{\infty} \frac{\sin^k(nt)}{n^k} = t^{k-1} L - \frac{t^k}{2}.$$

The source writes $L$ as $\pi I_k$, with $I_k$ the normalized integral of its Theorem 1. For
$k = 1$ the series converges only conditionally.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 4 (`integers-2025-A50-prop-4`), quoting its reference [18]. -/
public theorem_wanted tendsto_sum_sin_pow_div_pow (k : ℕ) (hk : 1 ≤ k) (t : ℝ)
    (ht₁ : k = 1 → 0 < t ∧ t < 2 * Real.pi) (ht₂ : 2 ≤ k → 0 ≤ t ∧ t ≤ 2 * Real.pi / k)
    (L : ℝ) (hL : Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, (Real.sin x / x) ^ k)
      Filter.atTop (nhds L)) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        Real.sin ((n + 1 : ℝ) * t) ^ k / ((n : ℝ) + 1) ^ k) Filter.atTop
      (nhds (t ^ (k - 1) * L - t ^ k / 2))

end

end MetaMathlibExt
