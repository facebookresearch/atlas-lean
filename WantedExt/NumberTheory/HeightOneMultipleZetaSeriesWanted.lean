/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import WantedExt.NumberTheory.BernoulliStirlingHarmonicWanted
public import WantedExt.NumberTheory.HyperharmonicEulerSumsWanted

/-! # Series of height one multiple zeta functions

Statement-only requests from Paul Thomas Young, *Series of Height One Multiple Zeta
Functions*, INTEGERS 24 (2024), Article A43. The height one multiple zeta function
`ζ(s, {1}^j) = ∑_{n₁ > n₂ > ⋯ > n_{j+1} ≥ 1} n₁^{-s} (n₂ ⋯ n_{j+1})^{-1}` is
`heightOneMultipleZeta s j`: the largest index is `n + 1`, and the remaining `j` indices form a
`j`-element subset `T` of `{1, …, n}`, contributing `∏_{m ∈ T} 1/m`. The multiple Hurwitz zeta
function `ζ_r(s) = ζ_r(s, 1)` of (2.2) is `multipleHurwitzZeta r s`, with
`binom(m + r - 1, m) = r (r + 1) ⋯ (r + m - 1) / m!` written through `ascPochhammer`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Height one multiple zeta function.** For a complex number $s$ and an integer $j \ge 0$, the
height one multiple zeta function is
$$\zeta(s, \{1\}^j) = \sum_{n \ge 0} (n + 1)^{-s} \sum_{T} \prod_{m \in T} \frac{1}{m},$$
where $T$ runs over the $j$-element subsets of $\{1, \dots, n\}$. Writing $n_1 = n + 1$ and
$T = \{n_2, \dots, n_{j+1}\}$, this is
$\zeta(s, \{1\}^j) = \sum_{n_1 > \cdots > n_{j+1} \ge 1} n_1^{-s} (n_2 \cdots n_{j+1})^{-1}$, which
converges for $\operatorname{Re} s > 1$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 1. -/
public noncomputable def heightOneMultipleZeta (s : ℂ) (j : ℕ) : ℂ :=
  ∑' n : ℕ, ((n : ℂ) + 1) ^ (-s) *
    ∑ T ∈ (Finset.Icc 1 n).powersetCard j, ∏ m ∈ T, (1 / (m : ℂ))

/-- **Height one multiple zeta function of depth one.** For every complex number $s$, the height
one multiple zeta function $\zeta(s, \{1\}^j)$ at $j = 0$ is the Dirichlet series of the Riemann
zeta function: $\zeta(s, \{1\}^0) = \sum_{n \ge 0} (n + 1)^{-s}$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 1. -/
public theorem heightOneMultipleZeta_zero (s : ℂ) :
    heightOneMultipleZeta s 0 = ∑' n : ℕ, ((n : ℂ) + 1) ^ (-s) := by
  simp [heightOneMultipleZeta]

/-- **Multiple Hurwitz zeta function.** For complex numbers $r$ and $s$, the multiple Hurwitz zeta
function of order $r$, with Hurwitz parameter $a = 1$, is the Dirichlet series
$$\zeta_r(s) = \sum_{m \ge 0} \binom{m + r - 1}{m} (m + 1)^{-s},$$
where $\binom{m + r - 1}{m} = r (r + 1) \cdots (r + m - 1) / m!$. The series converges for
$\operatorname{Re} r < \operatorname{Re} s$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 2, Equation (2.2). -/
public noncomputable def multipleHurwitzZeta (r s : ℂ) : ℂ :=
  ∑' m : ℕ, (ascPochhammer ℂ m).eval r / (m.factorial : ℂ) * ((m : ℂ) + 1) ^ (-s)

/-- **Multiple Hurwitz zeta function of order zero.** For every complex number $s$, the multiple
Hurwitz zeta function of order $0$ is identically one: $\zeta_0(s) = 1$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 2, Equation (2.2). -/
public theorem multipleHurwitzZeta_zero (s : ℂ) : multipleHurwitzZeta 0 s = 1 := by
  rw [multipleHurwitzZeta, tsum_eq_single 0]
  · simp
  · intro m hm
    simp [hm]

/-- **Expansion of the multiple Hurwitz zeta function in height one multiple zeta values.** Let
$r$ and $s$ be complex numbers with $\operatorname{Re} s > 1$, $|r - 1| < |s - 1|$ and
$\operatorname{Re} r < \operatorname{Re} s$. Write $\zeta(s, \{1\}^j)$ for the height one multiple
zeta function and $\zeta_r(s)$ for the multiple Hurwitz zeta function of order $r$. Then the series
$\sum_{j \ge 0} \zeta(s, \{1\}^j) \, (r - 1)^j$ is summable with sum $\zeta_r(s)$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Theorem 1 (`integers-2024-A43-thm-1`). -/
public theorem_wanted hasSum_heightOneMultipleZeta_mul_pow {s r : ℂ} (hs : 1 < s.re)
    (hr : ‖r - 1‖ < ‖s - 1‖) (hrs : r.re < s.re) :
    HasSum (fun j : ℕ => heightOneMultipleZeta s j * (r - 1) ^ j) (multipleHurwitzZeta r s)

/-- **Height one multiple zeta series weighted by powers of a natural number.** Let $n \ge 0$ be
an integer. Write $\zeta(s, \{1\}^j)$ for the height one multiple zeta function, $\zeta$ for the
Riemann zeta function, $c(n, m)$ for the unsigned Stirling numbers of the first kind and
$B_j^{(k)}(x)$ for the poly-Bernoulli polynomials. For every complex $s$ with
$\operatorname{Re} s > n + 1$, the series $\sum_{j \ge 0} \zeta(s, \{1\}^j) \, n^j$ (with $0^0 = 1$)
is summable with sum $\frac{1}{n!} \sum_{m=0}^{n} c(n, m) \, \zeta(s - m)$. For every complex $s$
with $\operatorname{Re} s > 1$, the series $\sum_{j \ge 0} B_j^{(-n)}(-1) \, \zeta(s + n, \{1\}^j)$
is summable with sum $\zeta(s)$.

The source states the second identity with $C_j^{(-n)} = B_j^{(-n)}(1)$, where its poly-Bernoulli
polynomials have the generating function with $e^{-xt}$; with the factor $e^{xt}$ used here this
coefficient is $B_j^{(-n)}(-1)$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Corollary 1 (`integers-2024-A43-cor-1`). -/
public theorem_wanted hasSum_heightOneMultipleZeta_mul_nat_pow (n : ℕ) :
    (∀ s : ℂ, (n : ℝ) + 1 < s.re →
      HasSum (fun j : ℕ => heightOneMultipleZeta s j * (n : ℂ) ^ j)
        (1 / (n.factorial : ℂ) *
          ∑ m ∈ Finset.range (n + 1), (n.stirlingFirst m : ℂ) * riemannZeta (s - m))) ∧
    ∀ s : ℂ, 1 < s.re →
      HasSum (fun j : ℕ => (polyBernoulliPoly j (-(n : ℤ)) (-1) : ℂ) *
        heightOneMultipleZeta (s + n) j) (riemannZeta s)

/-- **Height one multiple zeta series weighted by powers of a negative integer.** Let $r \ge 1$
be an integer and let $\zeta(s, \{1\}^j)$ denote the height one multiple zeta function. For
every complex number $s$ with $\operatorname{Re} s > r + 1$,

$$\sum_{j \ge 0} \zeta(s, \{1\}^j) (-r)^j = \sum_{m=0}^{r-1} \binom{r-1}{m} (-1)^m (m+1)^{-s}.$$

For every integer $k > r + 1$,

$$\sum_{j \ge 0} \zeta(k, \{1\}^j) (-r)^j = \frac{H_{r,k-1}}{r},$$

where $H_{r,k-1} = \sum_{i=1}^{r} (-1)^{i-1} \binom{r}{i} i^{-(k-1)}$ is the rational Roman
harmonic number (Equation (2.18)).

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Corollary 2 (`integers-2024-A43-cor-2`). -/
public theorem_wanted tsum_heightOneMultipleZeta_mul_neg_nat_pow
    (r : ℕ) (hr : 1 ≤ r) :
    (∀ s : ℂ, (r : ℝ) + 1 < s.re →
      ∑' j : ℕ, heightOneMultipleZeta s j * (-(r : ℂ)) ^ j =
        ∑ m ∈ Finset.range r, ((r - 1).choose m : ℂ) * (-1) ^ m * ((m : ℂ) + 1) ^ (-s)) ∧
    ∀ k : ℕ, r + 1 < k →
      ∑' j : ℕ, heightOneMultipleZeta k j * (-(r : ℂ)) ^ j =
        (((∑ i ∈ Finset.Icc 1 r, (-1 : ℚ) ^ (i - 1) * (r.choose i : ℚ) / (i : ℚ) ^ (k - 1)) /
          r : ℚ) : ℂ)

/-- **Generalized Goldbach series for height one multiple zeta values.** Let $k \ge 1$ be an
integer. Write $\zeta(s, \{1\}^j)$ for the height one multiple zeta function, $\zeta$ for the
Riemann zeta function, $c(k, m)$ for the unsigned Stirling numbers of the first kind,
$H_k = \sum_{i=1}^{k} 1/i$ for the $k$-th harmonic number and
$H_{k,k} = \sum_{i=1}^{k} (-1)^{i-1} \binom{k}{i} i^{-k}$ for the Roman harmonic number. Then the
series $\sum_{j \ge 0} \bigl(k^j \zeta(k + 1, \{1\}^j) - \frac{1}{k! \, k}\bigr)$ is summable with
sum $\frac{1}{k!} \bigl(\sum_{m=0}^{k-1} c(k, m) \, \zeta(k + 1 - m) + H_k\bigr)$, and the series
$\sum_{j \ge 0} (-1)^j \bigl(k^j \zeta(k + 1, \{1\}^j) - \frac{1}{k! \, k}\bigr)$ is summable with
sum $\frac{H_{k,k}}{k} - \frac{1}{2 \, k! \, k}$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Theorem 2 (`integers-2024-A43-thm-2`). -/
public theorem_wanted hasSum_heightOneMultipleZeta_goldbach (k : ℕ) (hk : 1 ≤ k) :
    HasSum (fun j : ℕ => (k : ℂ) ^ j * heightOneMultipleZeta ((k : ℂ) + 1) j -
        1 / ((k.factorial : ℂ) * k))
      (1 / (k.factorial : ℂ) *
        (∑ m ∈ Finset.range k, (k.stirlingFirst m : ℂ) * riemannZeta ((k : ℂ) + 1 - m) +
          (harmonic k : ℂ))) ∧
    HasSum (fun j : ℕ => (-1) ^ j * ((k : ℂ) ^ j * heightOneMultipleZeta ((k : ℂ) + 1) j -
        1 / ((k.factorial : ℂ) * k)))
      (((∑ i ∈ Finset.Icc 1 k, (-1 : ℚ) ^ (i - 1) * (k.choose i : ℚ) / (i : ℚ) ^ k) / k -
        1 / (2 * (k.factorial : ℚ) * k) : ℚ) : ℂ)

/-- **Expansion of the hyperharmonic zeta function in height one multiple zeta values.** Let $r$
and $s$ be complex numbers with $\operatorname{Re} s > 0$, $|r| < |s|$ and
$\operatorname{Re} r < \operatorname{Re} s$. Write $\zeta(s, \{1\}^j)$ for the height one multiple
zeta function, $H_m^{[r]}(k)$ for the generalized hyperharmonic numbers and
$H_m^{[r]} = H_m^{[r]}(1)$; equivalently, $H_m^{[r]}$ is the derivative of $\binom{m + r - 1}{m}$
with respect to $r$. Then the series $\sum_{j \ge 0} (j + 1) \, \zeta(s + 1, \{1\}^j) \, r^j$ is
summable with sum the hyperharmonic zeta function $\sigma(r, s) = \sum_{m \ge 1} H_m^{[r]} m^{-s}$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Theorem 3, second equality (`integers-2024-A43-thm-3`). -/
public theorem_wanted hasSum_succ_mul_heightOneMultipleZeta_mul_pow {r s : ℂ} (hs : 0 < s.re)
    (hr : ‖r‖ < ‖s‖) (hrs : r.re < s.re) :
    HasSum (fun j : ℕ => ((j : ℂ) + 1) * heightOneMultipleZeta (s + 1) j * r ^ j)
      (∑' m : ℕ, generalizedHyperharmonic (m + 1) 1 r * ((m : ℂ) + 1) ^ (-s))

/-- **Shifted alternating series of height one multiple zeta values.** Let $k \ge -1$ and
$p \ge 0$ be integers, write $\zeta(s, \{1\}^p)$ for the height one multiple zeta function and
$\zeta_r(s)$ for the multiple Hurwitz zeta function of order $r$. Then the partial sums of the
series $\nu_{k,p} = \sum_{n \ge 2} \frac{(-1)^n \, \zeta(n, \{1\}^p)}{n + k}$ converge to
$\int_0^1 (1 - r)^{k+1} \, \zeta_r(p + 2) \, dr$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Theorem 4 (`integers-2024-A43-thm-4`). -/
public theorem_wanted tendsto_alternating_heightOneMultipleZeta_integral (k : ℤ) (hk : -1 ≤ k)
    (p : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Ico 2 N,
        (-1 : ℂ) ^ n / ((n : ℂ) + k) * heightOneMultipleZeta n p)
      Filter.atTop
      (nhds (∫ r in (0 : ℝ)..1,
        (1 - (r : ℂ)) ^ (k + 1).toNat * multipleHurwitzZeta r ((p : ℂ) + 2)))

/-- **Linear Laurent coefficient of the height one multiple zeta function.** Let $j \ge 1$ be an
integer, write $\zeta(s, \{1\}^{j-1})$ for the height one multiple zeta function and $\zeta_r(s)$
for the multiple Hurwitz zeta function of order $r$. There are complex numbers
$c_0, \dots, c_{j-1}$ and a function $F$ analytic at $s = 1$ such that
$\zeta(s, \{1\}^{j-1}) = \sum_{i=0}^{j-1} c_i (s - 1)^{-(i+1)} + F(s)$ for all $s$ near $1$
with $\operatorname{Re} s > 1$, and
$$-F'(1) = \int_0^1 \bigl((1 - r) \, \zeta_r(j + 2) - \zeta_r(j + 1)\bigr) \, dr - a_{j+1},$$
where $a_{j+1}$ is the coefficient of $s^{j+1}$ in the Taylor expansion of $1/\Gamma(s + 1)$
at $s = 0$.

The number $-F'(1)$ generalizes the first Stieltjes constant $\gamma_1$: for $j = 1$ and
$\operatorname{Re} s > 1$, $\zeta(s, \{1\}^0)$ equals the Riemann zeta function $\zeta(s)$, whose
Laurent expansion at $s = 1$ is $\zeta(s) = \frac{1}{s - 1} + \gamma - \gamma_1 (s - 1) + \cdots$
with Euler's constant $\gamma$, so $-F'(1) = \gamma_1$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Corollary 3 (`integers-2024-A43-cor-3`). -/
public theorem_wanted heightOneMultipleZeta_laurent_linear_coeff (j : ℕ) (hj : 1 ≤ j) :
    ∃ c : ℕ → ℂ, ∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧
      (∀ᶠ s in nhdsWithin (1 : ℂ) {s | 1 < s.re},
        heightOneMultipleZeta s (j - 1) =
          ∑ i ∈ Finset.range j, c i / (s - 1) ^ (i + 1) + F s) ∧
      -deriv F 1 =
        (∫ r in (0 : ℝ)..1, ((1 - (r : ℂ)) * multipleHurwitzZeta r ((j : ℂ) + 2) -
          multipleHurwitzZeta r ((j : ℂ) + 1))) -
        iteratedDeriv (j + 1) (fun s : ℂ => (Complex.Gamma (s + 1))⁻¹) 0 /
          ((j + 1).factorial : ℂ)

end

end MetaMathlibExt
