/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Explicit estimates for incomplete exponential sums (statements)

Statement-only targets from Todd Cochrane, *Explicit Estimates for Incomplete Exponential
Sums*. The incomplete sum `S_p(f, B) = ∑_{x=1}^{B} e_p(f(x))`, with `e_p(t) = e^{2πit/p}`, is
written out inline: `∑ x ∈ Finset.Icc 1 B, Complex.exp (2 * π * I * f(x) / p)`. The maximum
`Φ(f, p) = max_{0 ≤ y ≤ p-1} |∑_{x=1}^{p} e_p(f(x) + y x)|` of (1.1) is written inline as a
`Finset.sup` of `‖·‖₊` over `Finset.range p`, and `d_p(f)` as the `natDegree` of the image of
`f` in `(ZMod p)[X]`.
-/

namespace MetaMathlibExt

open Complex Finset

@[expose] public section

/-- **Partial-fraction bound for the cosecant.** For every real number $x$ with $0 < x < 1$,
$$\frac{1}{\sin(\pi x)} < \frac{1}{\pi}\left(\frac{1}{x} + \frac{2x}{1 - x^2}\right).$$
That is, the first two terms of the partial-fraction expansion of $\pi / \sin(\pi x)$ bound it
from above.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.1 (quoted from [3, Lemma 2.2]) (`integers-2025-A48-lem-3-1`). -/
public theorem_wanted one_div_sin_pi_lt (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
    1 / Real.sin (Real.pi * x) < (1 / Real.pi) * (1 / x + 2 * x / (1 - x ^ 2))

/-- **Bound for a sum of reciprocal sines.** Let $p$ be a prime, let $a$ be an integer not
divisible by $p$, let $B$ be an integer with $1 \le B < p/2$, and let $\gamma$ be the
Euler–Mascheroni constant. Then
$$
\sum_{h=1}^{B} \frac{1}{|\sin(\pi a h / p)|} <
\frac{p}{\pi}\left(\log B + \gamma + \frac{1}{2B}\right) + \frac{pB(B+1)}{\pi(p^2 - B^2)}.
$$

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.2 (`integers-2025-A48-lem-3-2`). -/
public theorem_wanted sum_one_div_abs_sin_lt (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : 1 ≤ B) (hB : (B : ℝ) < p / 2) :
    ∑ h ∈ Icc 1 B, 1 / |Real.sin (Real.pi * a * h / p)| <
      (p / Real.pi) * (Real.log B + Real.eulerMascheroniConstant + 1 / (2 * B)) +
        p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2))

/-- **Bound for a weighted sum of absolute sines.** Let $K$ be a positive integer, let $\xi$ be a
real number, and let $\gamma$ be the Euler–Mascheroni constant. Then
$$
\sum_{y=1}^{K} \frac{|\sin(y\xi)|}{y} <
\frac{2}{\pi}\left(\log(K + 1) + \gamma + \log 2\right) + \frac{3}{\pi(K + 1)}
$$
and
$$
\sum_{y=1}^{K} \frac{|\sin(y\xi)|}{y} <
\frac{2}{\pi}\log K + \frac{2}{\pi}(\gamma + \log 2) + \frac{5}{\pi K}.
$$

The second bound is the form (3.1) of the first, obtained from $\log(K + 1) < \log K + 1/K$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.4 (quoted from [3, Lemma 2.1]) and inequality (3.1)
(`integers-2025-A48-lem-3-4`). -/
public theorem_wanted sum_abs_sin_mul_div_lt (K : ℕ) (hK : 1 ≤ K) (ξ : ℝ) :
    ∑ y ∈ Icc 1 K, |Real.sin (y * ξ)| / y <
        (2 / Real.pi) * (Real.log (K + 1) + Real.eulerMascheroniConstant + Real.log 2) +
          3 / (Real.pi * (K + 1)) ∧
      ∑ y ∈ Icc 1 K, |Real.sin (y * ξ)| / y <
        (2 / Real.pi) * Real.log K +
          (2 / Real.pi) * (Real.eulerMascheroniConstant + Real.log 2) + 5 / (Real.pi * K)

/-- **Trigonometric polynomials bounding the indicator of an arc.** Let $a \le b$ be real
numbers with $b - a < 1$ and let $K \ge 1$ be an integer. Let $\chi(x) = 1$ if
$a \le x - n \le b$ for some integer $n$, and $\chi(x) = 0$ otherwise. Then there are complex
numbers $\alpha_-(k)$ and $\alpha_+(k)$, for $k \in \mathbb{Z}$, with
$\alpha_\pm(0) = b - a \pm \frac{1}{K+1}$, such that for every real $x$ the trigonometric
polynomials $S_\pm(x) = \sum_{k=-K}^{K} \alpha_\pm(k) e^{2\pi i k x}$ are real and satisfy
$S_-(x) \le \chi(x) \le S_+(x)$.

Only the constant coefficients and the pointwise bounds are stated; no bounds on the
coefficients $\alpha_\pm(k)$ with $k \ne 0$ are asserted.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 4.1 (`integers-2025-A48-lem-4-1`). -/
public theorem_wanted exists_trigPoly_minorant_majorant (a b : ℝ) (hab : a ≤ b)
    (hlen : b - a < 1) (K : ℕ) (hK : 1 ≤ K) :
    ∃ αm αp : ℤ → ℂ,
      αm 0 = ((b - a - 1 / (K + 1) : ℝ) : ℂ) ∧ αp 0 = ((b - a + 1 / (K + 1) : ℝ) : ℂ) ∧
      ∀ x : ℝ,
        let Sm := ∑ k ∈ Icc (-(K : ℤ)) K, αm k * exp (2 * Real.pi * I * k * x)
        let Sp := ∑ k ∈ Icc (-(K : ℤ)) K, αp k * exp (2 * Real.pi * I * k * x)
        let ind : ℝ := Set.indicator {y : ℝ | ∃ n : ℤ, a ≤ y - n ∧ y - n ≤ b} 1 x
        Sm.im = 0 ∧ Sp.im = 0 ∧ Sm.re ≤ ind ∧ ind ≤ Sp.re

/-- **Incomplete quadratic exponential sums of medium length.** Let $p$ be a prime, write
$e_p(t) = e^{2\pi i t/p}$, let $a, b, c$ be integers with $p \nmid a$, and let $B$ be an integer
with $\sqrt{p} < B < p/2$. Then $\left|\sum_{x=1}^{B} e_p(a x^2 + b x + c)\right| <
\sqrt{\frac{2}{\pi} \, p \log \frac{16.6 B^2}{p}}$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Theorem 1.2 (`integers-2025-A48-thm-1-2`). -/
public theorem_wanted norm_incomplete_quadratic_sum_lt (p : ℕ) (hp : p.Prime) (a b c : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : Real.sqrt p < B) (hB₂ : (B : ℝ) < p / 2) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((a * x ^ 2 + b * x + c : ℤ) : ℂ) / p)‖ <
      Real.sqrt ((2 / Real.pi) * p * Real.log (16.6 * B ^ 2 / p))

/-- **Bounds for short incomplete exponential sums of monic cubics.** Let $p$ be a prime, write
$e_p(t) = e^{2\pi i t/p}$, let $b, c$ be integers, let $B$ be an integer with
$4 p^{1/3} < B < \sqrt{p/12}$, and put $S = \sum_{x=1}^{B} e_p(x^3 + b x^2 + c x)$. Then
$|S| < (Bp)^{1/4} \left(\log \frac{B^3}{p}\right)^{1/4} (\log (Bp))^{1/4}$ and
$|S| < (Bp)^{1/4} (\log p)^{1/2}$.

The second bound is stated on the same range $4 p^{1/3} < B < \sqrt{p/12}$ as the first,
although the source states it for $B < \sqrt{p/12}$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Theorem 1.4 (`integers-2025-A48-thm-1-4`). -/
public theorem_wanted norm_incomplete_monic_cubic_sum_lt (p : ℕ) (hp : p.Prime) (b c : ℤ)
    (B : ℕ) (hB₁ : 4 * (p : ℝ) ^ ((1 : ℝ) / 3) < B) (hB₂ : (B : ℝ) < Real.sqrt (p / 12)) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((x ^ 3 + b * x ^ 2 + c * x : ℤ) : ℂ) / p)‖ <
        ((B : ℝ) * p) ^ ((1 : ℝ) / 4) * Real.log ((B : ℝ) ^ 3 / p) ^ ((1 : ℝ) / 4) *
          Real.log ((B : ℝ) * p) ^ ((1 : ℝ) / 4) ∧
      ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((x ^ 3 + b * x ^ 2 + c * x : ℤ) : ℂ) / p)‖ <
        ((B : ℝ) * p) ^ ((1 : ℝ) / 4) * Real.log p ^ ((1 : ℝ) / 2)

/-- **Completing an incomplete exponential sum.** Let $p$ be a prime, write
$e_p(t) = e^{2\pi i t/p}$, let $f$ be a polynomial with integer coefficients, and let $B$ be an
integer with $1 \le B \le p$. Put
$T_p(B) = \frac{1}{p} \sum_{y=1}^{p-1} \left|\frac{\sin(\pi B y/p)}{\sin(\pi y/p)}\right|$ and
$M = \max_{1 \le y \le p-1} \left|\sum_{x=1}^{p} e_p(f(x) + yx)\right|$. Then there is a complex
number $\theta$ with $|\theta| \le 1$ such that
$\sum_{x=1}^{B} e_p(f(x)) = \frac{B}{p} \sum_{x=1}^{p} e_p(f(x)) + \theta \, T_p(B) \, M$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 2.1 (`integers-2025-A48-lem-2-1`). -/
public theorem_wanted exists_incompleteSum_eq_completeSum_add (p : ℕ) (hp : p.Prime)
    (f : Polynomial ℤ) (B : ℕ) (hB₁ : 1 ≤ B) (hB₂ : B ≤ p) :
    ∃ θ : ℂ, ‖θ‖ ≤ 1 ∧
      ∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((f.eval (x : ℤ) : ℤ) : ℂ) / p) =
        ((B : ℂ) / p) * ∑ x ∈ Icc 1 p, exp (2 * Real.pi * I * ((f.eval (x : ℤ) : ℤ) : ℂ) / p) +
          θ * (((1 / p : ℝ) * ∑ y ∈ Icc 1 (p - 1),
              |Real.sin (Real.pi * B * y / p) / Real.sin (Real.pi * y / p)| : ℝ) : ℂ) *
            ((((Icc 1 (p - 1)).sup fun y : ℕ =>
              ‖∑ x ∈ Icc 1 p,
                exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖₊ : NNReal) : ℝ) : ℂ)

/-- **Lower bound for the maximal twisted complete exponential sum.** Let $p$ be a prime, let $f$
be a polynomial with integer coefficients, and write $e_p(t) = e^{2\pi i t / p}$ for integers $t$.
Then
$$\max_{0 \le y \le p - 1} \left| \sum_{x=1}^{p} e_p(f(x) + yx) \right| \ge \sqrt{p}.$$

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 2.2 (`integers-2025-A48-lem-2-2`). -/
public theorem_wanted sqrt_le_sup_norm_completeSum (p : ℕ) (hp : p.Prime) (f : Polynomial ℤ) :
    Real.sqrt p ≤
      (((range p).sup fun y : ℕ =>
        ‖∑ x ∈ Icc 1 p,
          exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖₊ : NNReal) : ℝ)

/-- **Explicit completion bound for incomplete exponential sums.** Let $p$ be a prime, write
$e_p(t) = e^{2\pi i t/p}$, let $f$ be a polynomial with integer coefficients whose reduction
modulo $p$ has degree at least $2$, and let $B$ be an integer with $1 \le B \le p$. Put
$\Phi(f, p) = \max_{0 \le y \le p-1} \left|\sum_{x=1}^{p} e_p(f(x) + yx)\right|$. Then
$\left|\sum_{x=1}^{B} e_p(f(x))\right| \le
\min\left\{\frac{2}{\pi^2} \log p + 3.29 + \frac{B}{p},
\frac{4}{\pi^2} \log p + \frac{B}{p} + 0.35\right\} \Phi(f, p)$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Theorem 1.1 (`integers-2025-A48-thm-1-1`). -/
public theorem_wanted norm_incompleteSum_le_min_mul_sup (p : ℕ) (hp : p.Prime)
    (f : Polynomial ℤ) (hf : 2 ≤ (f.map (Int.castRingHom (ZMod p))).natDegree) (B : ℕ)
    (hB₁ : 1 ≤ B) (hB₂ : B ≤ p) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((f.eval (x : ℤ) : ℤ) : ℂ) / p)‖ ≤
      min (2 / Real.pi ^ 2 * Real.log p + 3.29 + B / p)
          (4 / Real.pi ^ 2 * Real.log p + B / p + 0.35) *
        (((range p).sup fun y : ℕ =>
          ‖∑ x ∈ Icc 1 p,
            exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖₊ : NNReal) : ℝ)

/-- **Logarithmic completion bound for incomplete exponential sums.** Let $p \ge 5$ be a prime,
write $e_p(t) = e^{2\pi i t/p}$, let $f$ be a polynomial with integer coefficients whose reduction
modulo $p$ has degree at least $2$, and let $B$ be an integer with $1 \le B \le p$. Put
$\Phi(f, p) = \max_{0 \le y \le p-1} \left|\sum_{x=1}^{p} e_p(f(x) + yx)\right|$. Then
$\left|\sum_{x=1}^{B} e_p(f(x))\right| < \Phi(f, p) \log p$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Corollary 1.1 (`integers-2025-A48-cor-1-1`). -/
public theorem_wanted norm_incompleteSum_lt_sup_mul_log (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (f : Polynomial ℤ) (hf : 2 ≤ (f.map (Int.castRingHom (ZMod p))).natDegree) (B : ℕ)
    (hB₁ : 1 ≤ B) (hB₂ : B ≤ p) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((f.eval (x : ℤ) : ℤ) : ℂ) / p)‖ <
      (((range p).sup fun y : ℕ =>
          ‖∑ x ∈ Icc 1 p,
            exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖₊ : NNReal) : ℝ) *
        Real.log p

/-- **Bound for a truncated sum of reciprocal sines.** Let $p$ be a prime, let $a$ be an integer
not divisible by $p$, and let $B$ be an integer with $\sqrt{p/\pi} < B < p/2$. Then
$$
\sum_{h=1}^{B} \min\left\{B, \frac{1}{|\sin(\pi a h / p)|}\right\} <
\frac{p}{\pi}\left(\log\frac{\pi B^2}{p} + 1 + \frac{\pi B}{p}\right) +
\frac{pB(B+1)}{\pi(p^2 - B^2)}.
$$

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.3 (`integers-2025-A48-lem-3-3`). -/
public theorem_wanted sum_min_one_div_abs_sin_lt (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : Real.sqrt (p / Real.pi) < B) (hB₂ : (B : ℝ) < p / 2) :
    ∑ h ∈ Icc 1 B, min (B : ℝ) (1 / |Real.sin (Real.pi * a * h / p)|) <
      (p / Real.pi) * (Real.log (Real.pi * B ^ 2 / p) + 1 + Real.pi * B / p) +
        p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2))

/-- **Bound for a sum of sine ratios.** Let $q$, $K$ and $B$ be natural numbers with
$1 \le K < q$ and $B \ge 1$, and let $\gamma$ be the Euler–Mascheroni constant. Then
$$
\sum_{k=1}^{K} \frac{|\sin(\pi B k / q)|}{|\sin(\pi k / q)|} <
\frac{2}{\pi^2} q \log K + \frac{2q}{\pi^2}(\gamma + \log 2) + \frac{q}{\pi} \cdot \frac{K}{q - K} +
\frac{5q}{\pi^2 K}.
$$

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.5 (`integers-2025-A48-lem-3-5`). -/
public theorem_wanted sum_abs_sin_div_abs_sin_lt (q K B : ℕ) (hK : 1 ≤ K) (hKq : K < q)
    (hB : 1 ≤ B) :
    ∑ k ∈ Icc 1 K, |Real.sin (Real.pi * B * k / q)| / |Real.sin (Real.pi * k / q)| <
      2 / Real.pi ^ 2 * q * Real.log K +
          2 * q / Real.pi ^ 2 * (Real.eulerMascheroniConstant + Real.log 2) +
        q / Real.pi * (K / ((q : ℝ) - K)) + 5 * q / (Real.pi ^ 2 * K)

/-- **Square of an incomplete quadratic exponential sum.** Let $p$ be a prime, write
$e_p(t) = e^{2\pi i t/p}$, let $a, b, c$ be integers with $p \nmid a$, let $B$ be an integer with
$\sqrt{p} < B < p/2$, and put $S = \sum_{x=1}^{B} e_p(a x^2 + b x + c)$ and
$R = \frac{2pB(B+1)}{\pi(p^2 - B^2)}$. Then $|S|^2$ is at most the minimum of
$\frac{2p}{\pi} \log \frac{B^2}{p} + 1.366 p + 3B + R$ and
$\frac{2p}{\pi} \log B + 0.368 p + B + \frac{p}{\pi B} + R$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Proposition 6.1 (`integers-2025-A48-prop-6-1`). -/
public theorem_wanted norm_sq_incomplete_quadratic_sum_le (p : ℕ) (hp : p.Prime) (a b c : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : Real.sqrt p < B) (hB₂ : (B : ℝ) < p / 2) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((a * x ^ 2 + b * x + c : ℤ) : ℂ) / p)‖ ^ 2 ≤
      min (2 * p / Real.pi * Real.log ((B : ℝ) ^ 2 / p) + 1.366 * p + 3 * B +
            2 * p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)))
        (2 * p / Real.pi * Real.log B + 0.368 * p + B + p / (Real.pi * B) +
            2 * p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)))

/-- **Uniform bound for incomplete quadratic exponential sums.** Let $p$ be a prime, write
$e_p(t) = e^{2\pi i t/p}$, let $a, b, c$ be integers with $p \nmid a$, and let $B$ be an integer
with $1 \le B \le p$. Then $\left|\sum_{x=1}^{B} e_p(a x^2 + b x + c)\right| <
\sqrt{p} + \sqrt{\frac{2}{\pi} p \log p + \frac{p}{2}}$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Corollary 6.1 (`integers-2025-A48-cor-6-1`). -/
public theorem_wanted norm_incomplete_quadratic_sum_lt_sqrt_add_sqrt (p : ℕ) (hp : p.Prime)
    (a b c : ℤ) (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : 1 ≤ B) (hB₂ : B ≤ p) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((a * x ^ 2 + b * x + c : ℤ) : ℂ) / p)‖ <
      Real.sqrt p + Real.sqrt (2 / Real.pi * p * Real.log p + p / 2)

/-- **Explicit bounds for incomplete cubic exponential sums.** Let $p \ge 3$ be a prime, write
$e_p(t) = e^{2\pi i t/p}$ and $\delta_p = \frac{1.0661}{\log \log p}$, let $a, b, c$ be integers
with $p \nmid a$, let $B$ be a positive integer, and put
$S = \sum_{x=1}^{B} e_p(a x^3 + b x^2 + c x)$. If $B < \sqrt{p/2}$, then
$|S| \le 1.1 \, B^{1/4} p^{1/4 + \delta_p/4} (\log p)^{1/4}$. If $\sqrt{p/2} < B \le p$, then
$|S| \le 1.38 \, (1 + p/B^2)^{1/4} B^{3/4} p^{\delta_p/2} (\log p)^{1/4}$.

The hypothesis $p \ge 3$ makes $\log \log p > 0$. For $p = 2$, $f(x) = x^3 + x$ and $B = 2$,
the sum equals $2$ while the second bound is below $0.86$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Theorem 1.3 (`integers-2025-A48-thm-1-3`). -/
public theorem_wanted norm_incomplete_cubic_sum_le (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (a b c : ℤ) (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB : 1 ≤ B) :
    ((B : ℝ) < Real.sqrt (p / 2) →
      ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((a * x ^ 3 + b * x ^ 2 + c * x : ℤ) : ℂ) / p)‖ ≤
        1.1 * (B : ℝ) ^ ((1 : ℝ) / 4) *
            (p : ℝ) ^ ((1 : ℝ) / 4 + 1.0661 / Real.log (Real.log p) / 4) *
          Real.log p ^ ((1 : ℝ) / 4)) ∧
    (Real.sqrt (p / 2) < B → B ≤ p →
      ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((a * x ^ 3 + b * x ^ 2 + c * x : ℤ) : ℂ) / p)‖ ≤
        1.38 * (1 + p / (B : ℝ) ^ 2) ^ ((1 : ℝ) / 4) * (B : ℝ) ^ ((3 : ℝ) / 4) *
            (p : ℝ) ^ (1.0661 / Real.log (Real.log p) / 2) *
          Real.log p ^ ((1 : ℝ) / 4))

/-- **Explicit asymptotic for the logarithmic mean of the divisor function.** Let $\tau(n)$ be
the number of positive divisors of $n$ and let $\gamma$ be the Euler–Mascheroni constant. There
is a real constant $C$ such that $\sum_{k=1}^{N} \frac{\log k}{k} - \frac{(\log N)^2}{2}$ tends
to $\frac{\gamma^2 - C}{2}$ as $N \to \infty$ and such that for every real $x \ge 2$,
$\left|\sum_{1 \le n \le x} \frac{\tau(n)}{n} -
\left(\frac{(\log x)^2}{2} + 2\gamma \log x + C\right)\right| \le \frac{2.1 \log x}{x^{2/3}}$.

The first condition says that $C = \gamma^2 - 2\gamma_1$, where
$\gamma_1 = \lim_{N \to \infty} \left(\sum_{k=1}^{N} \frac{\log k}{k} - \frac{(\log N)^2}{2}\right)$
is the first Stieltjes constant.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 7.1 (`integers-2025-A48-lem-7-1`). -/
public theorem_wanted exists_sum_card_divisors_div_sub_le :
    ∃ C : ℝ,
      Filter.Tendsto
          (fun N : ℕ => ∑ k ∈ Icc 1 N, Real.log k / k - Real.log N ^ 2 / 2)
          Filter.atTop (nhds ((Real.eulerMascheroniConstant ^ 2 - C) / 2)) ∧
        ∀ x : ℝ, 2 ≤ x →
          |∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ) / n -
              (Real.log x ^ 2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log x + C)| ≤
            2.1 * Real.log x / x ^ ((2 : ℝ) / 3)

end

end MetaMathlibExt
