/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The log moments of smallest denominators

Statements from Jens Marklof, *The Log Moments of Smallest Denominators*,
INTEGERS 24 (2024), Article A55 (arXiv:2312.15303).

`q_min(x, δ)` is the smallest denominator of a rational number in the open
interval of length `δ` centred at `x`. The limit law of
`log q_min(x, δ) + ½ log δ` for uniformly random `x` has the explicit density
`η_log` of the paper's Equation (1.3).
-/

open Filter Topology MeasureTheory

namespace MetaMathlibExt

@[expose] public section

/-- **Smallest denominator in an interval.** For real numbers $x$ and $\delta$, the smallest
denominator $q_{\min}(x, \delta)$ is the least positive integer $q$ for which there is an integer
$p$ with $|x - p/q| < \delta/2$, that is, with $p/q$ in the open interval
$(x - \delta/2, x + \delta/2)$. If there is no such $q$, which happens only when $\delta \le 0$,
then $q_{\min}(x, \delta) = 0$.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
noncomputable def smallestDenominator (x δ : ℝ) : ℕ :=
  sInf {q : ℕ | 0 < q ∧ ∃ p : ℤ, |x - p / q| < δ / 2}

/-- **Denominators of nearby rationals bound the smallest denominator.** Let $x$ and $\delta$ be
real numbers, let $q$ be a positive integer and let $p$ be an integer. If $|x - p/q| < \delta/2$,
then the smallest denominator satisfies $q_{\min}(x, \delta) \le q$.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
theorem smallestDenominator_le {x δ : ℝ} {q : ℕ} {p : ℤ} (hq : 0 < q)
    (hp : |x - p / q| < δ / 2) : smallestDenominator x δ ≤ q :=
  Nat.sInf_le ⟨hq, p, hp⟩

/-- **Every real number has arbitrarily close rationals.** For every real number $x$ and every
real $\delta > 0$ there are a positive integer $q$ and an integer $p$ with $|x - p/q| < \delta/2$.

Taking $q > 1/\delta$ and $p$ the integer nearest to $qx$ gives
$|x - p/q| \le 1/(2q) < \delta/2$.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
theorem exists_denominator_mem_window (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ, 0 < q ∧ ∃ p : ℤ, |x - p / q| < δ / 2 := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / δ)
  have hq0 : (0 : ℝ) < q := lt_trans (by positivity) hq
  refine ⟨q, by exact_mod_cast hq0, round (x * q), ?_⟩
  have h1 := abs_sub_round (x * q)
  have h2 : x - (round (x * q) : ℝ) / q = (x * q - round (x * q)) / q := by
    field_simp
  have h3 : 1 < q * δ := by
    rw [div_lt_iff₀ hδ] at hq
    linarith
  rw [h2, abs_div, abs_of_pos hq0, div_lt_iff₀ hq0]
  nlinarith

/-- **The smallest denominator is positive and attained.** For every real number $x$ and every
real $\delta > 0$, the smallest denominator $q = q_{\min}(x, \delta)$ is positive and there is an
integer $p$ with $|x - p/q| < \delta/2$.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
theorem smallestDenominator_spec (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    0 < smallestDenominator x δ ∧
      ∃ p : ℤ, |x - p / smallestDenominator x δ| < δ / 2 :=
  Nat.sInf_mem (exists_denominator_mem_window x hδ)

/-- **Minimality of the smallest denominator.** Let $x$ and $\delta$ be real numbers and let $q$
be a positive integer with $q < q_{\min}(x, \delta)$, where $q_{\min}(x, \delta)$ is the smallest
denominator. Then there is no integer $p$ with $|x - p/q| < \delta/2$.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
theorem not_mem_window_of_lt_smallestDenominator {x δ : ℝ} {q : ℕ} (hq : 0 < q)
    (hlt : q < smallestDenominator x δ) (p : ℤ) : ¬ |x - p / q| < δ / 2 :=
  fun hp => absurd (smallestDenominator_le hq hp) (not_le.mpr hlt)

/-- **Upper bounds on the smallest denominator.** Let $x$ be a real number, let $\delta > 0$ be
real, let $q$ be a natural number and let $q_{\min}(x, \delta)$ be the smallest denominator. Then
$q_{\min}(x, \delta) \le q$ if and only if there are a positive integer $q' \le q$ and an integer
$p$ with $|x - p/q'| < \delta/2$.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
theorem smallestDenominator_le_iff (x : ℝ) {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    smallestDenominator x δ ≤ q ↔ ∃ q' ≤ q, 0 < q' ∧ ∃ p : ℤ, |x - p / q'| < δ / 2 := by
  constructor
  · intro h
    exact ⟨_, h, smallestDenominator_spec x hδ⟩
  · rintro ⟨q', hq', hq0, p, hp⟩
    exact (smallestDenominator_le hq0 hp).trans hq'

/-- **Wide intervals have smallest denominator one.** For every real number $x$ and every real
$\delta > 1$, the smallest denominator $q_{\min}(x, \delta)$ equals $1$.

The open interval $(x - \delta/2, x + \delta/2)$ has length greater than $1$, so it contains an
integer.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
theorem smallestDenominator_eq_one {x δ : ℝ} (hδ : 1 < δ) : smallestDenominator x δ = 1 := by
  have hmem : (1 : ℕ) ∈ {q : ℕ | 0 < q ∧ ∃ p : ℤ, |x - p / q| < δ / 2} := by
    refine ⟨one_pos, round x, ?_⟩
    have h := abs_sub_round x
    simp only [Nat.cast_one, div_one]
    linarith
  refine le_antisymm (Nat.sInf_le hmem) ?_
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rcases Nat.sInf_eq_zero.mp h0 with h | h
  · exact absurd h.1 (lt_irrefl 0)
  · rw [h] at hmem
    exact hmem

/-- **Density of the logarithmic smallest denominator.** The function $\eta_{\log}$ on the real
line is defined by $\eta_{\log}(s) = \frac{6}{\pi^2} e^{2s}$ for $s \le 0$, by
$\eta_{\log}(s) = \frac{6}{\pi^2}\left(-e^{2s} + 2 + 4s\right)$ for $0 < s \le \log 2$, and by
$$
\eta_{\log}(s) = \frac{6}{\pi^2}\left(-e^{2s} + 2 + 2e^{2s}\sqrt{\tfrac14 - e^{-2s}} -
4\log\left(\tfrac12 + \sqrt{\tfrac14 - e^{-2s}}\right)\right)
$$
for $s > \log 2$.

In the cited paper, $\eta_{\log}$ is the density of the limit law, as $\delta \to 0^+$, of
$\log q_{\min}(x, \delta) + \frac12 \log \delta$ for uniformly random $x$, where
$q_{\min}(x, \delta)$ is the smallest denominator of a rational in $(x - \delta/2, x + \delta/2)$.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.3). -/
noncomputable def logSmallestDenominatorDensity (s : ℝ) : ℝ :=
  6 / Real.pi ^ 2 *
    if s ≤ 0 then Real.exp (2 * s)
    else if s ≤ Real.log 2 then -Real.exp (2 * s) + 2 + 4 * s
    else -Real.exp (2 * s) + 2 + 2 * Real.exp (2 * s) * Real.sqrt (1 / 4 - Real.exp (-2 * s)) -
      4 * Real.log (1 / 2 + Real.sqrt (1 / 4 - Real.exp (-2 * s)))

/-- **Value of the log smallest-denominator density at zero.** The density $\eta_{\log}$ of the
logarithmic smallest denominator satisfies $\eta_{\log}(0) = 6/\pi^2$.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.3). -/
theorem logSmallestDenominatorDensity_zero : logSmallestDenominatorDensity 0 = 6 / Real.pi ^ 2 := by
  simp [logSmallestDenominatorDensity]

/-- **The log smallest-denominator density for nonpositive arguments.** For every real $s \le 0$,
the density $\eta_{\log}$ of the logarithmic smallest denominator satisfies
$\eta_{\log}(s) = \frac{6}{\pi^2} e^{2s}$.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.3). -/
theorem logSmallestDenominatorDensity_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    logSmallestDenominatorDensity s = 6 / Real.pi ^ 2 * Real.exp (2 * s) := by
  simp [logSmallestDenominatorDensity, hs]

/-- **Limit law of the smallest denominator.** For real $x$ and $\delta > 0$ let
$q_{\min}(x, \delta)$ be the smallest positive integer $q$ such that some rational $p/q$ lies in
the open interval $(x - \delta/2, x + \delta/2)$, and let $\eta_{\log}$ be the log smallest
denominator density. Then $\eta_{\log}$ is a probability density on $\mathbb{R}$:
$\eta_{\log}(s) \ge 0$ for every real $s$ and $\int_{-\infty}^{\infty} \eta_{\log}(s) \, ds = 1$.
Moreover, for all real numbers $a$, $b$, $L$ with $0 \le a \le b \le 1$, as $\delta \to 0^+$ the
Lebesgue measure of $\{x \in [a, b] : \log q_{\min}(x, \delta) > L - \tfrac12 \log \delta\}$
tends to $(b - a) \int_L^\infty \eta_{\log}(s) \, ds$.

The interval is taken closed; its endpoints do not affect the measures.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Proposition 1 (`integers-2024-A55-prop-1`). -/
public theorem_wanted tendsto_volume_log_smallestDenominator_gt (a b L : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    (∀ s, 0 ≤ logSmallestDenominatorDensity s) ∧ ∫ s, logSmallestDenominatorDensity s = 1 ∧
      Tendsto (fun δ => (volume {x ∈ Set.Icc a b |
          L - Real.log δ / 2 < Real.log (smallestDenominator x δ)}).toReal)
        (𝓝[>] 0) (𝓝 ((b - a) * ∫ s in Set.Ioi L, logSmallestDenominatorDensity s))

/-- **Convergence of the log moments of smallest denominators.** Let $0 \le a \le b \le 1$ be
real numbers and let $n \ge 0$ be an integer. For real $x$ and $\delta > 0$ let
$q_{\min}(x, \delta)$ be the smallest positive integer $q$ such that some rational $p/q$ lies in
the open interval $(x - \delta/2, x + \delta/2)$, and let $\eta_{\log}$ be the log smallest
denominator density. Then, as $\delta \to 0^+$,
$$
\int_a^b \bigl(\log q_{\min}(x, \delta) + \tfrac12 \log \delta\bigr)^n \, dx \to \mu_n \, (b - a),
$$
where $\mu_n = \int_{-\infty}^{\infty} s^n \, \eta_{\log}(s) \, ds$.

The moment $\mu_n$ is an integral over the whole real line: $\eta_{\log}$ has mass $3/\pi^2$ on
$(-\infty, 0]$, so integrating only over $s \ge 0$ would give $\mu_0 = 1 - 3/\pi^2$ instead of
the correct limit $1$.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Proposition 2 (`integers-2024-A55-prop-2`). -/
public theorem_wanted tendsto_integral_log_smallestDenominator_pow (a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) (n : ℕ) :
    Tendsto (fun δ => ∫ x in Set.Icc a b,
        (Real.log (smallestDenominator x δ) + Real.log δ / 2) ^ n)
      (𝓝[>] 0) (𝓝 ((∫ s, s ^ n * logSmallestDenominatorDensity s) * (b - a)))

end

end MetaMathlibExt
