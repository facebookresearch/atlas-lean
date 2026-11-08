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

/-- The smallest denominator `q_min(x, δ)`: the least `q ≥ 1` such that some
rational `p / q` lies in `(x - δ/2, x + δ/2)` (`0` if there is none, which only
happens for `δ ≤ 0`).

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
noncomputable def smallestDenominator (x δ : ℝ) : ℕ :=
  sInf {q : ℕ | 0 < q ∧ ∃ p : ℤ, |x - p / q| < δ / 2}

/-- Any denominator of a rational in the window bounds `q_min(x, δ)`.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
theorem smallestDenominator_le {x δ : ℝ} {q : ℕ} {p : ℤ} (hq : 0 < q)
    (hp : |x - p / q| < δ / 2) : smallestDenominator x δ ≤ q :=
  Nat.sInf_le ⟨hq, p, hp⟩

/-- For `δ > 0` some rational lies in the window: with `q > 1/δ` and `p` the integer nearest to
`q x`, `|x - p/q| ≤ 1/(2q) < δ/2`.

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

/-- For `δ > 0`, `q_min(x, δ)` is positive and attained: some rational `p / q_min(x, δ)` lies in
the window.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
theorem smallestDenominator_spec (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    0 < smallestDenominator x δ ∧
      ∃ p : ℤ, |x - p / smallestDenominator x δ| < δ / 2 :=
  Nat.sInf_mem (exists_denominator_mem_window x hδ)

/-- Minimality of `q_min(x, δ)`: no positive `q < q_min(x, δ)` is the denominator of a rational
in the window.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
theorem not_mem_window_of_lt_smallestDenominator {x δ : ℝ} {q : ℕ} (hq : 0 < q)
    (hlt : q < smallestDenominator x δ) (p : ℤ) : ¬ |x - p / q| < δ / 2 :=
  fun hp => absurd (smallestDenominator_le hq hp) (not_le.mpr hlt)

/-- For `δ > 0`, `q_min(x, δ) ≤ q` exactly when some positive `q' ≤ q` is the denominator of a
rational in the window.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.1). -/
theorem smallestDenominator_le_iff (x : ℝ) {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    smallestDenominator x δ ≤ q ↔ ∃ q' ≤ q, 0 < q' ∧ ∃ p : ℤ, |x - p / q'| < δ / 2 := by
  constructor
  · intro h
    exact ⟨_, h, smallestDenominator_spec x hδ⟩
  · rintro ⟨q', hq', hq0, p, hp⟩
    exact (smallestDenominator_le hq0 hp).trans hq'

/-- For `δ > 1` the window always contains an integer, so `q_min(x, δ) = 1`.

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

/-- The limit density `η_log(s)` of `log q_min(x, δ) + ½ log δ`:
`(6/π²) e^{2s}` for `s ≤ 0`, `(6/π²)(-e^{2s} + 2 + 4s)` for `0 ≤ s ≤ log 2`, and
`(6/π²)(-e^{2s} + 2 + 2 e^{2s} √(1/4 - e^{-2s}) - 4 log(1/2 + √(1/4 - e^{-2s})))`
for `s ≥ log 2`.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.3). -/
noncomputable def logSmallestDenominatorDensity (s : ℝ) : ℝ :=
  6 / Real.pi ^ 2 *
    if s ≤ 0 then Real.exp (2 * s)
    else if s ≤ Real.log 2 then -Real.exp (2 * s) + 2 + 4 * s
    else -Real.exp (2 * s) + 2 + 2 * Real.exp (2 * s) * Real.sqrt (1 / 4 - Real.exp (-2 * s)) -
      4 * Real.log (1 / 2 + Real.sqrt (1 / 4 - Real.exp (-2 * s)))

/-- `η_log(0) = 6/π²`.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.3). -/
theorem logSmallestDenominatorDensity_zero : logSmallestDenominatorDensity 0 = 6 / Real.pi ^ 2 := by
  simp [logSmallestDenominatorDensity]

/-- On `s ≤ 0`, `η_log(s) = (6/π²) e^{2s}`.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Equation (1.3). -/
theorem logSmallestDenominatorDensity_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    logSmallestDenominatorDensity s = 6 / Real.pi ^ 2 * Real.exp (2 * s) := by
  simp [logSmallestDenominatorDensity, hs]

/-- Limit law of the smallest denominator: `η_log` is a probability density (nonnegative with
total integral `1`) and,
for an interval `D = [a, b] ⊆ [0, 1]` and `L ∈ ℝ`,
`vol {x ∈ D : log q_min(x, δ) > L - ½ log δ} → vol D · ∫_L^∞ η_log(s) ds` as
`δ → 0⁺`. The interval is taken closed (endpoints do not affect volumes).

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Proposition 1 (`integers-2024-A55-prop-1`). -/
public theorem_wanted tendsto_volume_log_smallestDenominator_gt (a b L : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    (∀ s, 0 ≤ logSmallestDenominatorDensity s) ∧ ∫ s, logSmallestDenominatorDensity s = 1 ∧
      Tendsto (fun δ => (volume {x ∈ Set.Icc a b |
          L - Real.log δ / 2 < Real.log (smallestDenominator x δ)}).toReal)
        (𝓝[>] 0) (𝓝 ((b - a) * ∫ s in Set.Ioi L, logSmallestDenominatorDensity s))

/-- Convergence of the logarithmic moments: for an interval `D = [a, b] ⊆ [0, 1]`
and `n ≥ 0`, `∫_D (log q_min(x, δ) + ½ log δ)^n dx → μ_n vol D` as `δ → 0⁺`, with
`μ_n = ∫ s^n η_log(s) ds` over all of `ℝ`. The record prints the lower limit `0`;
the whole line is used, as the paper's own second expression
`∫_0^∞ (log s)^n η(s) ds` with `η_log(s) = e^s η(e^s)` gives (with lower limit
`0`, `n = 0` would give `μ_0 = 1 - 3/π² ≠ 1 = lim ∫_D 1 / vol D`). The second
expression, through the density `η` of the cited paper, is not included.

Source: Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24
(2024), Article A55, Proposition 2 (`integers-2024-A55-prop-2`). -/
public theorem_wanted tendsto_integral_log_smallestDenominator_pow (a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) (n : ℕ) :
    Tendsto (fun δ => ∫ x in Set.Icc a b,
        (Real.log (smallestDenominator x δ) + Real.log δ / 2) ^ n)
      (𝓝[>] 0) (𝓝 ((∫ s, s ^ n * logSmallestDenominatorDensity s) * (b - a)))

end

end MetaMathlibExt
