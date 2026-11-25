/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Steady-state morphogen gradient and French-flag boundaries

A morphogen is secreted at `x = 0` with flux `j > 0` into the half-line `x ≥ 0`, diffuses with
coefficient `D > 0` and is degraded at rate `k > 0` (synthesis–diffusion–degradation model
with linear degradation). Its steady-state concentration solves

  `D c'' = k c` on `x > 0`,   `-D c'(0) = j`,   `c` bounded on `[0, ∞)`.

The unique solution is the exponential gradient `c(x) = (j / √(D k)) e^{-x/λ}` with decay
length `λ = √(D / k)` (`isSteadyState_profile`, `eq_profile_of_isSteadyState`). In Wolpert's
French-flag model a cell at `x` reads its fate from whether `c(x)` exceeds a threshold `θ`;
the boundary is at `x_θ = λ log(c(0)/θ)` (`profile_eq_iff`, `le_profile_iff`), and scaling the
source flux by `a > 0` moves every boundary by `λ log a`; doubling the source shifts it by
`λ log 2` (`thresholdPosition_mul`, `thresholdPosition_two_mul`).

## Main results

* `profile`, `decayLength`, `thresholdPosition`.
* `isSteadyState_profile`: the exponential profile is a bounded steady state with flux `j`.
* `eq_profile_of_isSteadyState`: it is the only one.
* `le_profile_iff`: `θ ≤ c(x)` iff `x ≤ x_θ` (cells closer to the source than `x_θ` are above
  threshold).
* `thresholdPosition_mul`: `x_θ(a j) = x_θ(j) + λ log a`.

The shift `λ log 2` under a twofold change of production is the computation behind the
observation of Eldar et al. (2003) that exponential (linear-degradation) profiles do not buffer
fluctuations in morphogen production; it is derived here from the closed form.

## References

* L. Wolpert, *Positional information and the spatial pattern of cellular differentiation*,
  J. Theor. Biol. 25 (1969) 1–47.
* F. Crick, *Diffusion in embryogenesis*, Nature 225 (1970) 420–422.
* O. Wartlick, A. Kicheva and M. González-Gaitán, *Morphogen gradient formation*, Cold Spring
  Harb. Perspect. Biol. 1 (2009) a001255.
* A. Eldar, D. Rosin, B.-Z. Shilo and N. Barkai, *Self-enhanced ligand degradation underlies
  robustness of morphogen gradients*, Dev. Cell 5 (2003) 635–646.
-/

@[expose] public section

open Real Set

namespace MathlibExt.Biology.Dynamics.MorphogenGradient

/-- The decay length `λ = √(D / k)` of a morphogen with diffusion coefficient `D` and linear
degradation rate `k` (both positive in the model). -/
noncomputable def decayLength (D k : ℝ) : ℝ :=
  √(D / k)

/-- The steady-state gradient `c(x) = (j / √(D k)) e^{-x/λ}`, `λ = √(D / k)`, for source flux
`j` at `x = 0`. Meaningful for `D, k > 0`. -/
noncomputable def profile (D k j x : ℝ) : ℝ :=
  j / √(D * k) * exp (-x / decayLength D k)

/-- The French-flag boundary for threshold `θ`: `x_θ = λ log(c(0) / θ)`, where
`c(0) = j / √(D k)`. Meaningful for `D, k, j, θ > 0`; it is negative when `θ > c(0)` (no cell
is above threshold). -/
noncomputable def thresholdPosition (D k j θ : ℝ) : ℝ :=
  decayLength D k * log (j / √(D * k) / θ)

/-- A bounded steady state of the synthesis–diffusion–degradation model on `[0, ∞)`, with
`c' = dc/dx`: `D c'' = k c` for `x > 0`, `c` and `c'` continuous up to the source, source flux
`-D c'(0) = j`, and `c` bounded on `[0, ∞)`. -/
structure IsSteadyState (D k j : ℝ) (c c' : ℝ → ℝ) : Prop where
  hasDerivAt_conc : ∀ x, 0 < x → HasDerivAt c (c' x) x
  hasDerivAt_grad : ∀ x, 0 < x → HasDerivAt c' (k / D * c x) x
  continuousOn_conc : ContinuousOn c (Ici 0)
  continuousOn_grad : ContinuousOn c' (Ici 0)
  source_flux : -D * c' 0 = j
  bounded : ∃ B, ∀ x, 0 ≤ x → |c x| ≤ B

/-- The decay length is positive for positive `D` and `k`. -/
theorem decayLength_pos {D k : ℝ} (hD : 0 < D) (hk : 0 < k) : 0 < decayLength D k :=
  sqrt_pos.2 (div_pos hD hk)

/-- `D / λ² = k`. -/
theorem div_decayLength_sq {D k : ℝ} (hD : 0 < D) (hk : 0 < k) :
    D / decayLength D k ^ 2 = k := by
  rw [decayLength, sq_sqrt (div_pos hD hk).le]; field_simp

/-- `√(D k) = D / λ`, so the source amplitude is `c(0) = j λ / D`. -/
theorem sqrt_mul_eq {D k : ℝ} (hD : 0 < D) (hk : 0 < k) :
    √(D * k) = D / decayLength D k := by
  have hl := decayLength_pos hD hk
  rw [eq_div_iff hl.ne', decayLength, ← sqrt_mul (mul_pos hD hk).le]
  rw [show D * k * (D / k) = D ^ 2 by field_simp]
  exact sqrt_sq hD.le

/-- The profile has slope `c'(x) = -c(x)/λ`. -/
theorem hasDerivAt_profile (D k j x : ℝ) :
    HasDerivAt (profile D k j) (-profile D k j x / decayLength D k) x := by
  have h := ((hasDerivAt_neg x).div_const (decayLength D k)).exp.const_mul (j / √(D * k))
  unfold profile
  convert h using 1
  ring

/-- The exponential profile is a bounded steady state with source flux `j`. -/
theorem isSteadyState_profile {D k j : ℝ} (hD : 0 < D) (hk : 0 < k) :
    IsSteadyState D k j (profile D k j) (fun x ↦ -profile D k j x / decayLength D k) := by
  have hl := decayLength_pos hD hk
  refine ⟨fun x _ ↦ hasDerivAt_profile D k j x, fun x _ ↦ ?_, ?_, ?_, ?_, ?_⟩
  · have h := ((hasDerivAt_profile D k j x).neg).div_const (decayLength D k)
    have hkD : k / D = 1 / decayLength D k ^ 2 := by
      rw [decayLength, sq_sqrt (div_pos hD hk).le, one_div_div]
    convert h using 1
    rw [hkD]; field_simp
  · exact fun x _ ↦ (hasDerivAt_profile D k j x).continuousAt.continuousWithinAt
  · exact fun x _ ↦ ((hasDerivAt_profile D k j x).continuousAt.neg.div_const
      _).continuousWithinAt
  · simp only [profile, neg_zero, zero_div, exp_zero, mul_one]
    rw [sqrt_mul_eq hD hk]; field_simp
  · refine ⟨|j / √(D * k)|, fun x hx ↦ ?_⟩
    rw [profile, abs_mul, abs_of_pos (exp_pos _)]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (div_nonneg hx hl.le)

private theorem eq_zero_of_hasDerivAt_zero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0)) (hd : ∀ y, 0 < y → HasDerivAt f 0 y)
    {x : ℝ} (hx : 0 ≤ x) : f x = f 0 := by
  rcases hx.eq_or_lt with hx | hx
  · rw [← hx]
  · obtain ⟨y, hy, he⟩ := exists_hasDerivAt_eq_slope f (fun _ ↦ 0) hx
      (hf.mono (fun z hz ↦ hz.1)) (fun z hz ↦ hd z hz.1)
    have he' : f x - f 0 = 0 := (div_eq_zero_iff).1 he.symm |>.resolve_right (by linarith)
    exact sub_eq_zero.mp he'

private theorem integrating_factor {D k j a : ℝ} {c c' : ℝ → ℝ}
    (hc : IsSteadyState D k j c c') (ha : k / D = a ^ 2)
    {x : ℝ} (hx : 0 ≤ x) :
    exp (-a * x) * (c' x + a * c x) = c' 0 + a * c 0 := by
  have hf : ContinuousOn (fun y ↦ exp (-a * y) * (c' y + a * c y)) (Ici 0) :=
    (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hc.continuousOn_grad.add (continuousOn_const.mul hc.continuousOn_conc))
  have hd : ∀ y, 0 < y →
      HasDerivAt (fun y ↦ exp (-a * y) * (c' y + a * c y)) 0 y := by
    intro y hy
    have h := ((hasDerivAt_id y).const_mul (-a)).exp.mul
      ((hc.hasDerivAt_grad y hy).add ((hc.hasDerivAt_conc y hy).const_mul a))
    convert h using 1 <;> first | rfl | (dsimp; rw [ha]; ring)
  simpa using eq_zero_of_hasDerivAt_zero hf hd hx

/-- **Uniqueness.** Every bounded steady state with source flux `j` is the exponential
profile on `[0, ∞)`. -/
theorem eq_profile_of_isSteadyState {D k j : ℝ} (hD : 0 < D) (hk : 0 < k) {c c' : ℝ → ℝ}
    (hc : IsSteadyState D k j c c') {x : ℝ} (hx : 0 ≤ x) :
    c x = profile D k j x := by
  let l := decayLength D k
  have hl : 0 < l := decayLength_pos hD hk
  have hkD : k / D = (1 / l) ^ 2 := by
    dsimp [l]
    rw [div_pow, one_pow, decayLength, sq_sqrt (div_pos hD hk).le, one_div_div]
  have hplus (y : ℝ) (hy : 0 ≤ y) := integrating_factor hc hkD hy
  have hminus (y : ℝ) (hy : 0 ≤ y) :=
    integrating_factor hc (show k / D = (- (1 / l)) ^ 2 by
      simpa only [neg_sq] using hkD) hy
  let p := (c 0 + l * c' 0) / 2
  let q := (c 0 - l * c' 0) / 2
  have hform : ∀ y, 0 ≤ y → c y = p * exp (y / l) + q * exp (-y / l) := by
    intro y hy
    have hp := congrArg (fun z : ℝ ↦ z * exp (y / l)) (hplus y hy)
    have hm := congrArg (fun z : ℝ ↦ z * exp (-y / l)) (hminus y hy)
    have he : exp (-y / l) * exp (y / l) = 1 := by
      rw [← exp_add]
      convert exp_zero using 2
      ring
    have hp' : c' y + c y / l = (c' 0 + c 0 / l) * exp (y / l) := by
      convert hp using 1 <;> simp only [neg_mul, one_div_mul_eq_div, neg_div] at *
      rw [mul_right_comm, he, one_mul]
    have hm' : c' y - c y / l = (c' 0 - c 0 / l) * exp (-y / l) := by
      convert hm using 1 <;> simp only [neg_neg, one_div_mul_eq_div, neg_mul,
        ← sub_eq_add_neg] at *
      rw [mul_right_comm, mul_comm (exp (y / l)), he, one_mul]
    dsimp [p, q]
    field_simp [hl.ne'] at hp' hm' ⊢
    nlinarith [hp', hm']
  obtain ⟨B, hB⟩ := hc.bounded
  have hB0 : 0 ≤ B := (abs_nonneg (c 0)).trans (hB 0 le_rfl)
  have hbound : ∀ y, 0 ≤ y → |p| * exp (y / l) ≤ B + |q| := by
    intro y hy
    have hh := abs_sub (c y) (q * exp (-y / l))
    rw [hform y hy, add_sub_cancel_right, abs_mul, abs_mul,
      abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)] at hh
    have hq : |q| * exp (-y / l) ≤ |q| := by
      apply mul_le_of_le_one_right (abs_nonneg q)
      rw [exp_le_one_iff, neg_div]
      exact neg_nonpos.mpr (div_nonneg hy hl.le)
    have hb := hB y hy
    rw [hform y hy] at hb
    linarith
  have hp : p = 0 := by
    by_contra hp
    have hap : 0 < |p| := abs_pos.mpr hp
    let t := (B + |q| + 1) / |p|
    have ht : 0 ≤ t := div_nonneg (by positivity) hap.le
    have hb := hbound (l * t) (mul_nonneg hl.le ht)
    rw [mul_div_cancel_left₀ t hl.ne'] at hb
    have he : |p| * t = B + |q| + 1 := by
      dsimp [t]
      field_simp
    have hg := mul_le_mul_of_nonneg_left (add_one_le_exp t) (abs_nonneg p)
    nlinarith
  have hp0 : c 0 + l * c' 0 = 0 := by
    have := hp
    dsimp [p] at this
    linarith
  have hq0 : q = c 0 := by dsimp [q]; linarith
  have hc0 : c 0 = j / √(D * k) := by
    rw [sqrt_mul_eq hD hk]
    change c 0 = j / (D / l)
    have hf := hc.source_flux
    field_simp [hD.ne', hl.ne']
    nlinarith
  rw [hform x hx, hp, zero_mul, zero_add, hq0, hc0]
  rfl

/-- The profile is strictly decreasing in `x` for a positive source. -/
theorem profile_strictAnti {D k j : ℝ} (hD : 0 < D) (hk : 0 < k) (hj : 0 < j) :
    StrictAnti (profile D k j) := by
  intro x y hxy
  have hl := decayLength_pos hD hk
  unfold profile
  refine mul_lt_mul_of_pos_left ?_ (div_pos hj (sqrt_pos.2 (mul_pos hD hk)))
  rw [exp_lt_exp, neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_right hxy hl

/-- The profile equals `θ` at the boundary `x_θ`. -/
theorem profile_thresholdPosition {D k j θ : ℝ} (hD : 0 < D) (hk : 0 < k) (hj : 0 < j)
    (hθ : 0 < θ) : profile D k j (thresholdPosition D k j θ) = θ := by
  have hl := decayLength_pos hD hk
  have hA : 0 < j / √(D * k) := div_pos hj (sqrt_pos.2 (mul_pos hD hk))
  unfold profile thresholdPosition
  rw [neg_div, mul_div_cancel_left₀ _ hl.ne', exp_neg, exp_log (div_pos hA hθ)]
  field_simp

/-- **French-flag boundary.** For positive parameters and threshold `θ`, `c(x) = θ` exactly at
`x = x_θ = λ log(c(0)/θ)`. -/
theorem profile_eq_iff {D k j θ : ℝ} (hD : 0 < D) (hk : 0 < k) (hj : 0 < j) (hθ : 0 < θ)
    (x : ℝ) : profile D k j x = θ ↔ x = thresholdPosition D k j θ := by
  conv_lhs => rw [← profile_thresholdPosition hD hk hj hθ]
  exact (profile_strictAnti hD hk hj).injective.eq_iff

/-- **French-flag regions.** A cell at `x` is at or above threshold `θ` iff it lies within the
boundary `x_θ`: `θ ≤ c(x) ↔ x ≤ x_θ`. -/
theorem le_profile_iff {D k j θ : ℝ} (hD : 0 < D) (hk : 0 < k) (hj : 0 < j) (hθ : 0 < θ)
    (x : ℝ) : θ ≤ profile D k j x ↔ x ≤ thresholdPosition D k j θ := by
  conv_lhs => rw [← profile_thresholdPosition hD hk hj hθ]
  exact (profile_strictAnti hD hk hj).le_iff_ge

/-- **Boundary shift.** Scaling the source flux by `a > 0` moves every French-flag boundary by
`λ log a`. -/
theorem thresholdPosition_mul {D k j θ a : ℝ} (hj : 0 < j) (hD : 0 < D) (hk : 0 < k)
    (hθ : 0 < θ) (ha : 0 < a) :
    thresholdPosition D k (a * j) θ = thresholdPosition D k j θ + decayLength D k * log a := by
  have hA : 0 < j / √(D * k) / θ := div_pos (div_pos hj (sqrt_pos.2 (mul_pos hD hk))) hθ
  unfold thresholdPosition
  rw [show a * j / √(D * k) / θ = a * (j / √(D * k) / θ) by ring,
    log_mul ha.ne' hA.ne']
  ring

/-- Doubling the source flux shifts every French-flag boundary away from the source by exactly
`λ log 2`. -/
theorem thresholdPosition_two_mul {D k j θ : ℝ} (hj : 0 < j) (hD : 0 < D) (hk : 0 < k)
    (hθ : 0 < θ) :
    thresholdPosition D k (2 * j) θ = thresholdPosition D k j θ + decayLength D k * log 2 :=
  thresholdPosition_mul hj hD hk hθ two_pos

end MathlibExt.Biology.Dynamics.MorphogenGradient
