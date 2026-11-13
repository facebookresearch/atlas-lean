/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CableTimeDependent

/-! Tests for the time-dependent sealed-end cable: mode values, a mode self-inner-product
(squared norm) computed with Mathlib's `integral_cos_sq`, decay rates at sample parameters, a
hand-checked solution witnessing that `IsCableSolution`, `SealedEnds` and the hypotheses of
`modeCoeff_eq_mul_exp` are satisfiable, a summable coefficient sequence for the infinite
expansion, and boundary cases (`ℓ = 0`, `t = 0`, no nonuniform modes). -/

open Real Set Filter Topology intervalIntegral

namespace MathlibExtTest.Biology.Biophysics.CableTimeDependent

open MathlibExt.Biology.Biophysics.CableTimeDependent

/-! ### Modes -/

/-- `cosMode π 1 x = cos x`. -/
example (x : ℝ) : cosMode π 1 x = cos x := by
  simp [cosMode, pi_ne_zero]

/-- Every mode equals `1` at the left end. -/
example (L : ℝ) (n : ℕ) : cosMode L n 0 = 1 := by simp [cosMode]

/-- The first mode on `[0, 2]` vanishes at the midpoint: `cos (π / 2) = 0`. -/
example : cosMode 2 1 1 = 0 := by
  simp only [cosMode, Nat.cast_one, one_mul, mul_one]
  exact cos_pi_div_two

/-- Mode self-inner-product (squared `L²` norm) on `[0, π]` computed with Mathlib's
`integral_cos_sq`, independently of `integral_cosMode_mul_cosMode`: `∫₀^π cos² = π / 2`. -/
example : ∫ x in (0 : ℝ)..π, cosMode π 1 x * cosMode π 1 x = π / 2 := by
  have h : (fun x => cosMode π 1 x * cosMode π 1 x) = fun x => cos x ^ 2 := by
    funext x; simp [cosMode, pi_ne_zero, sq]
  rw [h, integral_cos_sq]
  simp

/-- The orthogonality theorem agrees with that value. -/
example : ∫ x in (0 : ℝ)..π, cosMode π 1 x * cosMode π 1 x = π / 2 := by
  rw [integral_cosMode_mul_cosMode pi_ne_zero]; simp

/-- Distinct modes are orthogonal. -/
example : ∫ x in (0 : ℝ)..π, cosMode π 1 x * cosMode π 2 x = 0 := by
  rw [integral_cosMode_mul_cosMode pi_ne_zero]; simp

/-! ### Decay rates -/

/-- `τ = 2`, `ℓ = 1`, `L = π`: `k₁ = (1 + 1) / 2 = 1`. -/
example : decayRate 2 1 π 1 = 1 := by
  simp [decayRate, pi_ne_zero]

/-- `τ = 1`, `ℓ = 1`, `L = π`: `k₂ = 5`, so `k₂ / k₀ = 5 = 1 + (2 π ℓ / L)²`. -/
example : decayRate 1 1 π 2 / decayRate 1 1 π 0 = 5 := by
  simp [decayRate, pi_ne_zero]; norm_num

/-- Uniform mode at sample parameters, from the definition: `k₀ = 1 / τ`. -/
example : decayRate 5 3 7 0 = 1 / 5 := by simp [decayRate]

/-- Electrotonic length at `τ = 1`, `ℓ = 1`, `L = π`, computed from the definition:
`π / √(k₁ / k₀ - 1) = π / √1 = π = L / ℓ`. -/
example : π / √(decayRate 1 1 π 1 / decayRate 1 1 π 0 - 1) = π / 1 := by
  simp [decayRate, pi_ne_zero]

/-- Boundary `ℓ = 0`: every mode has the membrane rate `1 / τ`, so `decayRate_strictMono`
genuinely needs `ℓ ≠ 0`. -/
example (τ L : ℝ) (n : ℕ) : decayRate τ 0 L n = 1 / τ := by simp [decayRate]

example (τ L : ℝ) : ¬ StrictMono (decayRate τ 0 L) := fun h => by
  have := h (show (0 : ℕ) < 1 from one_pos)
  simp [decayRate] at this

/-! ### A hand-checked solution: the uniform mode `V t x = e^{-t}` with `τ = 1` -/

/-- The uniform decaying profile. -/
noncomputable def uniformDecay (t _x : ℝ) : ℝ := exp (-t)

/-- Time derivative of the uniform profile, from `HasDerivAt.exp`. -/
theorem hasDerivAt_uniformDecay (t x : ℝ) :
    HasDerivAt (fun s => uniformDecay s x) (-exp (-t)) t := by
  simpa [uniformDecay] using (hasDerivAt_neg t).exp

/-- The uniform profile is constant in space. -/
theorem deriv_uniformDecay_space (t : ℝ) : deriv (uniformDecay t) = fun _ => 0 := by
  funext x; exact deriv_const x (exp (-t))

/-- Non-vacuity of `IsCableSolution`, checked by hand from the definitions:
`1 · (-e^{-t}) = ℓ² · 0 - e^{-t}`. -/
theorem isCableSolution_uniformDecay (ℓ L : ℝ) (T : Set ℝ) :
    IsCableSolution 1 ℓ L T uniformDecay where
  differentiableAt_time t _ x _ := (hasDerivAt_uniformDecay t x).differentiableAt
  differentiableAt_space t _ x _ := differentiableAt_const (exp (-t))
  differentiableAt_deriv_space t _ x _ := by rw [deriv_uniformDecay_space]; simp
  cable t _ x _ := by
    rw [(hasDerivAt_uniformDecay t x).deriv, deriv_uniformDecay_space]
    simp [uniformDecay]

/-- Non-vacuity of `SealedEnds`. -/
theorem sealedEnds_uniformDecay (L : ℝ) (T : Set ℝ) : SealedEnds L T uniformDecay := fun t _ => by
  simp [deriv_uniformDecay_space]

/-- The hand-checked solution is the finite expansion with `s = {0}`, `a₀ = 1`, `τ = 1`. -/
example (ℓ L t x : ℝ) : cableSum 1 ℓ L {0} (fun _ => 1) t x = uniformDecay t x := by
  simp [cableSum, decayRate, cosMode, uniformDecay]

/-- Non-vacuity of all hypotheses of `modeCoeff_eq_mul_exp`, instantiated on the hand-checked
solution with `T = (0, ∞)`, `L = 2`; the conclusion for `n = 0` is then compared with the
coefficient computed directly from `modeCoeff`: `c₀(t) = 2 e^{-t}`. -/
example (ℓ : ℝ) {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : 0 < t) :
    modeCoeff 2 uniformDecay 0 t = modeCoeff 2 uniformDecay 0 t₀ * exp (-(t - t₀)) := by
  have hVt : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => uniformDecay s p.2) p.1)
      (Ioi 0 ×ˢ Icc 0 2) := by
    have : (fun p : ℝ × ℝ => deriv (fun s => uniformDecay s p.2) p.1) =
        fun p => -exp (-p.1) := funext fun p => (hasDerivAt_uniformDecay p.1 p.2).deriv
    rw [this]; fun_prop
  have hVxx : ∀ t ∈ Ioi (0 : ℝ), ContinuousOn (deriv (deriv (uniformDecay t))) (Icc 0 2) := by
    intro t _; rw [deriv_uniformDecay_space]; simp; exact continuousOn_const
  have h := modeCoeff_eq_mul_exp (τ := 1) (ℓ := ℓ) one_ne_zero two_pos isOpen_Ioi
    isPreconnected_Ioi (isCableSolution_uniformDecay ℓ 2 _) (sealedEnds_uniformDecay 2 _) hVt hVxx
    0 ht₀ ht
  simpa [decayRate] using h

/-- The coefficient computed directly from the definition. -/
example (t : ℝ) : modeCoeff 2 uniformDecay 0 t = 2 * exp (-t) := by
  simp [modeCoeff, uniformDecay, cosMode]

/-! ### Finite expansion -/

/-- Boundary `t = 0`, `x = 0`: with nonnegative coefficients the bound of `abs_cableSum_le`
is attained, `V 0 0 = ∑ a n = ∑ |a n|`. -/
example (τ ℓ L : ℝ) : cableSum τ ℓ L {0, 1, 2} (fun n => (n : ℝ) + 1) 0 0 = 6 := by
  simp [cableSum, cosMode]; norm_num

/-- Boundary `s = ∅` for equalization: the uniform mode alone gives `e^{t/τ} V = a₀` exactly. -/
example {τ : ℝ} (ℓ L : ℝ) (a : ℕ → ℝ) (t x : ℝ) :
    exp (t / τ) * cableSum τ ℓ L {0} a t x = a 0 := by
  simp only [cableSum, Finset.sum_singleton, decayRate, cosMode]
  rw [show exp (t / τ) * (a 0 * (exp (-((1 + ℓ ^ 2 * ((0 : ℕ) * π / L) ^ 2) / τ) * t) *
      cos ((0 : ℕ) * π / L * x))) = a 0 * (exp (t / τ) * exp (-(1 / τ) * t)) by simp; ring,
    ← exp_add]
  simp [div_eq_inv_mul]

/-- The finite expansion with modes `0, 1` on `[0, π]` at `τ = 1`, `ℓ = 1`: the mode-`1`
coefficient at time `t` is `a₁ e^{-2 t} π / 2`. -/
example (a : ℕ → ℝ) (t : ℝ) :
    ∫ x in (0 : ℝ)..π, cableSum 1 1 π {0, 1} a t x * cosMode π 1 x =
      a 1 * exp (-2 * t) * (π / 2) := by
  rw [integral_cableSum_mul_cosMode pi_ne_zero]
  simp [decayRate, pi_ne_zero]
  left; norm_num

/-! ### Infinite expansion -/

/-- A summable coefficient sequence `a n = 2⁻ⁿ` (non-vacuity of `∑ |a n| < ∞`). -/
theorem summable_half_pow : Summable fun n : ℕ => |(1 / 2 : ℝ) ^ n| := by
  simpa [abs_of_nonneg] using summable_geometric_two

/-- Initial value at `x = 0` computed from the definition: `∑ 2⁻ⁿ = 2`. -/
example (τ ℓ L : ℝ) : cableSeries τ ℓ L (fun n => (1 / 2 : ℝ) ^ n) 0 0 = 2 := by
  simp only [cableSeries, cosMode, mul_zero, exp_zero, cos_zero, mul_one]
  exact tsum_geometric_two

/-- The geometric expansion solves the cable equation for `t > 0` with sealed ends. -/
example : IsCableSolution 1 1 π (Ioi 0) (cableSeries 1 1 π fun n => (1 / 2 : ℝ) ^ n) :=
  isCableSolution_cableSeries one_pos one_ne_zero π summable_half_pow

example : SealedEnds π (Ioi 0) (cableSeries 1 1 π fun n => (1 / 2 : ℝ) ^ n) :=
  sealedEnds_cableSeries one_pos one_ne_zero pi_ne_zero summable_half_pow

/-- Its uniform coefficient decays at the membrane rate: `c₀(t) = π e^{-t}`. -/
example {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in (0 : ℝ)..π, cableSeries 1 1 π (fun n => (1 / 2 : ℝ) ^ n) t x * cosMode π 0 x =
      π * exp (-t) := by
  rw [integral_cableSeries_mul_cosMode one_pos pi_ne_zero 1 summable_half_pow ht]
  simp [decayRate]; ring

/-! ### Steady state and charging -/

/-- The steady profile equals `1` at the sealed end, from the definition. -/
example (ℓ L : ℝ) : sealedSteady ℓ L L = 1 := by simp [sealedSteady]

/-- The steady profile at the injection end is `cosh (L / ℓ)`. -/
example (ℓ L : ℝ) : sealedSteady ℓ L 0 = cosh (L / ℓ) := by simp [sealedSteady]

/-- Non-vacuity: a charging transient with nonzero injection on `[0, 1]`. -/
example : IsCableSolution 1 1 1 univ (chargingSum 1 1 1 2 {1} fun _ => -1) :=
  isCableSolution_chargingSum one_ne_zero one_ne_zero 1 2 {1} _

example (t : ℝ) : deriv (chargingSum 1 1 1 2 {1} (fun _ => -1) t) 0 = -2 * sinh 1 := by
  rw [(deriv_chargingSum_ends one_ne_zero 1 1 2 {1} _ t).2]; simp

end MathlibExtTest.Biology.Biophysics.CableTimeDependent
