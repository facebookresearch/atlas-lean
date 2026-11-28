/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Chemistry.Transport.SerialTankResponse
public import MathlibExt.Probability.Distributions.GammaMoments
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Serial transit times at fixed total mean

Let `n = k + 1` be the number of stages and `τ > 0` their total mean transit time.
For a solution of `serialTank_bolusResponse` with initial amount `m > 0` in the first
stage only, the final output divided by `m`, extended by zero for negative times, is the
gamma density with shape `n` and rate `n / τ`. For `θ ≥ 0`, the CDF is the lower incomplete
gamma integral up to `(n / τ) * θ`, divided by `Γ(n)`.

Rawlings and Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd ed.,
7th printing, §8.2.5, pp. 440–441, give the density (8.16), integrated law (8.17–8.19) and
qualitative narrowing. The mean `τ` and variance `τ² / n` are deductions. So is the following
limit: for fixed `τ > 0` and `ε > 0`, the probability outside the open interval `(τ − ε, τ + ε)`
tends to zero as `n` grows. No joint law across stage counts is assumed. A time-unit change
rescales times, mean and tolerance by the same `c > 0`; multiplication by zero instead sends
the probability law to a point mass.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace Chemistry.Transport

/-- For `n = k + 1` stages, the real response formula with rate parameter `r = n / τ` is
`rⁿ tᵏ exp(−r t) / k!` for `t ≥ 0` and zero otherwise. It is defined for every real `τ`.
For `τ > 0` it is a probability density with the following interpretation: if `u` solves the
serial model on nonnegative times with initial amount `m > 0` in the first stage and zero in
all others, then this density is `r * u (Fin.last k) t / m` for `t ≥ 0` and zero for `t < 0`. -/
noncomputable def serialTransitDensity (k : ℕ) (τ t : ℝ) : ℝ :=
  let r := ((k : ℝ) + 1) / τ
  if 0 ≤ t then r ^ (k + 1) / (k.factorial : ℝ) * t ^ k * Real.exp (-(r * t)) else 0

/-- Let `n = k + 1`, `τ > 0` and `r = n / τ`. If `u` solves the serial model equations
on nonnegative times, starting with amount `m > 0` in the first stage and zero in the
others, then `serialTransitDensity k τ t` is `r * u (Fin.last k) t / m` for `t ≥ 0` and
zero for `t < 0`. No value of `u` is prescribed before time zero. -/
theorem serialTransitDensity_eq_output (k : ℕ) {τ m : ℝ} (hτ : 0 < τ) (hm : 0 < m)
    (u : Fin (k + 1) → ℝ → ℝ) :
    let r := ((k : ℝ) + 1) / τ
    u 0 0 = m → (∀ j : Fin k, u j.succ 0 = 0) →
    (∀ t, 0 ≤ t → HasDerivAt (u 0) (-r * u 0 t) t) →
    (∀ (j : Fin k) t, 0 ≤ t → HasDerivAt (u j.succ)
      (r * (u j.castSucc t - u j.succ t)) t) →
    ∀ t, serialTransitDensity k τ t = if 0 ≤ t then r * u (Fin.last k) t / m else 0 := by
  intro r h₀ hj hd₀ hdj t
  obtain ⟨_, huniq, hout, _⟩ := serialTank_bolusResponse k τ m hτ hm
  have hu := huniq u ⟨h₀, hj, by simpa only [Nat.cast_succ] using hd₀,
    by simpa only [Nat.cast_succ] using hdj⟩
  by_cases ht : 0 ≤ t
  · rw [ite_eq_left ht, hu (Fin.last k) t ht]
    simpa only [serialTransitDensity, Nat.cast_succ, ite_eq_left ht] using hout t
  · simp [serialTransitDensity, ht]

/-- For `n = k + 1` and every real `τ`, the response formula agrees pointwise with
`gammaPDFReal n (n / τ)`, including at zero. For `τ > 0` this identifies a probability
density with shape `n` and rate `n / τ`. -/
theorem serialTransitDensity_eq_gammaPDFReal (k : ℕ) (τ : ℝ) :
    serialTransitDensity k τ = gammaPDFReal (k + 1) (((k : ℝ) + 1) / τ) := by
  funext t
  simp only [serialTransitDensity, gammaPDFReal, Real.Gamma_nat_eq_factorial,
    add_sub_cancel_right, Real.rpow_natCast]
  rw [← Nat.cast_succ, Real.rpow_natCast]

/-- For `n = k + 1` stages, weight Lebesgue measure by the nonnegative part of the real
response formula. This defines a measure for every real `τ`. For `τ > 0` it is the
probability law of the time coordinate, i.e. the identity on this measure space. -/
noncomputable def serialTransitLaw (k : ℕ) (τ : ℝ) : Measure ℝ :=
  volume.withDensity (fun t ↦ ENNReal.ofReal (serialTransitDensity k τ t))

/-- For `n = k + 1` and every real `τ`, the measure defined by the response formula equals
`gammaMeasure n (n / τ)`. For `τ > 0` this is a gamma probability law with shape `n` and
rate `n / τ`, not scale `n / τ`. -/
theorem serialTransitLaw_eq_gamma (k : ℕ) (τ : ℝ) :
    serialTransitLaw k τ = gammaMeasure (k + 1) (((k : ℝ) + 1) / τ) := by
  rw [serialTransitLaw, serialTransitDensity_eq_gammaPDFReal]
  rfl

/-- For `n = k + 1` stages and total mean `τ > 0`, the serial transit-time measure has
total mass one. -/
theorem serialTransitLaw_isProbability (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IsProbabilityMeasure (serialTransitLaw k τ) := by
  rw [serialTransitLaw_eq_gamma]
  exact isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)

/-- For `n = k + 1` stages, total mean `τ > 0` and threshold `θ ≥ 0`, the probability of
a transit time at most `θ` is `γ(n, (n / τ) * θ) / Γ(n)`. The numerator is the integral of
`sᵏ exp(−s)` from zero to `(n / τ) * θ`. -/
theorem serialTransitLaw_cdf (k : ℕ) {τ θ : ℝ} (hτ : 0 < τ) (hθ : 0 ≤ θ) :
    cdf (serialTransitLaw k τ) θ =
      (∫ s in 0..(((k : ℝ) + 1) / τ * θ), s ^ k * Real.exp (-s)) / Real.Gamma (k + 1) := by
  let r := ((k : ℝ) + 1) / τ
  let f : ℝ → ℝ := fun s ↦ s ^ k * Real.exp (-s)
  have hr : 0 < r := div_pos (by positivity) hτ
  have hd : serialTransitDensity k τ =
      (Ici 0).indicator (fun t ↦ r * f (r * t) / Real.Gamma (k + 1)) := by
    funext t
    by_cases ht : 0 ≤ t
    · rw [indicator_of_mem ht]
      simp only [serialTransitDensity, ite_eq_left ht, Real.Gamma_nat_eq_factorial, f, mul_pow]
      dsimp only [r]
      rw [pow_succ]
      ring
    · simp [serialTransitDensity, ht]
  rw [serialTransitLaw_eq_gamma, cdf_gammaMeasure_eq_integral (by positivity) hr,
    ← serialTransitDensity_eq_gammaPDFReal, hd, setIntegral_indicator measurableSet_Ici,
    inter_comm, Ici_inter_Iic, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hθ,
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  have hs := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := θ) f r
  simpa only [smul_eq_mul, mul_zero] using congrArg (fun z : ℝ ↦ z / Real.Gamma (k + 1)) hs

/-- For `n = k + 1` stages and `τ > 0`, the identity time variable under the serial
transit-time law has mean `τ` and variance `τ² / n`. -/
theorem serialTransitLaw_moments (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ t, t ∂serialTransitLaw k τ) = τ ∧
      variance id (serialTransitLaw k τ) = τ ^ 2 / ((k : ℝ) + 1) := by
  have hs : 0 < (k : ℝ) + 1 := by positivity
  have hr := div_pos hs hτ
  rw [serialTransitLaw_eq_gamma, integral_id_gammaMeasure hs hr, variance_id_gammaMeasure hs hr]
  constructor <;> field_simp [hs.ne', hτ.ne']

private lemma outside_eq (τ ε : ℝ) :
    (Ioo (τ - ε) (τ + ε))ᶜ = {t | ε ≤ |t - τ|} := by
  ext t
  change (¬ (τ - ε < t ∧ t < τ + ε)) ↔ ε ≤ |t - τ|
  rw [← not_lt, abs_lt]
  apply not_congr
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- For `n = k + 1` stages, total mean `τ > 0` and tolerance `ε > 0`, the probability
outside the open interval `(τ − ε, τ + ε)` is at most `min(1, τ² / (n ε²))`. Both
endpoints count as outside. -/
theorem serialTransitLaw_outside_le (k : ℕ) {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    (serialTransitLaw k τ).real (Ioo (τ - ε) (τ + ε))ᶜ ≤
      min 1 (τ ^ 2 / (((k : ℝ) + 1) * ε ^ 2)) := by
  let := serialTransitLaw_isProbability k hτ
  refine le_min ?_ ?_
  · simp
  have hL : MemLp id 2 (serialTransitLaw k τ) := by
    rw [serialTransitLaw_eq_gamma]
    exact memLp_id_gammaMeasure (by positivity) (by positivity)
  have h := meas_ge_le_variance_div_sq hL hε
  obtain ⟨hmean, hvar⟩ := serialTransitLaw_moments k hτ
  simp only [id_eq] at h
  rw [hmean, hvar, div_div] at h
  rw [outside_eq, measureReal_def]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 h |>.trans_eq
    (ENNReal.toReal_ofReal (by positivity))

/-- Fix the total mean `τ > 0` and tolerance `ε > 0`. As the stage count `n = k + 1` tends
to infinity, both the bound `min(1, τ² / (n ε²))` and the probability outside the open
interval `(τ − ε, τ + ε)` tend to zero. -/
theorem serialTransitLaw_concentration {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    Tendsto (fun k : ℕ ↦ min 1 (τ ^ 2 / (((k : ℝ) + 1) * ε ^ 2))) atTop (𝓝 0) ∧
      Tendsto (fun k : ℕ ↦ (serialTransitLaw k τ).real (Ioo (τ - ε) (τ + ε))ᶜ)
        atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ ↦ τ ^ 2 / ε ^ 2) atTop (𝓝 (τ ^ 2 / ε ^ 2)) := tendsto_const_nhds
  have hraw : Tendsto (fun k : ℕ ↦ τ ^ 2 / (((k : ℝ) + 1) * ε ^ 2)) atTop (𝓝 0) := by
    have h := hc.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero, div_eq_mul_inv, mul_inv_rev, one_mul, mul_assoc] using h
  have h1 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hb := h1.min hraw
  rw [min_eq_right zero_le_one] at hb
  exact ⟨hb, squeeze_zero (fun _ ↦ measureReal_nonneg)
    (fun k ↦ serialTransitLaw_outside_le k hτ hε) hb⟩

/-- For `n = k + 1` stages, total mean `τ > 0` and unit factor `c > 0`, the map `t ↦ c * t`
pushes the serial transit-time law to the one with total mean `c * τ`. Its shape is still
`n` and its rate is `n / (c * τ)`. -/
theorem serialTransitLaw_map_mul (k : ℕ) {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) :
    (serialTransitLaw k τ).map (fun t ↦ c * t) = serialTransitLaw k (c * τ) := by
  rw [serialTransitLaw_eq_gamma, serialTransitLaw_eq_gamma,
    gammaMeasure_map_const_mul (by positivity) (by positivity) hc, div_div, mul_comm τ c]

/-- For `n = k + 1` stages, `τ > 0`, `ε > 0` and `c > 0`, the preimage under `t ↦ c * t`
of the event outside `(cτ − cε, cτ + cε)` is the event outside `(τ − ε, τ + ε)`. The
two events have equal probabilities under their respective laws, and the clipped bound
`min(1, τ² / (n ε²))` is unchanged by the same rescaling. -/
theorem serialTransitLaw_changeUnit (k : ℕ) {τ ε c : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hc : 0 < c) :
    let A := (Ioo (τ - ε) (τ + ε))ᶜ
    let B := (Ioo (c * τ - c * ε) (c * τ + c * ε))ᶜ
    (fun t : ℝ ↦ c * t) ⁻¹' B = A ∧
      (serialTransitLaw k (c * τ)).real B = (serialTransitLaw k τ).real A ∧
      min 1 ((c * τ) ^ 2 / (((k : ℝ) + 1) * (c * ε) ^ 2)) =
        min 1 (τ ^ 2 / (((k : ℝ) + 1) * ε ^ 2)) := by
  intro A B
  have he : (fun t : ℝ ↦ c * t) ⁻¹' B = A := by
    ext t
    change (¬ (c * τ - c * ε < c * t ∧ c * t < c * τ + c * ε)) ↔
      ¬ (τ - ε < t ∧ t < τ + ε)
    simp only [← mul_sub, ← mul_add, mul_lt_mul_iff_right₀ hc]
  refine ⟨he, ?_, ?_⟩
  · rw [← serialTransitLaw_map_mul k hτ hc,
      map_measureReal_apply (by fun_prop) measurableSet_Ioo.compl, he]
  · congr 1
    field_simp [hc.ne', hε.ne']

/-- For `n = k + 1` stages and total mean `τ > 0`, multiplication of the time variable by
zero pushes its probability law to the unit point mass at zero. This is not a change of unit. -/
theorem serialTransitLaw_map_zero (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (serialTransitLaw k τ).map (fun t ↦ 0 * t) = Measure.dirac 0 := by
  let := serialTransitLaw_isProbability k hτ
  simp [Measure.map_const]

end Chemistry.Transport
