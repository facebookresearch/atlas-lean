/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Sojourn times of the neutral Wright–Fisher diffusion

For the neutral Wright–Fisher diffusion (time in units of `2N` generations, backward generator
`L_0 u = x (1 - x) / 2 · u''`) started at frequency `p`, the expected time spent at frequencies
in `[a, b] ⊆ (0, 1)` before absorption at `0` or `1` is `∫ x in a..b, G(p, x)` with the neutral
Green's function (sojourn density)

  `G(p, x) = 2 (1 - p) / (1 - x)` for `0 < x ≤ p`,   `G(p, x) = 2 p / x` for `p ≤ x < 1`.

Analytically, `G` is the Green's function of the boundary-value problem `L_0 u = -g`,
`u(0) = u(1) = 0`: for continuous `g` the function `u(p) = ∫ x in 0..1, G(p, x) g(x)` (the
expected value of `∫₀^T g(X_t) dt`, `T` the absorption time) solves it. Taking `g = 1` gives the
Kimura–Ohta mean absorption time `meanAbsorptionTime p = -2 (p log p + (1 - p) log (1 - p))`.

The probabilistic reading (occupation measure of the diffusion) is not formalized: Mathlib has
no diffusion processes. The statements here are the analytic Green's-function facts.

## Main results

* `neutralGreen`: the neutral Green's function `G(p, x)`.
* `generator_integral_neutralGreen`: `u(p) = ∫ G(p, x) g(x) dx` solves `L_0 u = -g` on `(0, 1)`.
* `integral_neutralGreen_left`, `integral_neutralGreen_right`: `u(0) = u(1) = 0`.
* `integral_neutralGreen`: `∫ x in 0..1, G(p, x) = meanAbsorptionTime p` on `[0, 1]`.

## References

* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), Chapter 4.
* M. Kimura and T. Ohta, *The average number of generations until fixation of a mutant gene in
  a finite population*, Genetics 61 (1969) 763–771.
-/

@[expose] public section

open Real Set

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The neutral Wright–Fisher Green's function (sojourn density), time in units of `2N`
generations (Ewens 2004, Chapter 4): `G(p, x) = 2 (1 - p) / (1 - x)` for `x ≤ p` and
`G(p, x) = 2 p / x` for `p < x`. In the diffusion reading (not formalized here), for
`0 < x < 1`, `G(p, x) dx` is the expected time a neutral allele started at frequency `p` spends
at frequencies in `(x, x + dx)` before loss or fixation. -/
noncomputable def neutralGreen (p x : ℝ) : ℝ :=
  if x ≤ p then 2 * (1 - p) / (1 - x) else 2 * p / x

/-- Splitting the Green integral at `q ∈ (0, 1)`:
`∫₀¹ G(q, x) g(x) dx = 2 (1 - q) ∫₀^q g(x) / (1 - x) dx + 2 q ∫_q^1 g(x) / x dx`. -/
private theorem integral_neutralGreen_mul {g : ℝ → ℝ} (hg : Continuous g) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, neutralGreen q x * g x =
      2 * (1 - q) * (∫ x in (0 : ℝ)..q, g x / (1 - x)) + 2 * q * ∫ x in q..1, g x / x := by
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  have hL : EqOn (fun x => neutralGreen q x * g x) (fun x => 2 * (1 - q) * (g x / (1 - x)))
      (Icc 0 q) := by
    intro x hx
    simp only [neutralGreen, ite_eq_left hx.2]
    ring
  have hR : EqOn (fun x => neutralGreen q x * g x) (fun x => 2 * q * (g x / x)) (Icc q 1) := by
    intro x hx
    rcases hx.1.eq_or_lt with rfl | h
    · simp only [neutralGreen, le_refl, ↓reduceIte]
      field_simp
    · simp only [neutralGreen, ite_eq_right (not_le.mpr h)]
      ring
  have hcL : ContinuousOn (fun x => 2 * (1 - q) * (g x / (1 - x))) (Icc 0 q) :=
    continuousOn_const.mul (hg.continuousOn.div (continuousOn_const.sub continuousOn_id)
      fun x hx => (sub_pos.mpr (hx.2.trans_lt hq.2)).ne')
  have hcR : ContinuousOn (fun x => 2 * q * (g x / x)) (Icc q 1) :=
    continuousOn_const.mul (hg.continuousOn.div continuousOn_id
      fun x hx => (hq.1.trans_le hx.1).ne')
  have h1 : ∫ x in (0 : ℝ)..q, neutralGreen q x * g x =
      ∫ x in (0 : ℝ)..q, 2 * (1 - q) * (g x / (1 - x)) :=
    intervalIntegral.integral_congr (by rwa [uIcc_of_le hq.1.le])
  have h2 : ∫ x in q..1, neutralGreen q x * g x = ∫ x in q..1, 2 * q * (g x / x) :=
    intervalIntegral.integral_congr (by rwa [uIcc_of_le hq.2.le])
  rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hcL.congr hL).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hq.1.le)
      ((hcR.congr hR).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hq.2.le),
    h1, h2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- FTC for `t ↦ ∫₀^t g(x) / (1 - x) dx` at `q ∈ (0, 1)`. -/
private theorem hasDerivAt_integral_div_one_sub {g : ℝ → ℝ} (hg : Continuous g) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => ∫ x in (0 : ℝ)..t, g x / (1 - x)) (g q / (1 - q)) q := by
  have hc : ContinuousOn (fun x => g x / (1 - x)) (Iio 1) :=
    hg.continuousOn.div (continuousOn_const.sub continuousOn_id) fun x hx => (sub_pos.mpr hx).ne'
  exact intervalIntegral.integral_hasDerivAt_right
    (ContinuousOn.intervalIntegrable_of_Icc hq.1.le (hc.mono fun x hx => hx.2.trans_lt hq.2))
    (hc.stronglyMeasurableAtFilter isOpen_Iio q hq.2) (hc.continuousAt (Iio_mem_nhds hq.2))

/-- FTC for `t ↦ ∫_t^1 g(x) / x dx` at `q ∈ (0, 1)`. -/
private theorem hasDerivAt_integral_div {g : ℝ → ℝ} (hg : Continuous g) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => ∫ x in t..1, g x / x) (-(g q / q)) q := by
  have hc : ContinuousOn (fun x => g x / x) (Ioi 0) :=
    hg.continuousOn.div continuousOn_id fun x hx => (mem_Ioi.mp hx).ne'
  exact intervalIntegral.integral_hasDerivAt_left
    (ContinuousOn.intervalIntegrable_of_Icc hq.2.le (hc.mono fun x hx => hq.1.trans_le hx.1))
    (hc.stronglyMeasurableAtFilter isOpen_Ioi q hq.1) (hc.continuousAt (Ioi_mem_nhds hq.1))

/-- The first derivative of the split Green integral: the boundary terms cancel. -/
private theorem hasDerivAt_sojourn {g : ℝ → ℝ} (hg : Continuous g) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun t => 2 * (1 - t) * (∫ x in (0 : ℝ)..t, g x / (1 - x)) + 2 * t * ∫ x in t..1, g x / x)
      (-2 * (∫ x in (0 : ℝ)..q, g x / (1 - x)) + 2 * ∫ x in q..1, g x / x) q := by
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  have h1 : HasDerivAt (fun t : ℝ => 2 * (1 - t)) (-2) q := by
    simpa using ((hasDerivAt_id q).const_sub 1).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 q := by
    simpa using (hasDerivAt_id q).const_mul (2 : ℝ)
  convert (h1.mul (hasDerivAt_integral_div_one_sub hg hq)).add
    (h2.mul (hasDerivAt_integral_div hg hq)) using 1
  field_simp
  ring

/-- **Green's representation (Ewens 2004, Chapter 4).** For continuous `g` and `p ∈ (0, 1)`, the
function `u(q) = ∫ x in 0..1, G(q, x) g(x)` solves the neutral backward equation `L_0 u = -g`
at `p`. In the diffusion reading (not formalized here), `u(p)` is the expected value of
`∫₀^T g(X_t) dt` up to the absorption time `T`. -/
theorem generator_integral_neutralGreen {g : ℝ → ℝ} (hg : Continuous g) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    generator 0 (fun q => ∫ x in (0 : ℝ)..1, neutralGreen q x * g x) p = -g p := by
  have hderiv : deriv (fun q => ∫ x in (0 : ℝ)..1, neutralGreen q x * g x) =ᶠ[nhds p]
      fun t => -2 * (∫ x in (0 : ℝ)..t, g x / (1 - x)) + 2 * ∫ x in t..1, g x / x := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with t ht
    rw [Filter.EventuallyEq.deriv_eq (f := fun t => 2 * (1 - t) *
      (∫ x in (0 : ℝ)..t, g x / (1 - x)) + 2 * t * ∫ x in t..1, g x / x) ?_]
    · exact (hasDerivAt_sojourn hg ht).deriv
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact integral_neutralGreen_mul hg hs
  have h2 := ((hasDerivAt_integral_div_one_sub hg hp).const_mul (-2 : ℝ)).fun_add
    ((hasDerivAt_integral_div hg hp).const_mul (2 : ℝ))
  have hp0 : p ≠ 0 := hp.1.ne'
  have hp1 : 1 - p ≠ 0 := (sub_pos.mpr hp.2).ne'
  simp only [generator, zero_mul, add_zero]
  rw [hderiv.deriv_eq, h2.deriv]
  field_simp
  ring

/-- Boundary value at `0`: an allele that is absent spends no time in `(0, 1)`, so
`∫ x in 0..1, G(0, x) g(x) = 0`. -/
theorem integral_neutralGreen_left (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, neutralGreen 0 x * g x = 0 := by
  refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
    (MeasureTheory.ae_of_all _ fun x hx => ?_)).trans (by simp)
  rw [uIoc_of_le zero_le_one] at hx
  simp [neutralGreen, not_le.2 hx.1]

/-- Boundary value at `1`: a fixed allele spends no time in `(0, 1)`, so
`∫ x in 0..1, G(1, x) g(x) = 0`. -/
theorem integral_neutralGreen_right (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, neutralGreen 1 x * g x = 0 := by
  refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
    (MeasureTheory.ae_of_all _ fun x hx => ?_)).trans (by simp)
  rw [uIoc_of_le zero_le_one] at hx
  simp [neutralGreen, hx.2]

/-- `∫₀^p 1 / (1 - x) dx = -log (1 - p)` for `p < 1`. -/
private theorem integral_one_div_one_sub {p : ℝ} (hp : p < 1) :
    ∫ x in (0 : ℝ)..p, 1 / (1 - x) = -log (1 - p) := by
  have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => 1 / x) (a := 0) (b := p) 1
  simp only [sub_zero] at h
  rw [h, integral_one_div_of_pos (sub_pos.mpr hp) one_pos,
    log_div one_ne_zero (sub_pos.mpr hp).ne', log_one, zero_sub]

/-- **Mean absorption time as a sojourn integral.** For `p ∈ [0, 1]`, the total expected
sojourn time `∫ x in 0..1, G(p, x)` is the Kimura–Ohta mean absorption time
`-2 (p log p + (1 - p) log (1 - p))` (units of `2N` generations). -/
theorem integral_neutralGreen {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, neutralGreen p x = meanAbsorptionTime p := by
  rcases hp.1.eq_or_lt with rfl | hp0
  · rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
      (Filter.Eventually.of_forall fun x hx => ?_)]
    · simp [meanAbsorptionTime]
    · rw [uIoc_of_le zero_le_one] at hx
      simp [neutralGreen, not_le.mpr hx.1]
  rcases hp.2.eq_or_lt with rfl | hp1
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => ?_]
    · simp [meanAbsorptionTime]
    · rw [uIcc_of_le zero_le_one] at hx
      simp [neutralGreen, hx.2]
  have h := integral_neutralGreen_mul (g := fun _ => (1 : ℝ)) continuous_const ⟨hp0, hp1⟩
  simp only [mul_one] at h
  rw [h, integral_one_div_one_sub hp1, integral_one_div_of_pos hp0 one_pos,
    log_div one_ne_zero hp0.ne', log_one, meanAbsorptionTime]
  ring

end MathlibExt.Biology.PopulationGenetics.Diffusion
