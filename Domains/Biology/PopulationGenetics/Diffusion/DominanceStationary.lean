/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure
public import Domains.Biology.PopulationGenetics.Diffusion.DominanceFixation
public import Domains.Biology.PopulationGenetics.Diffusion.SpeedDensity

/-!
# Dominance stationary law via the interior-basepoint speed measure

This module states Wright's stationary density for the Wright-Fisher diffusion
with dominance and two-way mutation, expressed through the interior-basepoint
speed measure.

The diffusion has drift `b x = (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x`
and diffusion coefficient `a x = x * (1 - x)` on `(0, 1)`. Here `x` is the
frequency of the focal allele, `c = N * s` is the population-scaled selection
coefficient for fitnesses `1`, `1 + h * s`, `1 + s` (for zero, one, and two copies
of the focal allele), `h` is the dominance coefficient, and `θ₁` (resp. `θ₂`) is
the population-scaled mutation rate toward (resp. away from) the focal allele.

The stationary density is the Beta mutation weight times the exponential of the
quadratic dominance potential `Φ(x) = 4 * c * h * x + 2 * c * (1 - 2 * h) * x ^ 2`,
covering directional (`h = 0`, `h = 1`), genic (`h = 1 / 2`), and balancing regimes
with a single formula. The interior basepoint `c0 ∈ (0, 1)` is named `c0` because
`c` denotes the selection scale.

Only analytic weak stationarity is claimed: the generator integrates to zero
against the speed measure. No dominance-mutation process, no invariance of a
process law, and no internal equilibrium frequencies are constructed or claimed.

References: Kimura (1964), "Diffusion models in population genetics",
J. Appl. Probab. 1, 177-232; Wright (1931), "Evolution in Mendelian populations",
Genetics 16, 97-159; Ewens (2004), "Mathematical Population Genetics", Springer.
-/

open Set MeasureTheory Filter
open scoped Topology

@[expose] public section
namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Stationary density for mutation-dominance balance: the exponential of the
quadratic dominance potential times the Beta mutation weight
(`mutationSpeedDensity`). The parameters follow the module conventions: `c` is the
selection scale, `h` the dominance coefficient, and `θ₁`, `θ₂` the mutation rates.
At `h = 1 / 2` this agrees with the genic `selectionMutationSpeedDensity`. This is
a density function only; integrability and normalizability are not claimed here. -/
public noncomputable def dominanceStationaryDensity (c h θ₁ θ₂ x : ℝ) : ℝ :=
  Real.exp (4 * c * h * x + 2 * c * (1 - 2 * h) * x ^ 2) *
    mutationSpeedDensity θ₁ θ₂ x

/-- Genic consistency: at `h = 1 / 2` the dominance stationary density equals the
genic selection-mutation speed density with selection parameter `c`. This is a
definitional computation. -/
public theorem dominanceStationaryDensity_half (c θ₁ θ₂ x : ℝ) :
    dominanceStationaryDensity c (1 / 2) θ₁ θ₂ x =
      selectionMutationSpeedDensity c θ₁ θ₂ x := by
  unfold dominanceStationaryDensity selectionMutationSpeedDensity
  congr 1
  congr 1
  ring

/-- Closed form of the interior-basepoint scale density for the mutation-dominance
coefficient pair with basepoint `c0`: a basepoint constant times the exponential
of the negative dominance potential times `mutationScaleDensity`. It unfolds the
identity `∫ z in c0..y, 2 * b z / a z` equals the logarithmic mutation terms plus
the potential difference `Φ(y) - Φ(c0)`. -/
public theorem scaleDensityFrom_dominance (c h θ₁ θ₂ c0 y : ℝ)
    (hc0 : c0 ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    scaleDensityFrom (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
      (fun x => x * (1 - x)) c0 y =
      (c0 ^ θ₁ * (1 - c0) ^ θ₂ *
        Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2)) *
        (Real.exp (-(4 * c * h * y + 2 * c * (1 - 2 * h) * y ^ 2)) *
          mutationScaleDensity θ₁ θ₂ y) := by
  have hseg : Set.uIcc c0 y ⊆ Set.Ioo (0 : ℝ) 1 := by
    rcases le_total c0 y with hle | hle
    · rw [Set.uIcc_of_le hle]
      intro z hz
      exact ⟨lt_of_lt_of_le hc0.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
    · rw [Set.uIcc_of_ge hle]
      intro z hz
      exact ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hc0.2⟩
  have hEq : EqOn
      (fun z => 2 * ((θ₁ * (1 - z) - θ₂ * z) / 2 + dominanceDrift c h z)
        / (z * (1 - z)))
      (fun z => θ₁ / z - θ₂ / (1 - z) + 4 * c * (h + (1 - 2 * h) * z))
      (Set.uIcc c0 y) := by
    intro z hz
    have hmem := hseg hz
    have hz0 : z ≠ 0 := ne_of_gt hmem.1
    have hz1 : (1 - z) ≠ 0 := ne_of_gt (sub_pos.mpr hmem.2)
    simp only [dominanceDrift]
    field_simp
    ring
  have hIntEq :
      (∫ z in c0..y, 2 * ((θ₁ * (1 - z) - θ₂ * z) / 2 + dominanceDrift c h z)
        / (z * (1 - z)))
        = ∫ z in c0..y,
          (θ₁ / z - θ₂ / (1 - z) + 4 * c * (h + (1 - 2 * h) * z)) := by
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall (fun z hz => hEq (Set.uIoc_subset_uIcc hz))
  have h1 : IntervalIntegrable (fun z => θ₁ / z) volume c0 y := by
    apply ContinuousOn.intervalIntegrable
    have hdiv : ContinuousOn (fun z => θ₁ / z) (Set.uIcc c0 y) :=
      continuousOn_const.div continuousOn_id
        (fun z hz => ne_of_gt (hseg hz).1)
    exact hdiv
  have h2 : IntervalIntegrable (fun z => θ₂ / (1 - z)) volume c0 y := by
    apply ContinuousOn.intervalIntegrable
    have hdiv : ContinuousOn (fun z => θ₂ / (1 - z)) (Set.uIcc c0 y) :=
      continuousOn_const.div (continuousOn_const.sub continuousOn_id)
        (fun z hz => ne_of_gt (sub_pos.mpr (hseg hz).2))
    exact hdiv
  have h3 : IntervalIntegrable
      (fun z => 4 * c * (h + (1 - 2 * h) * z)) volume c0 y := by
    apply ContinuousOn.intervalIntegrable
    have hlin : ContinuousOn (fun z => h + (1 - 2 * h) * z)
        (Set.uIcc c0 y) :=
      continuousOn_const.add (continuousOn_id.const_mul (1 - 2 * h))
    have hmul : ContinuousOn (fun z => 4 * c * (h + (1 - 2 * h) * z))
        (Set.uIcc c0 y) :=
      hlin.const_mul (4 * c)
    exact hmul
  have e1 : (∫ z in c0..y, θ₁ / z)
      = θ₁ * Real.log y - θ₁ * Real.log c0 := by
    have hderiv : ∀ z ∈ Set.uIcc c0 y,
        HasDerivAt (fun z => θ₁ * Real.log z) (θ₁ / z) z := by
      intro z hz
      have hz0 : z ≠ 0 := ne_of_gt (hseg hz).1
      have h := (Real.hasDerivAt_log hz0).const_mul θ₁
      simpa only [div_eq_mul_inv] using h
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h1
    simpa using hFTC
  have e2 : (∫ z in c0..y, θ₂ / (1 - z))
      = (-(θ₂ * Real.log (1 - y))) - (-(θ₂ * Real.log (1 - c0))) := by
    have hderiv : ∀ z ∈ Set.uIcc c0 y,
        HasDerivAt (fun z => -(θ₂ * Real.log (1 - z))) (θ₂ / (1 - z)) z := by
      intro z hz
      have hz1 : (1 - z) ≠ 0 := ne_of_gt (sub_pos.mpr (hseg hz).2)
      have hsub : HasDerivAt (fun z : ℝ => 1 - z) (-1) z := by
        simpa using (hasDerivAt_id z).const_sub (1 : ℝ)
      have hlog := hsub.log hz1
      have hmul := hlog.const_mul θ₂
      have hneg := hmul.neg
      have hval : -(θ₂ * (-1 / (1 - z))) = θ₂ / (1 - z) := by
        field_simp
      rw [hval] at hneg
      exact hneg
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h2
    simpa using hFTC
  have e3 : (∫ z in c0..y, 4 * c * (h + (1 - 2 * h) * z))
      = (4 * c * h * y + 2 * c * (1 - 2 * h) * y ^ 2)
        - (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2) := by
    have hderiv : ∀ z ∈ Set.uIcc c0 y,
        HasDerivAt (fun z => 4 * c * h * z + 2 * c * (1 - 2 * h) * z ^ 2)
          (4 * c * (h + (1 - 2 * h) * z)) z := by
      intro z hz
      have h1d : HasDerivAt (fun z : ℝ => 4 * c * h * z) (4 * c * h) z := by
        simpa only [mul_one] using (hasDerivAt_id' z).const_mul (4 * c * h)
      have h2d : HasDerivAt (fun z : ℝ => 2 * c * (1 - 2 * h) * z ^ 2)
          (2 * c * (1 - 2 * h) * (2 * z)) z := by
        simpa using ((hasDerivAt_pow 2 z).const_mul (2 * c * (1 - 2 * h)))
      have hsum := h1d.add h2d
      have hder : 4 * c * h + 2 * c * (1 - 2 * h) * (2 * z)
          = 4 * c * (h + (1 - 2 * h) * z) := by ring
      rw [hder] at hsum
      exact hsum
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h3
    simpa using hFTC
  have r1 : Real.exp (θ₁ * Real.log y) = y ^ θ₁ := by
    rw [mul_comm θ₁ (Real.log y), ← Real.rpow_def_of_pos hy.1 θ₁]
  have r2 : Real.exp (θ₁ * Real.log c0) = c0 ^ θ₁ := by
    rw [mul_comm θ₁ (Real.log c0), ← Real.rpow_def_of_pos hc0.1 θ₁]
  have r3 : Real.exp (θ₂ * Real.log (1 - y)) = (1 - y) ^ θ₂ := by
    rw [mul_comm θ₂ (Real.log (1 - y)),
      ← Real.rpow_def_of_pos (sub_pos.mpr hy.2) θ₂]
  have r4 : Real.exp (θ₂ * Real.log (1 - c0)) = (1 - c0) ^ θ₂ := by
    rw [mul_comm θ₂ (Real.log (1 - c0)),
      ← Real.rpow_def_of_pos (sub_pos.mpr hc0.2) θ₂]
  simp only [scaleDensityFrom, mutationScaleDensity]
  rw [hIntEq, intervalIntegral.integral_add (h1.sub h2) h3,
    intervalIntegral.integral_sub h1 h2, e1, e2, e3,
    Real.rpow_neg hy.1.le θ₁, Real.rpow_neg (sub_nonneg.mpr hy.2.le) θ₂,
    ← r1, ← r3, ← Real.exp_neg, ← Real.exp_neg, ← r2, ← r4]
  repeat rw [← Real.exp_add]
  congr 1
  ring

/-- Closed form of the interior-basepoint speed density for the mutation-dominance
coefficient pair with basepoint `c0`: a basepoint constant times
`dominanceStationaryDensity`. The constant is the reciprocal of the basepoint
constant in `scaleDensityFrom_dominance`, with the factor `2` carried by
`mutationSpeedDensity`. -/
public theorem speedDensityFrom_dominance (c h θ₁ θ₂ c0 y : ℝ)
    (hc0 : c0 ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    speedDensityFrom (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
      (fun x => x * (1 - x)) c0 y =
      (c0 ^ (-θ₁) * (1 - c0) ^ (-θ₂) *
        Real.exp (-(4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))) *
        dominanceStationaryDensity c h θ₁ θ₂ y := by
  have hS := scaleDensityFrom_dominance c h θ₁ θ₂ c0 y hc0 hy
  have hy0 : y ≠ 0 := ne_of_gt hy.1
  have hy1 : (1 - y) ≠ 0 := ne_of_gt (sub_pos.mpr hy.2)
  have hpy : 0 < y ^ θ₁ := Real.rpow_pos_of_pos hy.1 θ₁
  have hpy1 : 0 < (1 - y) ^ θ₂ :=
    Real.rpow_pos_of_pos (sub_pos.mpr hy.2) θ₂
  have hpc : 0 < c0 ^ θ₁ := Real.rpow_pos_of_pos hc0.1 θ₁
  have hpc1 : 0 < (1 - c0) ^ θ₂ :=
    Real.rpow_pos_of_pos (sub_pos.mpr hc0.2) θ₂
  simp only [speedDensityFrom, dominanceStationaryDensity,
    mutationSpeedDensity]
  rw [hS]
  simp only [mutationScaleDensity]
  rw [Real.rpow_sub_one hy0 θ₁, Real.rpow_sub_one hy1 θ₂,
    Real.rpow_neg hy.1.le θ₁, Real.rpow_neg (sub_nonneg.mpr hy.2.le) θ₂,
    Real.rpow_neg hc0.1.le θ₁, Real.rpow_neg (sub_nonneg.mpr hc0.2.le) θ₂]
  simp only [Real.exp_neg]
  field_simp [hy0, hy1, hpy.ne', hpy1.ne', hpc.ne', hpc1.ne',
    (Real.exp_pos _).ne']

/-- Vanishing boundary flux at `0` for the mutation-dominance coefficient pair with
basepoint `c0`: under positive mutation rates the flux
`deriv f y / scaleDensityFrom …` tends to `0` as `y` tends to `0` from the right.
Near `0` the scale density grows like `y ^ (-θ₁)` with `θ₁ > 0`, so its reciprocal
sends the flux to zero for bounded `deriv f`. No extra hypotheses on `deriv f` are
stated: its continuity near the boundary follows from `ContDiffOn ℝ 2 f`. -/
public theorem tendsto_deriv_div_scaleDensityFrom_dominance_zero
    (c h θ₁ θ₂ c0 : ℝ) (f : ℝ → ℝ)
    (hc0 : c0 ∈ Ioo (0 : ℝ) 1) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    Tendsto (fun y => deriv f y /
      scaleDensityFrom (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0 y) (𝓝[>] 0) (𝓝 0) := by
  have hC0 : 0 < c0 ^ θ₁ * (1 - c0) ^ θ₂ *
      Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hc0.1 θ₁)
      (Real.rpow_pos_of_pos (sub_pos.mpr hc0.2) θ₂)) (Real.exp_pos _)
  have hIoo : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) 1 := by
    have h1 : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Set.Ioi 0 := self_mem_nhdsWithin
    have h2 : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Set.Iio 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_of_mem (Iio_mem_nhds zero_lt_one) (fun y hy => hy))
    filter_upwards [h1, h2] with y hy0 hy1
    exact ⟨hy0, hy1⟩
  have hcongr : (fun y => deriv f y / scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0 y)
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun y => deriv f y * ((c0 ^ θ₁ * (1 - c0) ^ θ₂ *
        Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))⁻¹ *
        (Real.exp (4 * c * h * y + 2 * c * (1 - 2 * h) * y ^ 2) *
          (y ^ θ₁ * (1 - y) ^ θ₂)))) := by
    filter_upwards [hIoo] with y hy
    have hS := scaleDensityFrom_dominance c h θ₁ θ₂ c0 y hc0 hy
    have hpy : y ^ θ₁ ≠ 0 := (Real.rpow_pos_of_pos hy.1 θ₁).ne'
    have hpy1 : (1 - y) ^ θ₂ ≠ 0 :=
      (Real.rpow_pos_of_pos (sub_pos.mpr hy.2) θ₂).ne'
    rw [hS]
    simp only [mutationScaleDensity]
    rw [Real.rpow_neg hy.1.le θ₁,
      Real.rpow_neg (sub_nonneg.mpr hy.2.le) θ₂, Real.exp_neg]
    field_simp [hC0.ne', hpy, hpy1, (Real.exp_pos _).ne']
  have hDW : ContinuousOn (derivWithin f (Icc (0 : ℝ) 1))
      (Icc (0 : ℝ) 1) :=
    hf.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by decide)
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc (0 : ℝ) 1] 0 := by
    have hIooEq : Set.Ioo (0 : ℝ) 1 = Set.Ioi 0 ∩ Set.Iio 1 := by
      ext y
      simp only [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]
    have hmem : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
    have heq : 𝓝[Set.Ioo (0 : ℝ) 1] (0 : ℝ) = 𝓝[>] (0 : ℝ) := by
      rw [hIooEq, Set.inter_comm]
      exact nhdsWithin_inter_of_mem hmem
    rw [← heq]
    exact nhdsWithin_mono 0 Set.Ioo_subset_Icc_self
  have hTderiv : Tendsto (deriv f) (𝓝[>] (0 : ℝ))
      (𝓝 (derivWithin f (Icc (0 : ℝ) 1) 0)) := by
    have hCWA : ContinuousWithinAt (derivWithin f (Icc (0 : ℝ) 1))
        (Icc (0 : ℝ) 1) 0 :=
      hDW.continuousWithinAt (left_mem_Icc.mpr zero_le_one)
    have hT0 : Tendsto (derivWithin f (Icc (0 : ℝ) 1))
        (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 (derivWithin f (Icc (0 : ℝ) 1) 0)) := hCWA
    have hT : Tendsto (derivWithin f (Icc (0 : ℝ) 1)) (𝓝[>] (0 : ℝ))
        (𝓝 (derivWithin f (Icc (0 : ℝ) 1) 0)) := hT0.mono_left hle
    have hagr : derivWithin f (Icc (0 : ℝ) 1) =ᶠ[𝓝[>] (0 : ℝ)] deriv f := by
      filter_upwards [hIoo] with y hy
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
    exact Filter.Tendsto.congr' hagr hT
  have hTrpow : Tendsto (fun y : ℝ => y ^ θ₁) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun y : ℝ => y ^ θ₁) (𝓝 0) (𝓝 ((0 : ℝ) ^ θ₁)) :=
      Real.continuousAt_rpow_const 0 θ₁ (Or.inr hθ₁.le)
    have h : Tendsto (fun y : ℝ => y ^ θ₁) (𝓝[>] (0 : ℝ))
        (𝓝 ((0 : ℝ) ^ θ₁)) :=
      h0.mono_left nhdsWithin_le_nhds
    simpa only [Real.zero_rpow hθ₁.ne'] using h
  have hTrpow1 : Tendsto (fun y : ℝ => (1 - y) ^ θ₂) (𝓝[>] (0 : ℝ))
      (𝓝 1) := by
    have hcont : ContinuousAt (fun y : ℝ => (1 - y) ^ θ₂) 0 :=
      (continuousAt_const.sub continuousAt_id).rpow_const
        (Or.inr hθ₂.le)
    have h0 : Tendsto (fun y : ℝ => (1 - y) ^ θ₂) (𝓝 0)
        (𝓝 (((1 : ℝ) - 0) ^ θ₂)) := hcont
    have h1 : ((1 : ℝ) - 0) ^ θ₂ = 1 := by
      rw [sub_zero, Real.one_rpow]
    rw [h1] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hTexp : Tendsto
      (fun y : ℝ => Real.exp (4 * c * h * y + 2 * c * (1 - 2 * h) * y ^ 2))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (4 * c * h * 0 + 2 * c * (1 - 2 * h) * 0 ^ 2))) := by
    have h1c : Continuous (fun y : ℝ => 4 * c * h * y) :=
      continuous_id.const_mul (4 * c * h)
    have h2c : Continuous (fun y : ℝ => 2 * c * (1 - 2 * h) * y ^ 2) :=
      (continuous_id.pow 2).const_mul (2 * c * (1 - 2 * h))
    have hpoly : Continuous
        (fun y : ℝ => 4 * c * h * y + 2 * c * (1 - 2 * h) * y ^ 2) :=
      h1c.add h2c
    exact ((Real.continuous_exp.comp hpoly).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hB : Tendsto (fun _ : ℝ => (c0 ^ θ₁ * (1 - c0) ^ θ₂ *
      Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))⁻¹)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((c0 ^ θ₁ * (1 - c0) ^ θ₂ *
        Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))⁻¹)) :=
    tendsto_const_nhds
  have hFinal : Tendsto (fun y => deriv f y * ((c0 ^ θ₁ * (1 - c0) ^ θ₂ *
      Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))⁻¹ *
      (Real.exp (4 * c * h * y + 2 * c * (1 - 2 * h) * y ^ 2) *
        (y ^ θ₁ * (1 - y) ^ θ₂)))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hmul := hTderiv.mul (hB.mul (hTexp.mul (hTrpow.mul hTrpow1)))
    simpa using hmul
  exact Filter.Tendsto.congr' hcongr.symm hFinal

private theorem tendsto_deriv_div_scaleDensityFrom_dominance_one_zero
    (c h θ₁ θ₂ c0 : ℝ) (f : ℝ → ℝ)
    (hc0 : c0 ∈ Ioo (0 : ℝ) 1) (_hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    Tendsto (fun y => deriv f y /
      scaleDensityFrom (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0 y) (𝓝[<] 1) (𝓝 0) := by
  have hC0 : 0 < c0 ^ θ₁ * (1 - c0) ^ θ₂ *
      Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hc0.1 θ₁)
      (Real.rpow_pos_of_pos (sub_pos.mpr hc0.2) θ₂)) (Real.exp_pos _)
  have hIoo : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ∈ Ioo (0 : ℝ) 1 := by
    have h1 : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ∈ Set.Iio 1 := self_mem_nhdsWithin
    have h2 : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ∈ Set.Ioi 0 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_of_mem (Ioi_mem_nhds zero_lt_one) (fun y hy => hy))
    filter_upwards [h2, h1] with y hy0 hy1
    exact ⟨hy0, hy1⟩
  have hcongr : (fun y => deriv f y / scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0 y)
      =ᶠ[𝓝[<] (1 : ℝ)]
      (fun y => deriv f y * ((c0 ^ θ₁ * (1 - c0) ^ θ₂ *
        Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))⁻¹ *
        (Real.exp (4 * c * h * y + 2 * c * (1 - 2 * h) * y ^ 2) *
          (y ^ θ₁ * (1 - y) ^ θ₂)))) := by
    filter_upwards [hIoo] with y hy
    have hS := scaleDensityFrom_dominance c h θ₁ θ₂ c0 y hc0 hy
    have hpy : y ^ θ₁ ≠ 0 := (Real.rpow_pos_of_pos hy.1 θ₁).ne'
    have hpy1 : (1 - y) ^ θ₂ ≠ 0 :=
      (Real.rpow_pos_of_pos (sub_pos.mpr hy.2) θ₂).ne'
    rw [hS]
    simp only [mutationScaleDensity]
    rw [Real.rpow_neg hy.1.le θ₁,
      Real.rpow_neg (sub_nonneg.mpr hy.2.le) θ₂, Real.exp_neg]
    field_simp [hC0.ne', hpy, hpy1, (Real.exp_pos _).ne']
  have hDW : ContinuousOn (derivWithin f (Icc (0 : ℝ) 1))
      (Icc (0 : ℝ) 1) :=
    hf.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by decide)
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝[Icc (0 : ℝ) 1] 1 := by
    have hIooEq : Set.Ioo (0 : ℝ) 1 = Set.Iio 1 ∩ Set.Ioi 0 := by
      rw [Set.inter_comm]
      ext y
      simp only [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]
    have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)
    have heq : 𝓝[Set.Ioo (0 : ℝ) 1] (1 : ℝ) = 𝓝[<] (1 : ℝ) := by
      rw [hIooEq, Set.inter_comm]
      exact nhdsWithin_inter_of_mem hmem
    rw [← heq]
    exact nhdsWithin_mono 1 Set.Ioo_subset_Icc_self
  have hTderiv : Tendsto (deriv f) (𝓝[<] (1 : ℝ))
      (𝓝 (derivWithin f (Icc (0 : ℝ) 1) 1)) := by
    have hCWA : ContinuousWithinAt (derivWithin f (Icc (0 : ℝ) 1))
        (Icc (0 : ℝ) 1) 1 :=
      hDW.continuousWithinAt (right_mem_Icc.mpr zero_le_one)
    have hT1 : Tendsto (derivWithin f (Icc (0 : ℝ) 1))
        (𝓝[Icc (0 : ℝ) 1] 1) (𝓝 (derivWithin f (Icc (0 : ℝ) 1) 1)) := hCWA
    have hT : Tendsto (derivWithin f (Icc (0 : ℝ) 1)) (𝓝[<] (1 : ℝ))
        (𝓝 (derivWithin f (Icc (0 : ℝ) 1) 1)) := hT1.mono_left hle
    have hagr : derivWithin f (Icc (0 : ℝ) 1) =ᶠ[𝓝[<] (1 : ℝ)] deriv f := by
      filter_upwards [hIoo] with y hy
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
    exact Filter.Tendsto.congr' hagr hT
  have hTrpow : Tendsto (fun y : ℝ => y ^ θ₁) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hcont : ContinuousAt (fun y : ℝ => y ^ θ₁) 1 :=
      continuousAt_id.rpow_const (Or.inl one_ne_zero)
    have h1 : Tendsto (fun y : ℝ => y ^ θ₁) (𝓝 1) (𝓝 ((1 : ℝ) ^ θ₁)) :=
      hcont
    have hv : ((1 : ℝ) ^ θ₁) = 1 := Real.one_rpow θ₁
    rw [hv] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hTrpow1 : Tendsto (fun y : ℝ => (1 - y) ^ θ₂) (𝓝[<] (1 : ℝ))
      (𝓝 0) := by
    have hcont : ContinuousAt (fun y : ℝ => (1 - y) ^ θ₂) 1 :=
      (continuousAt_const.sub continuousAt_id).rpow_const
        (Or.inr hθ₂.le)
    have h1 : Tendsto (fun y : ℝ => (1 - y) ^ θ₂) (𝓝 1)
        (𝓝 (((1 : ℝ) - 1) ^ θ₂)) := hcont
    have hv : ((1 : ℝ) - 1) ^ θ₂ = 0 := by
      rw [sub_self, Real.zero_rpow hθ₂.ne']
    rw [hv] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hTexp : Tendsto
      (fun y : ℝ => Real.exp (4 * c * h * y + 2 * c * (1 - 2 * h) * y ^ 2))
      (𝓝[<] (1 : ℝ))
      (𝓝 (Real.exp (4 * c * h * 1 + 2 * c * (1 - 2 * h) * 1 ^ 2))) := by
    have h1c : Continuous (fun y : ℝ => 4 * c * h * y) :=
      continuous_id.const_mul (4 * c * h)
    have h2c : Continuous (fun y : ℝ => 2 * c * (1 - 2 * h) * y ^ 2) :=
      (continuous_id.pow 2).const_mul (2 * c * (1 - 2 * h))
    have hpoly : Continuous
        (fun y : ℝ => 4 * c * h * y + 2 * c * (1 - 2 * h) * y ^ 2) :=
      h1c.add h2c
    exact ((Real.continuous_exp.comp hpoly).tendsto 1).mono_left
      nhdsWithin_le_nhds
  have hB : Tendsto (fun _ : ℝ => (c0 ^ θ₁ * (1 - c0) ^ θ₂ *
      Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))⁻¹)
      (𝓝[<] (1 : ℝ))
      (𝓝 ((c0 ^ θ₁ * (1 - c0) ^ θ₂ *
        Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))⁻¹)) :=
    tendsto_const_nhds
  have hFinal : Tendsto (fun y => deriv f y * ((c0 ^ θ₁ * (1 - c0) ^ θ₂ *
      Real.exp (4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))⁻¹ *
      (Real.exp (4 * c * h * y + 2 * c * (1 - 2 * h) * y ^ 2) *
        (y ^ θ₁ * (1 - y) ^ θ₂)))) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hmul := hTderiv.mul (hB.mul (hTexp.mul (hTrpow.mul hTrpow1)))
    simpa using hmul
  exact Filter.Tendsto.congr' hcongr.symm hFinal

/-- Vanishing boundary flux at `1` for the mutation-dominance coefficient pair with
basepoint `c0`: under positive mutation rates the flux
`deriv f y / scaleDensityFrom …` tends to `0` as `y` tends to `1` from the left.
Near `1` the scale density grows like `(1 - y) ^ (-θ₂)` with `θ₂ > 0`, so its
reciprocal sends the flux to zero for bounded `deriv f`. No extra hypotheses on
`deriv f` are stated: its continuity near the boundary follows from
`ContDiffOn ℝ 2 f`. -/
public theorem tendsto_deriv_div_scaleDensityFrom_dominance_one
    (c h θ₁ θ₂ c0 : ℝ) (f : ℝ → ℝ)
    (hc0 : c0 ∈ Ioo (0 : ℝ) 1) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    Tendsto (fun y => deriv f y /
      scaleDensityFrom (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0 y) (𝓝[<] 1) (𝓝 0) := by
  exact tendsto_deriv_div_scaleDensityFrom_dominance_one_zero c h θ₁ θ₂ c0 f
    hc0 hθ₁ hθ₂ hf

/-- Weak stationarity for the mutation-dominance coefficient pair with basepoint
`c0`: the diffusion generator integrates to zero against the interior-basepoint
speed measure for `C²` test functions under positive mutation rates. Integrability
of the generator is an explicit hypothesis, not established here. This is analytic
stationarity of the measure only; no process with this invariant law is claimed. -/
public theorem integral_diffusionGenerator_dominance_speedMeasureFrom
    (c h θ₁ θ₂ c0 : ℝ) (f : ℝ → ℝ)
    (hc0 : c0 ∈ Ioo (0 : ℝ) 1) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hint : Integrable
      (diffusionGenerator
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) f)
      (speedMeasureFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0)) :
    ∫ x, diffusionGenerator
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
      (fun x => x * (1 - x)) f x
      ∂(speedMeasureFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0) = 0 := by
  have ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < x * (1 - x) := by
    intro x hx
    exact mul_pos hx.1 (sub_pos.mpr hx.2)
  have ha_cont : ContinuousOn (fun x : ℝ => x * (1 - x)) (Ioo (0 : ℝ) 1) :=
    continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  have hmut : Continuous (fun x : ℝ => (θ₁ * (1 - x) - θ₂ * x) / 2) := by
    have e1 : Continuous (fun x : ℝ => θ₁ * (1 - x)) :=
      continuous_const.mul (continuous_const.sub continuous_id)
    have e2 : Continuous (fun x : ℝ => θ₂ * x) :=
      continuous_const.mul continuous_id
    exact (e1.sub e2).div_const 2
  have hdom : ContinuousOn (fun x : ℝ => dominanceDrift c h x)
      (Ioo (0 : ℝ) 1) := by
    simp only [dominanceDrift]
    have d1 : ContinuousOn (fun x : ℝ => 2 * c * x) (Ioo (0 : ℝ) 1) :=
      continuousOn_id.const_mul (2 * c)
    have d2 : ContinuousOn (fun x : ℝ => 2 * c * x * (1 - x))
        (Ioo (0 : ℝ) 1) :=
      d1.mul (continuousOn_const.sub continuousOn_id)
    have d3 : ContinuousOn (fun x : ℝ => h + (1 - 2 * h) * x)
        (Ioo (0 : ℝ) 1) :=
      continuousOn_const.add (continuousOn_const.mul continuousOn_id)
    exact d2.mul d3
  have hb_cont : ContinuousOn
      (fun x : ℝ => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
      (Ioo (0 : ℝ) 1) :=
    hmut.continuousOn.add hdom
  have hdiv_cont : ContinuousOn
      (fun x => ((θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        / (x * (1 - x)))
      (Ioo (0 : ℝ) 1) :=
    hb_cont.div ha_cont (fun x hx =>
      mul_ne_zero (ne_of_gt hx.1) (ne_of_gt (sub_pos.mpr hx.2)))
  have h0 := tendsto_deriv_div_scaleDensityFrom_dominance_zero
    c h θ₁ θ₂ c0 f hc0 hθ₁ hθ₂ hf
  have h1 := tendsto_deriv_div_scaleDensityFrom_dominance_one_zero
    c h θ₁ θ₂ c0 f hc0 hθ₁ hθ₂ hf
  exact integral_diffusionGenerator_speedMeasureFrom_eq_zero
    (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
    (fun x => x * (1 - x)) f c0 ha_pos ha_cont hdiv_cont hc0 hf h0 h1
    hint

private theorem intervalIntegrable_dominance_aux (c h θ₁ θ₂ : ℝ)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    IntervalIntegrable (fun x => dominanceStationaryDensity c h θ₁ θ₂ x)
      volume 0 1 := by
  have hleft : IntervalIntegrable
      (fun x : ℝ => 2 * x ^ (θ₁ - 1) * (1 - x) ^ (θ₂ - 1))
      volume 0 (1 / 2) := by
    have hrpow : IntervalIntegrable (fun x : ℝ => x ^ (θ₁ - 1))
        volume 0 (1 / 2) :=
      intervalIntegral.intervalIntegrable_rpow'
        (show (-1 : ℝ) < θ₁ - 1 by linarith)
    have h2 : IntervalIntegrable (fun x : ℝ => 2 * x ^ (θ₁ - 1))
        volume 0 (1 / 2) :=
      hrpow.const_mul 2
    have hcont : ContinuousOn (fun x : ℝ => (1 - x) ^ (θ₂ - 1))
        (Set.uIcc 0 (1 / 2)) := by
      refine ContinuousOn.rpow_const
        (continuousOn_const.sub continuousOn_id) ?_
      intro x hx
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 / 2 by norm_num)] at hx
      obtain ⟨hx0, hx1⟩ := hx
      have hne : (1 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
      exact Or.inl hne
    exact h2.mul_continuousOn hcont
  have hright : IntervalIntegrable
      (fun x : ℝ => 2 * x ^ (θ₁ - 1) * (1 - x) ^ (θ₂ - 1))
      volume (1 / 2) 1 := by
    have hbase : IntervalIntegrable (fun x : ℝ => x ^ (θ₂ - 1))
        volume 0 (1 / 2) :=
      intervalIntegral.intervalIntegrable_rpow'
        (show (-1 : ℝ) < θ₂ - 1 by linarith)
    have hrefl : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (θ₂ - 1))
        volume (1 / 2) 1 := by
      have h := (hbase.comp_sub_left (1 : ℝ)).symm
      simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
        show (1 : ℝ) - 0 = 1 by norm_num] using h
    have hcont : ContinuousOn (fun x : ℝ => 2 * x ^ (θ₁ - 1))
        (Set.uIcc (1 / 2) 1) := by
      have hpow : ContinuousOn (fun x : ℝ => x ^ (θ₁ - 1))
          (Set.uIcc (1 / 2) 1) := by
        refine ContinuousOn.rpow_const continuousOn_id ?_
        intro x hx
        rw [Set.uIcc_of_le (show (1 / 2 : ℝ) ≤ 1 by norm_num)] at hx
        obtain ⟨hx0, hx1⟩ := hx
        have hne : (x : ℝ) ≠ 0 := ne_of_gt (by linarith)
        exact Or.inl hne
      exact hpow.const_mul 2
    exact hrefl.continuousOn_mul hcont
  have hmut0 := hleft.trans hright
  have hm : IntervalIntegrable (fun x => mutationSpeedDensity θ₁ θ₂ x)
      volume 0 1 := by
    simpa only [mutationSpeedDensity, mul_assoc, mul_comm,
      mul_left_comm] using hmut0
  have hexp : ContinuousOn
      (fun x : ℝ => Real.exp (4 * c * h * x + 2 * c * (1 - 2 * h) * x ^ 2))
      (Set.uIcc 0 1) := by
    have e1 : ContinuousOn (fun x : ℝ => 4 * c * h * x) (Set.uIcc 0 1) :=
      continuousOn_id.const_mul (4 * c * h)
    have e2 : ContinuousOn (fun x : ℝ => 2 * c * (1 - 2 * h) * x ^ 2)
        (Set.uIcc 0 1) :=
      (continuousOn_id.pow 2).const_mul (2 * c * (1 - 2 * h))
    exact (e1.add e2).rexp
  have hD := hm.continuousOn_mul hexp
  simpa only [dominanceStationaryDensity, mul_assoc, mul_comm,
    mul_left_comm] using hD

/-- Total mass of the interior-basepoint speed measure for the mutation-dominance
coefficient pair with basepoint `c0`: the basepoint constant times the integral of
`dominanceStationaryDensity` over `(0, 1)`, as an extended nonnegative real.
For positive mutation parameters the density is interval integrable
over `(0, 1)`, so the integral and the displayed total mass are finite. -/
public theorem speedMeasureFrom_dominance_univ (c h θ₁ θ₂ c0 : ℝ)
    (hc0 : c0 ∈ Ioo (0 : ℝ) 1) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    speedMeasureFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0 Set.univ =
      ENNReal.ofReal ((c0 ^ (-θ₁) * (1 - c0) ^ (-θ₂) *
        Real.exp (-(4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))) *
        ∫ x in (0 : ℝ)..1, dominanceStationaryDensity c h θ₁ θ₂ x) := by
  have hC1 : 0 < (c0 ^ (-θ₁) * (1 - c0) ^ (-θ₂) *
      Real.exp (-(4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hc0.1 _)
      (Real.rpow_pos_of_pos (sub_pos.mpr hc0.2) _)) (Real.exp_pos _)
  have hDint : IntervalIntegrable
      (fun x => dominanceStationaryDensity c h θ₁ θ₂ x) volume 0 1 :=
    intervalIntegrable_dominance_aux c h θ₁ θ₂ hθ₁ hθ₂
  have hCD : IntervalIntegrable (fun x => (c0 ^ (-θ₁) * (1 - c0) ^ (-θ₂) *
      Real.exp (-(4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))) *
      dominanceStationaryDensity c h θ₁ θ₂ x) volume 0 1 :=
    hDint.const_mul _
  have hInt : Integrable (fun x => (c0 ^ (-θ₁) * (1 - c0) ^ (-θ₂) *
      Real.exp (-(4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))) *
      dominanceStationaryDensity c h θ₁ θ₂ x)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hCD
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] (fun x =>
      (c0 ^ (-θ₁) * (1 - c0) ^ (-θ₂) *
        Real.exp (-(4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))) *
      dominanceStationaryDensity c h θ₁ θ₂ x) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
    have hD0 : 0 ≤ dominanceStationaryDensity c h θ₁ θ₂ a := by
      simp only [dominanceStationaryDensity, mutationSpeedDensity]
      have e1 : (0 : ℝ) ≤
          Real.exp (4 * c * h * a + 2 * c * (1 - 2 * h) * a ^ 2) :=
        (Real.exp_pos _).le
      have e2 : (0 : ℝ) ≤ 2 * a ^ (θ₁ - 1) * (1 - a) ^ (θ₂ - 1) :=
        mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg ha.1.le _))
          (Real.rpow_nonneg (sub_nonneg.mpr ha.2.le) _)
      exact mul_nonneg e1 e2
    exact mul_nonneg hC1.le hD0
  have hconv := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn
  have hρ : (fun x => ENNReal.ofReal (speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0 x))
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun x => ENNReal.ofReal ((c0 ^ (-θ₁) * (1 - c0) ^ (-θ₂) *
        Real.exp (-(4 * c * h * c0 + 2 * c * (1 - 2 * h) * c0 ^ 2))) *
        dominanceStationaryDensity c h θ₁ θ₂ x)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with a ha
    have hS := speedDensityFrom_dominance c h θ₁ θ₂ c0 a hc0 ha
    rw [hS]
  simp only [speedMeasureFrom]
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, MeasureTheory.lintegral_congr_ae hρ,
    ← hconv, MeasureTheory.integral_const_mul]
  congr 1
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]

end MathlibExt.Biology.PopulationGenetics.Diffusion
