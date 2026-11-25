/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.SelectionMutationStationary
public import Domains.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure
public import Domains.Biology.PopulationGenetics.Diffusion.SpeedDensity
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order

/-!
# Selection-mutation speed measure from an interior basepoint

For the Wright-Fisher selection-mutation diffusion on `(0, 1)` with drift
`b x = (θ₁ * (1 - x) - θ₂ * x) / 2 + α * x * (1 - x)` and variance
`a x = x * (1 - x)`, the interior-basepoint scale and speed densities
(`scaleDensityFrom`, `speedDensityFrom`) agree on `(0, 1)` with the explicit
selection-mutation densities (`selectionMutationScaleDensity`,
`selectionMutationSpeedDensity`) up to the basepoint constant
`K(α, θ₁, θ₂, c) = c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)`
and its reciprocal. The interior-basepoint speed measure
(`speedMeasureFrom`) is hence the same constant multiple of the explicit
density, with total mass `K(α, θ₁, θ₂, c)` times the landed partition
function `selectionMutationPartition`. For positive mutation parameters
both boundary fluxes of `f' / ψ` vanish, so the generator integrates to
zero against the speed measure (analytic weak stationarity). The
pure-mutation case (`α = 0`) against `betaMeasure` is the landed
`integral_mutationGenerator_betaMeasure`, which this file does not restate.

## Main results

* `scaleDensityFrom_selectionMutation`: the interior-basepoint scale density
  is the explicit selection-mutation scale density times the reciprocal
  basepoint constant.
* `speedDensityFrom_selectionMutation`: the interior-basepoint speed density
  is the explicit selection-mutation speed density times `K(α, θ₁, θ₂, c)`.
* `tendsto_deriv_div_scaleDensityFrom_selectionMutation_zero` and
  `tendsto_deriv_div_scaleDensityFrom_selectionMutation_one`: both boundary
  fluxes vanish for positive mutation parameters.
* `integral_diffusionGenerator_selectionMutation_speedMeasureFrom`: the
  generator integrates to zero against the interior-basepoint speed measure.
* `speedMeasureFrom_selectionMutation_univ`: the total mass is
  `K(α, θ₁, θ₂, c)` times the partition function.

## Conventions

`α`, `θ₁`, `θ₂` are real parameters and `c ∈ Ioo (0 : ℝ) 1` is the interior
basepoint. The coefficient pair is written out in every statement as the
explicit lambda terms, so each statement elaborates standalone. Real powers
follow the Mathlib junk convention; outside the positivity hypotheses
`0 < θ₁`, `0 < θ₂` the stated values are junk.

These are analytic identities about densities and integrals only. No claim
is made about construction of a selection-mutation process, about
invariance of any process law, or about convergence to equilibrium.

## References

* S. Wright, Evolution in Mendelian populations. Genetics 16:97-159, 1931
  (stationary distribution of gene frequencies under mutation and selection).
* W. J. Ewens, *Mathematical Population Genetics I*, Springer, 2004,
  Chapter 4 (diffusion theory; stationary distributions).
-/

@[expose] public section

open Real Set Filter MeasureTheory
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Interior-basepoint scale density for the selection-mutation diffusion:
on `(0, 1)` it agrees with the explicit `selectionMutationScaleDensity` up
to the reciprocal basepoint constant
`c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)`. The identity is the
integrated drift-to-variance relation exponentiated; it holds for arbitrary
real parameters with `c, y ∈ Ioo (0 : ℝ) 1`. This identifies densities
only; no process-level claim is made. -/
theorem scaleDensityFrom_selectionMutation (α θ₁ θ₂ c y : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    scaleDensityFrom (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y =
      (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
        selectionMutationScaleDensity α θ₁ θ₂ y := by
  obtain ⟨hc0, hc1⟩ := hc
  obtain ⟨hy0, hy1⟩ := hy
  set b : ℝ → ℝ := fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))
    with hb_def
  set a : ℝ → ℝ := fun x => x * (1 - x) with ha_def
  set F : ℝ → ℝ :=
    fun z => θ₁ * Real.log z + θ₂ * Real.log (1 - z) + 2 * α * z with hF_def
  have hseg : ∀ z ∈ uIcc c y, z ∈ Ioo (0 : ℝ) 1 := by
    intro z hz
    rw [mem_uIcc] at hz
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hc0 h1, lt_of_le_of_lt h2 hy1⟩
    · exact ⟨lt_of_lt_of_le hy0 h1, lt_of_le_of_lt h2 hc1⟩
  have hderiv : ∀ z ∈ uIcc c y, HasDerivAt F (2 * b z / a z) z := by
    intro z hz
    have hzm := hseg z hz
    have hz0 : z ≠ 0 := ne_of_gt hzm.1
    have h1z : (1 : ℝ) - z ≠ 0 := ne_of_gt (sub_pos.mpr hzm.2)
    have hlog1 : HasDerivAt (fun z => Real.log z) (1 / z) z :=
      (hasDerivAt_id' z).log hz0
    have hsub : HasDerivAt (fun z => (1 : ℝ) - z) (0 - 1) z :=
      (hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id' z)
    have hlog2 : HasDerivAt (fun z => Real.log (1 - z)) ((0 - 1) / (1 - z)) z :=
      hsub.log h1z
    have h1 : HasDerivAt (fun z => θ₁ * Real.log z) (θ₁ * (1 / z)) z :=
      hlog1.const_mul θ₁
    have h2 : HasDerivAt (fun z => θ₂ * Real.log (1 - z))
        (θ₂ * ((0 - 1) / (1 - z))) z :=
      hlog2.const_mul θ₂
    have h3 : HasDerivAt (fun z => 2 * α * z) (2 * α * 1) z :=
      (hasDerivAt_id' z).const_mul (2 * α)
    have h := (h1.add h2).add h3
    have hD : (θ₁ * (1 / z) + θ₂ * ((0 - 1) / (1 - z))) + 2 * α * 1
        = 2 * b z / a z := by
      simp only [hb_def, ha_def]
      field_simp
      ring
    rw [hF_def, ← hD]
    exact h
  have hint : IntervalIntegrable (fun z => 2 * b z / a z) volume c y := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · have hb : ContinuousOn b (uIcc c y) := by
        rw [hb_def]
        fun_prop
      exact continuousOn_const.mul hb
    · rw [ha_def]
      fun_prop
    · intro z hz
      have hzm := hseg z hz
      simp only [ha_def]
      exact mul_ne_zero (ne_of_gt hzm.1) (ne_of_gt (sub_pos.mpr hzm.2))
  simp only [scaleDensityFrom]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [selectionMutationScaleDensity, mutationScaleDensity, hF_def]
  rw [Real.rpow_def_of_pos hc0 θ₁, Real.rpow_def_of_pos (sub_pos.mpr hc1) θ₂,
    Real.rpow_def_of_pos hy0 (-θ₁), Real.rpow_def_of_pos (sub_pos.mpr hy1) (-θ₂)]
  simp only [← Real.exp_add]
  congr 1
  ring

/-- Interior-basepoint speed density for the selection-mutation diffusion:
on `(0, 1)` it agrees with the explicit `selectionMutationSpeedDensity` up
to the basepoint constant
`c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)`. The identity follows
from the scale-density identification above since the speed density is
`2 / (a * ψ)`; it holds for arbitrary real parameters with
`c, y ∈ Ioo (0 : ℝ) 1`. This identifies densities only; no process-level
claim is made. -/
theorem speedDensityFrom_selectionMutation (α θ₁ θ₂ c y : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    speedDensityFrom (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y =
      (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
        selectionMutationSpeedDensity α θ₁ θ₂ y := by
  obtain ⟨hc0, hc1⟩ := hc
  obtain ⟨hy0, hy1⟩ := hy
  have hsm :=
    scaleDensityFrom_selectionMutation α θ₁ θ₂ c y ⟨hc0, hc1⟩ ⟨hy0, hy1⟩
  have h1c : (0 : ℝ) < 1 - c := sub_pos.mpr hc1
  have h1y : (0 : ℝ) < 1 - y := sub_pos.mpr hy1
  have e1 : y ^ (θ₁ - 1) = y ^ θ₁ / y ^ (1 : ℝ) := Real.rpow_sub hy0 θ₁ 1
  have e2 : (1 - y) ^ (θ₂ - 1) = (1 - y) ^ θ₂ / (1 - y) ^ (1 : ℝ) :=
    Real.rpow_sub h1y θ₂ 1
  have n1 : y ^ (-θ₁) = (y ^ θ₁)⁻¹ := Real.rpow_neg (le_of_lt hy0) θ₁
  have n2 : (1 - y) ^ (-θ₂) = ((1 - y) ^ θ₂)⁻¹ := Real.rpow_neg (le_of_lt h1y) θ₂
  have n3 : c ^ (-θ₁) = (c ^ θ₁)⁻¹ := Real.rpow_neg (le_of_lt hc0) θ₁
  have n4 : (1 - c) ^ (-θ₂) = ((1 - c) ^ θ₂)⁻¹ :=
    Real.rpow_neg (le_of_lt h1c) θ₂
  have exy : Real.exp (-2 * α * y) = (Real.exp (2 * α * y))⁻¹ := by
    rw [(show (-2 : ℝ) * α * y = -(2 * α * y) by ring)]
    exact Real.exp_neg _
  have exc : Real.exp (-2 * α * c) = (Real.exp (2 * α * c))⁻¹ := by
    rw [(show (-2 : ℝ) * α * c = -(2 * α * c) by ring)]
    exact Real.exp_neg _
  have hy0' : y ≠ 0 := ne_of_gt hy0
  have h1y' : (1 : ℝ) - y ≠ 0 := ne_of_gt h1y
  have hyt : y ^ θ₁ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hy0 θ₁)
  have h1yt : (1 - y) ^ θ₂ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h1y θ₂)
  have hct : c ^ θ₁ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hc0 θ₁)
  have h1ct : (1 - c) ^ θ₂ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h1c θ₂)
  have hey : Real.exp (2 * α * y) ≠ 0 := Real.exp_ne_zero _
  have hec : Real.exp (2 * α * c) ≠ 0 := Real.exp_ne_zero _
  simp only [speedDensityFrom]
  rw [hsm]
  simp only [selectionMutationScaleDensity, mutationScaleDensity,
    selectionMutationSpeedDensity, mutationSpeedDensity]
  rw [n1, n2, n3, n4, e1, e2, exy, exc]
  simp only [Real.rpow_one]
  field_simp

/-- Left boundary flux vanishes: for positive mutation parameters and `f`
twice continuously differentiable on `[0, 1]`, the flux
`deriv f y / scaleDensityFrom b a c y` tends to `0` as `y → 0` from the
right, through values in `(0, 1)`. The scale density blows up like
`y ^ (-θ₁)` at `0` while `deriv f` stays bounded near the endpoint, so no
separate differentiability hypothesis on `deriv f` is needed beyond
`ContDiffOn ℝ 2 f (Icc 0 1)`. This is a boundary input to the zero-flux
identity, not a stationarity claim by itself. -/
theorem tendsto_deriv_div_scaleDensityFrom_selectionMutation_zero
    (α θ₁ θ₂ c : ℝ) (f : ℝ → ℝ)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    Tendsto (fun y => deriv f y / scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hc0, hc1⟩ := hc
  set b : ℝ → ℝ := fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))
    with hb_def
  set a : ℝ → ℝ := fun x => x * (1 - x) with ha_def
  have h1c : (0 : ℝ) < 1 - c := sub_pos.mpr hc1
  have hC : c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c) ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (Real.rpow_pos_of_pos hc0 θ₁)
      (Real.rpow_pos_of_pos h1c θ₂)) (Real.exp_pos _))
  have hflux : ∀ y ∈ Ioo (0 : ℝ) 1,
      deriv f y / scaleDensityFrom b a c y =
        (deriv f y * ((c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
          (Real.exp (2 * α * y) * (1 - y) ^ θ₂))) * y ^ θ₁ := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have h1y : (0 : ℝ) < 1 - y := sub_pos.mpr hy1
    have hsm :=
      scaleDensityFrom_selectionMutation α θ₁ θ₂ c y ⟨hc0, hc1⟩ ⟨hy0, hy1⟩
    simp only [hb_def, ha_def]
    rw [hsm]
    simp only [selectionMutationScaleDensity, mutationScaleDensity]
    rw [Real.rpow_neg (le_of_lt hy0) θ₁, Real.rpow_neg (le_of_lt h1y) θ₂,
      (show Real.exp (-2 * α * y) = (Real.exp (2 * α * y))⁻¹ by
        rw [(show (-2 : ℝ) * α * y = -(2 * α * y) by ring)]
        exact Real.exp_neg _)]
    have hyt : y ^ θ₁ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hy0 θ₁)
    have h1yt : (1 - y) ^ θ₂ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h1y θ₂)
    have hey : Real.exp (2 * α * y) ≠ 0 := Real.exp_ne_zero _
    field_simp
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc (0 : ℝ) 1] 0 := by
    have h := nhdsWithin_restrict' (Set.Ioi (0 : ℝ)) (Iio_mem_nhds zero_lt_one)
    rw [Set.Ioi_inter_Iio] at h
    rw [h]
    exact nhdsWithin_mono 0 Set.Ioo_subset_Icc_self
  have hcont : ContinuousOn (derivWithin f (Icc 0 1)) (Icc 0 1) :=
    hf.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) (by decide)
  have hder : Tendsto (derivWithin f (Icc 0 1)) (𝓝[>] (0 : ℝ))
      (𝓝 (derivWithin f (Icc 0 1) 0)) :=
    ((hcont.continuousWithinAt (by norm_num : (0 : ℝ) ∈ Icc 0 1)).tendsto).mono_left
      hle
  have hexp : Tendsto (fun y : ℝ => Real.exp (2 * α * y)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (2 * α * 0))) := by
    have hlin : Tendsto (fun y : ℝ => 2 * α * y) (𝓝[>] (0 : ℝ))
        (𝓝 (2 * α * 0)) := by
      have h0 : ContinuousAt (fun y : ℝ => 2 * α * y) 0 := by fun_prop
      exact tendsto_nhdsWithin_of_tendsto_nhds h0.tendsto
    have hexp0 : Tendsto Real.exp (𝓝 (2 * α * 0))
        (𝓝 (Real.exp (2 * α * 0))) :=
      Real.continuous_exp.tendsto _
    exact hexp0.comp hlin
  have hrpow : Tendsto (fun y : ℝ => (1 - y) ^ θ₂) (𝓝[>] (0 : ℝ))
      (𝓝 (((1 : ℝ) - 0) ^ θ₂)) := by
    have hbase : Tendsto (fun y : ℝ => (1 : ℝ) - y) (𝓝[>] (0 : ℝ))
        (𝓝 ((1 : ℝ) - 0)) := by
      have h0 : ContinuousAt (fun y : ℝ => (1 : ℝ) - y) 0 := by fun_prop
      exact tendsto_nhdsWithin_of_tendsto_nhds h0.tendsto
    have hrpow0 : Tendsto (fun x : ℝ => x ^ θ₂) (𝓝 ((1 : ℝ) - 0))
        (𝓝 (((1 : ℝ) - 0) ^ θ₂)) :=
      (Real.continuousAt_rpow_const _ _ (Or.inl (by norm_num))).tendsto
    exact hrpow0.comp hbase
  have hcof : Tendsto
      (fun y : ℝ => (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
        (Real.exp (2 * α * y) * (1 - y) ^ θ₂))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
        (Real.exp (2 * α * 0) * ((1 : ℝ) - 0) ^ θ₂))) :=
    Tendsto.mul tendsto_const_nhds (hexp.mul hrpow)
  have hH : Tendsto
      (fun y : ℝ => derivWithin f (Icc 0 1) y *
        ((c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
          (Real.exp (2 * α * y) * (1 - y) ^ θ₂)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (derivWithin f (Icc 0 1) 0 *
        ((c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
          (Real.exp (2 * α * 0) * ((1 : ℝ) - 0) ^ θ₂)))) :=
    hder.mul hcof
  have hR : Tendsto (fun y : ℝ => y ^ θ₁) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := Real.continuousAt_rpow_const 0 θ₁ (Or.inr (le_of_lt hθ₁))
    have h0 : (0 : ℝ) ^ θ₁ = 0 := Real.zero_rpow (ne_of_gt hθ₁)
    have hT : Tendsto (fun y : ℝ => y ^ θ₁) (𝓝 0) (𝓝 0) := by
      have ht := h.tendsto
      simpa only [h0] using ht
    exact tendsto_nhdsWithin_of_tendsto_nhds hT
  have hfinal : Tendsto
      (fun y : ℝ => (derivWithin f (Icc 0 1) y *
        ((c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
          (Real.exp (2 * α * y) * (1 - y) ^ θ₂))) * y ^ θ₁)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hHR := hH.mul hR
    simpa using hHR
  apply Tendsto.congr' _ hfinal
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) 1 := by
    have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
      have h1 : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
      have h2 : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
      have h := inter_mem h1 h2
      rwa [Set.Ioi_inter_Iio] at h
    exact eventually_of_mem hmem (fun y hy => hy)
  filter_upwards [hev] with y hy
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
  exact (hflux y hy).symm

/-- Right boundary flux vanishes: for positive mutation parameters and `f`
twice continuously differentiable on `[0, 1]`, the flux
`deriv f y / scaleDensityFrom b a c y` tends to `0` as `y → 1` from the
left, through values in `(0, 1)`. The scale density blows up like
`(1 - y) ^ (-θ₂)` at `1` while `deriv f` stays bounded near the endpoint,
so no separate differentiability hypothesis on `deriv f` is needed beyond
`ContDiffOn ℝ 2 f (Icc 0 1)`. This is a boundary input to the zero-flux
identity, not a stationarity claim by itself. -/
theorem tendsto_deriv_div_scaleDensityFrom_selectionMutation_one
    (α θ₁ θ₂ c : ℝ) (f : ℝ → ℝ)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) :
    Tendsto (fun y => deriv f y / scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨hc0, hc1⟩ := hc
  set b : ℝ → ℝ := fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))
    with hb_def
  set a : ℝ → ℝ := fun x => x * (1 - x) with ha_def
  have h1c : (0 : ℝ) < 1 - c := sub_pos.mpr hc1
  have hC : c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c) ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (Real.rpow_pos_of_pos hc0 θ₁)
      (Real.rpow_pos_of_pos h1c θ₂)) (Real.exp_pos _))
  have hflux : ∀ y ∈ Ioo (0 : ℝ) 1,
      deriv f y / scaleDensityFrom b a c y =
        (deriv f y * ((c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
          (Real.exp (2 * α * y) * y ^ θ₁))) * (1 - y) ^ θ₂ := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have h1y : (0 : ℝ) < 1 - y := sub_pos.mpr hy1
    have hsm :=
      scaleDensityFrom_selectionMutation α θ₁ θ₂ c y ⟨hc0, hc1⟩ ⟨hy0, hy1⟩
    simp only [hb_def, ha_def]
    rw [hsm]
    simp only [selectionMutationScaleDensity, mutationScaleDensity]
    rw [Real.rpow_neg (le_of_lt hy0) θ₁, Real.rpow_neg (le_of_lt h1y) θ₂,
      (show Real.exp (-2 * α * y) = (Real.exp (2 * α * y))⁻¹ by
        rw [(show (-2 : ℝ) * α * y = -(2 * α * y) by ring)]
        exact Real.exp_neg _)]
    have hyt : y ^ θ₁ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hy0 θ₁)
    have h1yt : (1 - y) ^ θ₂ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h1y θ₂)
    have hey : Real.exp (2 * α * y) ≠ 0 := Real.exp_ne_zero _
    field_simp
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝[Icc (0 : ℝ) 1] 1 := by
    have h := nhdsWithin_restrict' (Set.Iio (1 : ℝ)) (Ioi_mem_nhds zero_lt_one)
    rw [Set.Iio_inter_Ioi] at h
    rw [h]
    exact nhdsWithin_mono 1 Set.Ioo_subset_Icc_self
  have hcont : ContinuousOn (derivWithin f (Icc 0 1)) (Icc 0 1) :=
    hf.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) (by decide)
  have hder : Tendsto (derivWithin f (Icc 0 1)) (𝓝[<] (1 : ℝ))
      (𝓝 (derivWithin f (Icc 0 1) 1)) :=
    ((hcont.continuousWithinAt (by norm_num : (1 : ℝ) ∈ Icc 0 1)).tendsto).mono_left
      hle
  have hexp : Tendsto (fun y : ℝ => Real.exp (2 * α * y)) (𝓝[<] (1 : ℝ))
      (𝓝 (Real.exp (2 * α * 1))) := by
    have hlin : Tendsto (fun y : ℝ => 2 * α * y) (𝓝[<] (1 : ℝ))
        (𝓝 (2 * α * 1)) := by
      have h0 : ContinuousAt (fun y : ℝ => 2 * α * y) 1 := by fun_prop
      exact tendsto_nhdsWithin_of_tendsto_nhds h0.tendsto
    have hexp0 : Tendsto Real.exp (𝓝 (2 * α * 1))
        (𝓝 (Real.exp (2 * α * 1))) :=
      Real.continuous_exp.tendsto _
    exact hexp0.comp hlin
  have hrpow : Tendsto (fun y : ℝ => y ^ θ₁) (𝓝[<] (1 : ℝ))
      (𝓝 ((1 : ℝ) ^ θ₁)) := by
    have hbase : Tendsto (fun y : ℝ => y) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
      have h0 : ContinuousAt (fun y : ℝ => y) 1 := by fun_prop
      exact tendsto_nhdsWithin_of_tendsto_nhds h0.tendsto
    have hrpow0 : Tendsto (fun x : ℝ => x ^ θ₁) (𝓝 1) (𝓝 ((1 : ℝ) ^ θ₁)) :=
      (Real.continuousAt_rpow_const _ _ (Or.inl (by norm_num))).tendsto
    exact hrpow0.comp hbase
  have hcof : Tendsto
      (fun y : ℝ => (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
        (Real.exp (2 * α * y) * y ^ θ₁))
      (𝓝[<] (1 : ℝ))
      (𝓝 ((c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
        (Real.exp (2 * α * 1) * (1 : ℝ) ^ θ₁))) :=
    Tendsto.mul tendsto_const_nhds (hexp.mul hrpow)
  have hH : Tendsto
      (fun y : ℝ => derivWithin f (Icc 0 1) y *
        ((c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
          (Real.exp (2 * α * y) * y ^ θ₁)))
      (𝓝[<] (1 : ℝ))
      (𝓝 (derivWithin f (Icc 0 1) 1 *
        ((c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
          (Real.exp (2 * α * 1) * (1 : ℝ) ^ θ₁)))) :=
    hder.mul hcof
  have hR : Tendsto (fun y : ℝ => (1 - y) ^ θ₂) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hR0 : Tendsto (fun x : ℝ => x ^ θ₂) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := Real.continuousAt_rpow_const 0 θ₂ (Or.inr (le_of_lt hθ₂))
      have h0 : (0 : ℝ) ^ θ₂ = 0 := Real.zero_rpow (ne_of_gt hθ₂)
      have hT : Tendsto (fun x : ℝ => x ^ θ₂) (𝓝 0) (𝓝 0) := by
        have ht := h.tendsto
        simpa only [h0] using ht
      exact tendsto_nhdsWithin_of_tendsto_nhds hT
    have h1m : Tendsto (fun y : ℝ => (1 : ℝ) - y) (𝓝[<] (1 : ℝ))
        (𝓝[>] (0 : ℝ)) := by
      have h1 : Tendsto (fun y : ℝ => (1 : ℝ) - y) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
        have h0 : ContinuousAt (fun y : ℝ => (1 : ℝ) - y) 1 := by fun_prop
        have ht : Tendsto (fun y : ℝ => (1 : ℝ) - y) (𝓝[<] (1 : ℝ))
            (𝓝 ((fun y : ℝ => (1 : ℝ) - y) 1)) :=
          tendsto_nhdsWithin_of_tendsto_nhds h0.tendsto
        simpa using ht
      have h2 : ∀ᶠ y in 𝓝[<] (1 : ℝ),
          (fun y : ℝ => (1 : ℝ) - y) y ∈ Set.Ioi (0 : ℝ) := by
        have hm : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ∈ Set.Iio (1 : ℝ) :=
          eventually_of_mem self_mem_nhdsWithin (fun y hy => hy)
        filter_upwards [hm] with y hy
        exact sub_pos.mpr hy
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 h2
    exact hR0.comp h1m
  have hfinal : Tendsto
      (fun y : ℝ => (derivWithin f (Icc 0 1) y *
        ((c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c))⁻¹ *
          (Real.exp (2 * α * y) * y ^ θ₁))) * (1 - y) ^ θ₂)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hHR := hH.mul hR
    simpa using hHR
  apply Tendsto.congr' _ hfinal
  have hev : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ∈ Ioo (0 : ℝ) 1 := by
    have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
      have h1 : Set.Iio (1 : ℝ) ∈ 𝓝[<] (1 : ℝ) := self_mem_nhdsWithin
      have h2 : Set.Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)
      have h := inter_mem h1 h2
      rwa [Set.Iio_inter_Ioi] at h
    exact eventually_of_mem hmem (fun y hy => hy)
  filter_upwards [hev] with y hy
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
  exact (hflux y hy).symm

/-- Zero-flux weak stationarity for the selection-mutation diffusion: for
positive mutation parameters, the generator integrates to zero against the
interior-basepoint speed measure. This specializes the general
`integral_diffusionGenerator_speedMeasureFrom_eq_zero` via the vanishing
boundary fluxes above. The integrability hypothesis is kept to mirror the
general theorem; discharging it would need dominating-integrability bounds
near the endpoints, which are not claimed here. Analytic stationarity
only: no process law, invariance, or convergence claim. -/
theorem integral_diffusionGenerator_selectionMutation_speedMeasureFrom
    (α θ₁ θ₂ c : ℝ) (f : ℝ → ℝ)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hint : Integrable (diffusionGenerator
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) f)
      (speedMeasureFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c)) :
    ∫ x, diffusionGenerator
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) f x ∂(speedMeasureFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c) = 0 := by
  have ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < x * (1 - x) := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    exact mul_pos hx0 (sub_pos.mpr hx1)
  have ha_cont : ContinuousOn (fun x : ℝ => x * (1 - x)) (Ioo (0 : ℝ) 1) := by
    fun_prop
  have hdiv_cont : ContinuousOn
      (fun x =>
        ((θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))) / (x * (1 - x)))
      (Ioo (0 : ℝ) 1) := by
    have hnice : ContinuousOn
        (fun x : ℝ => (θ₁ * (1 - x) - θ₂ * x) / (2 * (x * (1 - x))) + α)
        (Ioo (0 : ℝ) 1) := by
      apply ContinuousOn.add
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro x hx
          obtain ⟨hx0, hx1⟩ := hx
          have h1x : (0 : ℝ) < 1 - x := sub_pos.mpr hx1
          exact ne_of_gt
            (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hx0 h1x))
      · exact continuousOn_const
    apply hnice.congr
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have h1x : (0 : ℝ) < 1 - x := sub_pos.mpr hx1
    have hx0' : x ≠ 0 := ne_of_gt hx0
    have h1x' : (1 : ℝ) - x ≠ 0 := ne_of_gt h1x
    field_simp
  have h0 :=
    tendsto_deriv_div_scaleDensityFrom_selectionMutation_zero α θ₁ θ₂ c f hθ₁
      hθ₂ hc hf
  have h1 :=
    tendsto_deriv_div_scaleDensityFrom_selectionMutation_one α θ₁ θ₂ c f hθ₁
      hθ₂ hc hf
  exact integral_diffusionGenerator_speedMeasureFrom_eq_zero _ _ _ _ ha_pos
    ha_cont hdiv_cont hc hf h0 h1 hint

/-- Total mass of the interior-basepoint selection-mutation speed measure:
the measure of `univ` is the basepoint constant
`c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)` times the landed
partition function `selectionMutationPartition`. Positivity of both factors
under `0 < θ₁`, `0 < θ₂` makes the `ENNReal.ofReal` a genuine finite value.
This is a total-mass formula only; no probability normalization or
process-level claim is made. -/
theorem speedMeasureFrom_selectionMutation_univ (α θ₁ θ₂ c : ℝ)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hc : c ∈ Ioo (0 : ℝ) 1) :
    speedMeasureFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c Set.univ =
      ENNReal.ofReal ((c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
        selectionMutationPartition α θ₁ θ₂) := by
  obtain ⟨hc0, hc1⟩ := hc
  set b : ℝ → ℝ := fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))
    with hb_def
  set a : ℝ → ℝ := fun x => x * (1 - x) with ha_def
  have h1c : (0 : ℝ) < 1 - c := sub_pos.mpr hc1
  have hK : (0 : ℝ) ≤ c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c) :=
    le_of_lt (mul_pos (mul_pos (Real.rpow_pos_of_pos hc0 _)
      (Real.rpow_pos_of_pos h1c _)) (Real.exp_pos _))
  have hII := intervalIntegrable_selectionMutationSpeedDensity α hθ₁ hθ₂
  have hdef := hII.def'
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hdef
  have hmeas : volume.restrict (Set.Ioc (0 : ℝ) 1)
      = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hInt : Integrable (fun x => selectionMutationSpeedDensity α θ₁ θ₂ x)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have hdef2 : Integrable (fun x => selectionMutationSpeedDensity α θ₁ θ₂ x)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := hdef
    rwa [hmeas] at hdef2
  have haemeas : AEMeasurable
      (fun x => ENNReal.ofReal (selectionMutationSpeedDensity α θ₁ θ₂ x))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hInt.aemeasurable
  have hae : (fun x => ENNReal.ofReal (speedDensityFrom b a c x)) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)]
      (fun x => ENNReal.ofReal ((c ^ (-θ₁) * (1 - c) ^ (-θ₂) *
        Real.exp (-2 * α * c)) * selectionMutationSpeedDensity α θ₁ θ₂ x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [hb_def, ha_def]
    rw [speedDensityFrom_selectionMutation α θ₁ θ₂ c x ⟨hc0, hc1⟩ hx]
  have hsplit : ∀ x : ℝ, ENNReal.ofReal
      ((c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
        selectionMutationSpeedDensity α θ₁ θ₂ x) =
      ENNReal.ofReal (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
        ENNReal.ofReal (selectionMutationSpeedDensity α θ₁ θ₂ x) :=
    fun x => ENNReal.ofReal_mul hK
  have hpart : (∫⁻ x, ENNReal.ofReal (selectionMutationSpeedDensity α θ₁ θ₂ x)
      ∂(volume.restrict (Ioo (0 : ℝ) 1)))
      = ENNReal.ofReal (selectionMutationPartition α θ₁ θ₂) := by
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        (fun x => selectionMutationSpeedDensity α θ₁ θ₂ x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      simp only [selectionMutationSpeedDensity, mutationSpeedDensity]
      obtain ⟨hx0, hx1⟩ := hx
      have h1x : (0 : ℝ) < 1 - x := sub_pos.mpr hx1
      exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hx0) _))
          (Real.rpow_nonneg (le_of_lt h1x) _))
    have hmain := ofReal_integral_eq_lintegral_ofReal hInt hnn
    rw [← hmain]
    congr 1
    rw [selectionMutationPartition,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← hmeas]
  simp only [speedMeasureFrom]
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_congr_ae hae]
  simp only [hsplit]
  rw [lintegral_const_mul'' _ haemeas, hpart]
  exact (ENNReal.ofReal_mul hK).symm

end MathlibExt.Biology.PopulationGenetics.Diffusion

end
