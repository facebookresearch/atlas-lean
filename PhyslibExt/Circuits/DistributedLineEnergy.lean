/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Transmission-line energy balance

## i. Overview

For voltage and current fields satisfying the telegrapher
equations on a line segment `[0, ℓ]` with per-unit-length
parameters `R, L, G, C`, the stored line energy obeys a balance:
its pointwise density satisfies
`∂t u + ∂x p = -(R i² + G v²)`, and over a time window the energy
change equals the integrated endpoint power flux minus the
integrated dissipation. Lossless traveling waves carry flux at
the wave speed `1/√(LC)` with equal electric and magnetic energy
densities, and the shunt-discharge solution loses energy
strictly. Swapping the endpoint fluxes breaks the balance.

## ii. Key results

- `energyDensity_timeDeriv_add_powerFlux_spaceDeriv`: the
  pointwise energy identity.
- `lineEnergy_sub_eq_integral_endpointFlux_sub_dissipation`: the
  integrated balance over `[0, ℓ] × [t₀, t₁]`.
- `travelingWave_powerFlux_eq_speed_mul_energyDensity` and
  `travelingWave_electric_eq_magnetic`: the lossless traveling
  wave.
- `shuntDischarge_lineEnergy_strictAnti`: stored energy strictly
  decreases for the shunt discharge.

## iii. Table of contents

- A. Line energy and the telegrapher system

## iv. References

- J. D. Kraus and D. A. Fleisch, *Electromagnetics with
Applications*, fifth edition, McGraw-Hill, 1999: the telegrapher equations, Poynting flux on a line and
  stored line energy.

## A. Line energy and the telegrapher system
-/

@[expose] public section

open Set

namespace PhyslibExt.Circuits.DistributedLineEnergy

open Set

/-- Telegrapher equations on `U`: `v_x = -R i - L i_t` and `i_x = -G v - C v_t` at every
`(x, t) ∈ U`, with per-length constants `R L G C`. -/
def IsTelegrapherSolution (R L G C : ℝ) (U : Set (ℝ × ℝ)) (v i : ℝ → ℝ → ℝ) : Prop :=
  ∀ x t : ℝ, (x, t) ∈ U →
    deriv (fun y => v y t) x = -R * i x t - L * deriv (fun s => i x s) t ∧
      deriv (fun y => i y t) x = -G * v x t - C * deriv (fun s => v x s) t

/-- Stored energy per unit length `C v² / 2 + L i² / 2`. -/
noncomputable def energyDensity (L C : ℝ) (v i : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  C * v x t ^ 2 / 2 + L * i x t ^ 2 / 2

/-- Power flowing in the `+x` direction, `v i`. -/
noncomputable def powerFlux (v i : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  v x t * i x t

/-- Dissipated power per unit length `R i² + G v²`. -/
noncomputable def dissipationDensity (R G : ℝ) (v i : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  R * i x t ^ 2 + G * v x t ^ 2

/-- Energy stored on the line `[0, ℓ]` at time `t`. -/
noncomputable def lineEnergy (L C ℓ : ℝ) (v i : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..ℓ, energyDensity L C v i x t

-- Private helpers for the proofs below.

/-- Time slices of a `C¹` field on an open set are differentiable. -/
private theorem differentiableAt_timeSlice (U : Set (ℝ × ℝ)) (f : ℝ → ℝ → ℝ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) U) (x t : ℝ)
    (hxt : (x, t) ∈ U) : DifferentiableAt ℝ (fun s => f x s) t := by
  have hAt : ContDiffAt ℝ 1 (Function.uncurry f) (x, t) := hf.contDiffAt (hU.mem_nhds hxt)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) (x, t) := hAt.differentiableAt one_ne_zero
  have hF : HasFDerivAt (Function.uncurry f) (fderiv ℝ (Function.uncurry f) (x, t)) (x, t) :=
    hdiff.hasFDerivAt
  have hcurve : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (x, s)) t hF hcurve
  exact hcomp.differentiableAt

/-- Space slices of a `C¹` field on an open set are differentiable. -/
private theorem differentiableAt_spaceSlice (U : Set (ℝ × ℝ)) (f : ℝ → ℝ → ℝ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) U) (x t : ℝ)
    (hxt : (x, t) ∈ U) : DifferentiableAt ℝ (fun y => f y t) x := by
  have hAt : ContDiffAt ℝ 1 (Function.uncurry f) (x, t) := hf.contDiffAt (hU.mem_nhds hxt)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) (x, t) := hAt.differentiableAt one_ne_zero
  have hF : HasFDerivAt (Function.uncurry f) (fderiv ℝ (Function.uncurry f) (x, t)) (x, t) :=
    hdiff.hasFDerivAt
  have hcurve : HasDerivAt (fun y : ℝ => (y, t)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun y : ℝ => (y, t)) x hF hcurve
  exact hcomp.differentiableAt

/-- Time-slice derivatives agree with the `fderiv` applied to `(0, 1)`. -/
private theorem sliceDeriv_eq_fderiv_time (U : Set (ℝ × ℝ)) (f : ℝ → ℝ → ℝ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) U) (x t : ℝ)
    (hxt : (x, t) ∈ U) :
    deriv (fun s => f x s) t = fderiv ℝ (Function.uncurry f) (x, t) (0, 1) := by
  have hAt : ContDiffAt ℝ 1 (Function.uncurry f) (x, t) := hf.contDiffAt (hU.mem_nhds hxt)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) (x, t) := hAt.differentiableAt one_ne_zero
  have hF : HasFDerivAt (Function.uncurry f) (fderiv ℝ (Function.uncurry f) (x, t)) (x, t) :=
    hdiff.hasFDerivAt
  have hcurve : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have hcomp : HasDerivAt (fun s => f x s) (fderiv ℝ (Function.uncurry f) (x, t) (0, 1)) t :=
    HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (x, s)) t hF hcurve
  exact hcomp.deriv

/-- Space-slice derivatives agree with the `fderiv` applied to `(1, 0)`. -/
private theorem sliceDeriv_eq_fderiv_space (U : Set (ℝ × ℝ)) (f : ℝ → ℝ → ℝ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) U) (x t : ℝ)
    (hxt : (x, t) ∈ U) :
    deriv (fun y => f y t) x = fderiv ℝ (Function.uncurry f) (x, t) (1, 0) := by
  have hAt : ContDiffAt ℝ 1 (Function.uncurry f) (x, t) := hf.contDiffAt (hU.mem_nhds hxt)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) (x, t) := hAt.differentiableAt one_ne_zero
  have hF : HasFDerivAt (Function.uncurry f) (fderiv ℝ (Function.uncurry f) (x, t)) (x, t) :=
    hdiff.hasFDerivAt
  have hcurve : HasDerivAt (fun y : ℝ => (y, t)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  have hcomp : HasDerivAt (fun y => f y t) (fderiv ℝ (Function.uncurry f) (x, t) (1, 0)) x :=
    HasFDerivAt.comp_hasDerivAt (f := fun y : ℝ => (y, t)) x hF hcurve
  exact hcomp.deriv

/-- `√(L*C) = C * √(L/C)` for positive `L, C`. -/
private theorem sqrt_mul_eq (L C : ℝ) (hL : 0 < L) (hC : 0 < C) :
    Real.sqrt (L * C) = C * Real.sqrt (L / C) := by
  have hC' : C ≠ 0 := ne_of_gt hC
  have h1 : C ^ 2 * (L / C) = L * C := by
    field_simp [hC']
  have h2 : Real.sqrt (C ^ 2 * (L / C)) = Real.sqrt (C ^ 2) * Real.sqrt (L / C) :=
    Real.sqrt_mul (sq_nonneg C) _
  rw [Real.sqrt_sq (le_of_lt hC)] at h2
  rw [h1] at h2
  exact h2

/-- `√(L*C) * √(L/C) = L` for positive `L, C`. -/
private theorem sqrt_mul_sqrt_eq (L C : ℝ) (hL : 0 < L) (hC : 0 < C) :
    Real.sqrt (L * C) * Real.sqrt (L / C) = L := by
  have hC' : C ≠ 0 := ne_of_gt hC
  have h1 : (Real.sqrt (L * C) * Real.sqrt (L / C)) ^ 2 = L ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt (mul_pos hL hC)),
      Real.sq_sqrt (le_of_lt (div_pos hL hC))]
    field_simp [hC']
  have hnn : 0 ≤ Real.sqrt (L * C) * Real.sqrt (L / C) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc Real.sqrt (L * C) * Real.sqrt (L / C)
      = Real.sqrt ((Real.sqrt (L * C) * Real.sqrt (L / C)) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ = Real.sqrt (L ^ 2) := by rw [h1]
    _ = L := Real.sqrt_sq (le_of_lt hL)

/-- Integral of `x²` over `[a, b]`, by FTC with antiderivative `x*x*x/3`. -/
private theorem integral_sq (a b : ℝ) : ∫ x in a..b, x ^ 2 = (b ^ 3 - a ^ 3) / 3 := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => y * y * y / 3) (x ^ 2) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have h3 : HasDerivAt (fun y : ℝ => y * y * y / 3)
        (((1 * x + x * 1) * x + x * x * 1) / 3) x :=
      ((h1.mul h1).mul h1).div_const 3
    have hval : ((1 * x + x * 1) * x + x * x * 1) / 3 = x ^ 2 := by ring
    rw [hval] at h3
    exact h3
  have hint : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume a b :=
    (continuous_pow 2).intervalIntegrable a b
  have hFTC : (∫ y in a..b, y ^ 2) = b * b * b / 3 - a * a * a / 3 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc (∫ x in a..b, x ^ 2) = b * b * b / 3 - a * a * a / 3 := hFTC
    _ = (b ^ 3 - a ^ 3) / 3 := by ring

/-- A compact segment in an open set has a uniform time-neighborhood in the set. -/
private theorem exists_ball_slab (U : Set (ℝ × ℝ)) (ℓ t : ℝ)
    (hU : IsOpen U) (hseg : Set.Icc 0 ℓ ×ˢ {t} ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ Set.Icc 0 ℓ ×ˢ Metric.ball t ε ⊆ U := by
  obtain ⟨V, W, hVopen, hWopen, hKV, htW, hVWU⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hU hseg
  have htm : t ∈ ({t} : Set ℝ) := by simp
  obtain ⟨ε, hε, hballW⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds (htW htm))
  refine ⟨ε, hε, ?_⟩
  rintro ⟨x, s⟩ ⟨hx, hs⟩
  exact hVWU (Set.mk_mem_prod (hKV hx) (hballW hs))

/-- A continuous function on a compact set is norm-bounded. -/
private theorem exists_norm_bound_of_continuousOn_compact {K : Set (ℝ × ℝ)}
    {g : ℝ × ℝ → ℝ} (hK : IsCompact K) (hg : ContinuousOn g K) :
    ∃ C : ℝ, ∀ p ∈ K, ‖g p‖ ≤ C := by
  have h1 : IsCompact (g '' K) := hK.image_of_continuousOn hg
  obtain ⟨C, hC⟩ := h1.isBounded.subset_ball 0
  refine ⟨C, fun p hp => ?_⟩
  have hmem : g p ∈ Metric.ball (0 : ℝ) C := hC ⟨p, hp, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hmem
  exact le_of_lt hmem

/-- `fderiv` partials of a `C¹` field are continuous on the open set. -/
private theorem continuousOn_fderivApply (U : Set (ℝ × ℝ)) (f : ℝ → ℝ → ℝ)
    (w : ℝ × ℝ) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) U) :
    ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry f) p w) U := by
  have hfd : ContinuousOn (fderiv ℝ (Function.uncurry f)) U :=
    hf.continuousOn_fderiv_of_isOpen hU le_rfl
  exact hfd.clm_apply continuousOn_const

/-- Space slices of a `C¹` field are continuous on segments in `U`. -/
private theorem continuousOn_spaceSlice_of_mem (U : Set (ℝ × ℝ)) (f : ℝ → ℝ → ℝ)
    (ℓ s : ℝ) (_hU : IsOpen U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) U)
    (hmem : ∀ x ∈ Set.Icc 0 ℓ, (x, s) ∈ U) :
    ContinuousOn (fun x => f x s) (Set.Icc 0 ℓ) := by
  have hC : ContinuousOn (Function.uncurry f) U := hf.continuousOn
  have hcurve : ContinuousOn (fun x : ℝ => (x, s)) (Set.Icc 0 ℓ) :=
    (continuous_id'.prodMk continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun x : ℝ => (x, s)) (Set.Icc 0 ℓ) U := fun x hx => hmem x hx
  exact hC.comp hcurve hmaps

/-- Time slices of a `C¹` field are continuous on segments in `U`. -/
private theorem continuousOn_timeSlice_of_mem (U : Set (ℝ × ℝ)) (f : ℝ → ℝ → ℝ)
    (t₀ t₁ c : ℝ) (_hU : IsOpen U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) U)
    (hmem : ∀ s ∈ Set.Icc t₀ t₁, (c, s) ∈ U) :
    ContinuousOn (fun s => f c s) (Set.Icc t₀ t₁) := by
  have hC : ContinuousOn (Function.uncurry f) U := hf.continuousOn
  have hcurve : ContinuousOn (fun s : ℝ => (c, s)) (Set.Icc t₀ t₁) :=
    (continuous_const.prodMk continuous_id').continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ => (c, s)) (Set.Icc t₀ t₁) U := fun s hs => hmem s hs
  exact hC.comp hcurve hmaps

/-- Space slices of `fderiv` partials are continuous on segments in `U`. -/
private theorem continuousOn_fderivSpaceSlice (U : Set (ℝ × ℝ)) (f : ℝ → ℝ → ℝ)
    (ℓ s : ℝ) (w : ℝ × ℝ) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 (Function.uncurry f) U)
    (hmem : ∀ x ∈ Set.Icc 0 ℓ, (x, s) ∈ U) :
    ContinuousOn (fun x => fderiv ℝ (Function.uncurry f) (x, s) w) (Set.Icc 0 ℓ) := by
  have hC : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry f) p w) U :=
    continuousOn_fderivApply U f w hU hf
  have hcurve : ContinuousOn (fun x : ℝ => (x, s)) (Set.Icc 0 ℓ) :=
    (continuous_id'.prodMk continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun x : ℝ => (x, s)) (Set.Icc 0 ℓ) U := fun x hx => hmem x hx
  exact hC.comp hcurve hmaps

/-- Space slices of the dissipation density are continuous on segments in `U`. -/
private theorem continuousOn_dissSpaceSlice (R G ℓ s : ℝ) (U : Set (ℝ × ℝ))
    (v i : ℝ → ℝ → ℝ) (hU : IsOpen U) (hv : ContDiffOn ℝ 1 (Function.uncurry v) U)
    (hi : ContDiffOn ℝ 1 (Function.uncurry i) U)
    (hmem : ∀ x ∈ Set.Icc 0 ℓ, (x, s) ∈ U) :
    ContinuousOn (fun x => dissipationDensity R G v i x s) (Set.Icc 0 ℓ) := by
  have hvS := continuousOn_spaceSlice_of_mem U v ℓ s hU hv hmem
  have hiS := continuousOn_spaceSlice_of_mem U i ℓ s hU hi hmem
  have hi2 := hiS.pow 2
  have hv2 := hvS.pow 2
  have h1 := hi2.const_mul R
  have h2 := hv2.const_mul G
  exact h1.add h2

/-- Space slices of the energy density are continuous on segments in `U`. -/
private theorem continuousOn_energySpaceSlice (L C ℓ s : ℝ) (U : Set (ℝ × ℝ))
    (v i : ℝ → ℝ → ℝ) (hU : IsOpen U) (hv : ContDiffOn ℝ 1 (Function.uncurry v) U)
    (hi : ContDiffOn ℝ 1 (Function.uncurry i) U)
    (hmem : ∀ x ∈ Set.Icc 0 ℓ, (x, s) ∈ U) :
    ContinuousOn (fun x => energyDensity L C v i x s) (Set.Icc 0 ℓ) := by
  have hvS := continuousOn_spaceSlice_of_mem U v ℓ s hU hv hmem
  have hiS := continuousOn_spaceSlice_of_mem U i ℓ s hU hi hmem
  have hv2 := hvS.pow 2
  have hi2 := hiS.pow 2
  have hCv := hv2.const_mul C
  have hLi := hi2.const_mul L
  have hCvd := hCv.div_const 2
  have hLid := hLi.div_const 2
  exact hCvd.add hLid

/-- A time-segment of the space-time rectangle lies in `U`. -/
private theorem segment_subset_of_rect (ℓ t₀ t₁ s : ℝ) (U : Set (ℝ × ℝ))
    (hs : s ∈ Set.Icc t₀ t₁) (hrect : Set.Icc 0 ℓ ×ˢ Set.Icc t₀ t₁ ⊆ U) :
    Set.Icc 0 ℓ ×ˢ {s} ⊆ U := by
  intro p hp
  obtain ⟨x, s'⟩ := p
  obtain ⟨hx, hs'⟩ := hp
  have hss : s' = s := Set.mem_singleton_iff.mp hs'
  subst hss
  exact hrect (Set.mk_mem_prod hx hs)

/-- Time-slice derivative of the dissipation density, in `fderiv` form. -/
private theorem hasDerivAt_dissSlice (R G : ℝ) (U : Set (ℝ × ℝ)) (v i : ℝ → ℝ → ℝ)
    (hU : IsOpen U) (hv : ContDiffOn ℝ 1 (Function.uncurry v) U)
    (hi : ContDiffOn ℝ 1 (Function.uncurry i) U) (x s : ℝ) (hxs : (x, s) ∈ U) :
    HasDerivAt (fun s' => dissipationDensity R G v i x s')
      (2 * R * (i x s) * (fderiv ℝ (Function.uncurry i) (x, s) (0, 1)) +
        2 * G * (v x s) * (fderiv ℝ (Function.uncurry v) (x, s) (0, 1))) s := by
  have hi_t := (differentiableAt_timeSlice U i hU hi x s hxs).hasDerivAt
  have hv_t := (differentiableAt_timeSlice U v hU hv x s hxs).hasDerivAt
  have hraw : HasDerivAt (fun s' => R * (i x s' * i x s') + G * (v x s' * v x s'))
      (R * (deriv (fun s' => i x s') s * i x s + i x s * deriv (fun s' => i x s') s) +
        G * (deriv (fun s' => v x s') s * v x s + v x s * deriv (fun s' => v x s') s)) s :=
    ((hi_t.mul hi_t).const_mul R).add ((hv_t.mul hv_t).const_mul G)
  have hval : R * (deriv (fun s' => i x s') s * i x s + i x s * deriv (fun s' => i x s') s) +
        G * (deriv (fun s' => v x s') s * v x s + v x s * deriv (fun s' => v x s') s)
      = 2 * R * (i x s) * (fderiv ℝ (Function.uncurry i) (x, s) (0, 1)) +
        2 * G * (v x s) * (fderiv ℝ (Function.uncurry v) (x, s) (0, 1)) := by
    rw [sliceDeriv_eq_fderiv_time U i hU hi x s hxs,
      sliceDeriv_eq_fderiv_time U v hU hv x s hxs]
    ring
  rw [hval] at hraw
  have h := hraw
  simp only [← pow_two] at h
  exact h

/-- The dissipation integral over `[0, ℓ]` is continuous in time on `[t₀, t₁]`. -/
private theorem continuousOn_dissIntegral (R G ℓ t₀ t₁ : ℝ) (U : Set (ℝ × ℝ))
    (v i : ℝ → ℝ → ℝ) (hU : IsOpen U) (hv : ContDiffOn ℝ 1 (Function.uncurry v) U)
    (hi : ContDiffOn ℝ 1 (Function.uncurry i) U) (hℓ : 0 < ℓ) (_ht : t₀ ≤ t₁)
    (hrect : Set.Icc 0 ℓ ×ˢ Set.Icc t₀ t₁ ⊆ U) :
    ContinuousOn (fun s => ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s)
      (Set.Icc t₀ t₁) := by
  apply continuousOn_of_forall_continuousAt
  intro s₀ hs₀
  have hseg : Set.Icc 0 ℓ ×ˢ {s₀} ⊆ U := segment_subset_of_rect ℓ t₀ t₁ s₀ U hs₀ hrect
  obtain ⟨ε, hε, hslab⟩ := exists_ball_slab U ℓ s₀ hU hseg
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  have hsub2 : Metric.ball s₀ (ε / 2) ⊆ Metric.ball s₀ ε :=
    Metric.ball_subset_ball (by linarith)
  have hmem_of : ∀ s ∈ Metric.ball s₀ (ε / 2), ∀ x ∈ Set.Icc (0 : ℝ) ℓ, (x, s) ∈ U := by
    intro s hs x hx
    exact hslab (Set.mk_mem_prod hx (hsub2 hs))
  have hFcont : ContinuousOn (fun p : ℝ × ℝ =>
      2 * R * ((Function.uncurry i) p) * (fderiv ℝ (Function.uncurry i) p (0, 1)) +
        2 * G * ((Function.uncurry v) p) * (fderiv ℝ (Function.uncurry v) p (0, 1))) U := by
    have hiC : ContinuousOn (Function.uncurry i) U := hi.continuousOn
    have hvC : ContinuousOn (Function.uncurry v) U := hv.continuousOn
    have hitC : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry i) p (0, 1)) U :=
      continuousOn_fderivApply U i (0, 1) hU hi
    have hvtC : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry v) p (0, 1)) U :=
      continuousOn_fderivApply U v (0, 1) hU hv
    have e1 : ContinuousOn (fun p : ℝ × ℝ => 2 * R * (Function.uncurry i) p *
        (fderiv ℝ (Function.uncurry i) p (0, 1))) U :=
      (hiC.const_mul (2 * R)).mul hitC
    have e2 : ContinuousOn (fun p : ℝ × ℝ => 2 * G * (Function.uncurry v) p *
        (fderiv ℝ (Function.uncurry v) p (0, 1))) U :=
      (hvC.const_mul (2 * G)).mul hvtC
    exact e1.add e2
  have hKcomp : IsCompact (Set.Icc (0 : ℝ) ℓ ×ˢ Metric.closedBall s₀ (ε / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKU : Set.Icc (0 : ℝ) ℓ ×ˢ Metric.closedBall s₀ (ε / 2) ⊆ U := by
    rintro ⟨x, s⟩ ⟨hx, hs⟩
    apply hslab
    refine Set.mk_mem_prod hx ?_
    rw [Metric.mem_ball]
    calc dist s s₀ ≤ ε / 2 := Metric.mem_closedBall.mp hs
      _ < ε := by linarith
  have hFcontK : ContinuousOn (fun p : ℝ × ℝ =>
      2 * R * ((Function.uncurry i) p) * (fderiv ℝ (Function.uncurry i) p (0, 1)) +
        2 * G * ((Function.uncurry v) p) * (fderiv ℝ (Function.uncurry v) p (0, 1)))
      (Set.Icc (0 : ℝ) ℓ ×ˢ Metric.closedBall s₀ (ε / 2)) :=
    hFcont.mono hKU
  obtain ⟨M, hM⟩ := exists_norm_bound_of_continuousOn_compact hKcomp hFcontK
  have hF : ∀ s ∈ Metric.ball s₀ (ε / 2),
      MeasureTheory.AEStronglyMeasurable (fun x => dissipationDensity R G v i x s)
        (MeasureTheory.volume.restrict (Set.uIoc 0 ℓ)) := by
    intro s hs
    have hsub : Set.uIoc (0 : ℝ) ℓ ⊆ Set.Icc 0 ℓ := by
      rw [Set.uIoc_of_le hℓ.le]
      exact Set.Ioc_subset_Icc_self
    have hmeas : MeasurableSet (Set.uIoc (0 : ℝ) ℓ) := by
      rw [Set.uIoc_of_le hℓ.le]
      exact measurableSet_Ioc
    exact ((continuousOn_dissSpaceSlice R G ℓ s U v i hU hv hi
      (hmem_of s hs)).mono hsub).aestronglyMeasurable hmeas
  have hF' : MeasureTheory.AEStronglyMeasurable
      (fun x => 2 * R * (i x s₀) * (fderiv ℝ (Function.uncurry i) (x, s₀) (0, 1)) +
        2 * G * (v x s₀) * (fderiv ℝ (Function.uncurry v) (x, s₀) (0, 1)))
      (MeasureTheory.volume.restrict (Set.uIoc 0 ℓ)) := by
    have hsub : Set.uIoc (0 : ℝ) ℓ ⊆ Set.Icc 0 ℓ := by
      rw [Set.uIoc_of_le hℓ.le]
      exact Set.Ioc_subset_Icc_self
    have hmeas : MeasurableSet (Set.uIoc (0 : ℝ) ℓ) := by
      rw [Set.uIoc_of_le hℓ.le]
      exact measurableSet_Ioc
    have hmaps : Set.MapsTo (fun x : ℝ => (x, s₀)) (Set.Icc 0 ℓ) U := fun x hx =>
      hseg (Set.mk_mem_prod hx (by simp : s₀ ∈ ({s₀} : Set ℝ)))
    have hcurve : ContinuousOn (fun x : ℝ => (x, s₀)) (Set.Icc 0 ℓ) :=
      (continuous_id'.prodMk continuous_const).continuousOn
    have hc : ContinuousOn (fun x => 2 * R * (i x s₀) *
        (fderiv ℝ (Function.uncurry i) (x, s₀) (0, 1)) +
        2 * G * (v x s₀) * (fderiv ℝ (Function.uncurry v) (x, s₀) (0, 1)))
        (Set.Icc 0 ℓ) :=
      hFcont.comp hcurve hmaps
    exact (hc.mono hsub).aestronglyMeasurable hmeas
  have hs_mem : Metric.ball s₀ (ε / 2) ∈ nhds s₀ := Metric.ball_mem_nhds s₀ hδ
  have hF_meas : ∀ᶠ s in nhds s₀,
      MeasureTheory.AEStronglyMeasurable (fun x => dissipationDensity R G v i x s)
        (MeasureTheory.volume.restrict (Set.uIoc 0 ℓ)) :=
    Filter.eventually_of_mem hs_mem hF
  have hF_int : IntervalIntegrable (fun x => dissipationDensity R G v i x s₀)
      MeasureTheory.volume 0 ℓ := by
    have hmem_s₀ : ∀ x ∈ Set.Icc (0 : ℝ) ℓ, (x, s₀) ∈ U := fun x hx =>
      hseg (Set.mk_mem_prod hx (by simp : s₀ ∈ ({s₀} : Set ℝ)))
    have h := continuousOn_dissSpaceSlice R G ℓ s₀ U v i hU hv hi hmem_s₀
    rw [← Set.uIcc_of_le hℓ.le] at h
    exact h.intervalIntegrable
  have hsubI : Set.uIoc (0 : ℝ) ℓ ⊆ Set.Icc 0 ℓ := by
    rw [Set.uIoc_of_le hℓ.le]
    exact Set.Ioc_subset_Icc_self
  have hle : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc 0 ℓ →
      ∀ s ∈ Metric.ball s₀ (ε / 2),
      ‖2 * R * (i x s) * (fderiv ℝ (Function.uncurry i) (x, s) (0, 1)) +
        2 * G * (v x s) * (fderiv ℝ (Function.uncurry v) (x, s) (0, 1))‖ ≤ M := by
    filter_upwards [Filter.Eventually.of_forall (fun x hx => hsubI hx)] with x hxIcc
    intro hx s hs
    exact hM (x, s) (Set.mk_mem_prod (hxIcc hx) (Metric.ball_subset_closedBall hs))
  have hbound : IntervalIntegrable (fun _ : ℝ => M) MeasureTheory.volume 0 ℓ :=
    continuous_const.intervalIntegrable 0 ℓ
  have hdiff : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc 0 ℓ →
      ∀ s ∈ Metric.ball s₀ (ε / 2),
      HasDerivAt (fun s' => dissipationDensity R G v i x s')
        (2 * R * (i x s) * (fderiv ℝ (Function.uncurry i) (x, s) (0, 1)) +
          2 * G * (v x s) * (fderiv ℝ (Function.uncurry v) (x, s) (0, 1))) s := by
    filter_upwards [Filter.Eventually.of_forall (fun x hx => hsubI hx)] with x hxIcc
    intro hx s hs
    exact hasDerivAt_dissSlice R G U v i hU hv hi x s (hmem_of s hs x (hxIcc hx))
  have hpar : HasDerivAt (fun s => ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s)
      (∫ x in (0 : ℝ)..ℓ, 2 * R * (i x s₀) * (fderiv ℝ (Function.uncurry i) (x, s₀) (0, 1)) +
        2 * G * (v x s₀) * (fderiv ℝ (Function.uncurry v) (x, s₀) (0, 1))) s₀ :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs_mem hF_meas hF_int hF' hle hbound hdiff).2
  exact hpar.continuousAt

/-- **Local energy identity**: `∂ₜ(C v²/2 + L i²/2) + ∂ₓ(v i) = -(R i² + G v²)`. -/
lemma energyDensity_timeDeriv_add_powerFlux_spaceDeriv (R L G C : ℝ) (U : Set (ℝ × ℝ))
    (v i : ℝ → ℝ → ℝ) (hU : IsOpen U) (hv : ContDiffOn ℝ 1 (Function.uncurry v) U)
    (hi : ContDiffOn ℝ 1 (Function.uncurry i) U) (htel : IsTelegrapherSolution R L G C U v i)
    (x t : ℝ) (hxt : (x, t) ∈ U) :
    deriv (fun s => energyDensity L C v i x s) t + deriv (fun y => powerFlux v i y t) x =
      -dissipationDensity R G v i x t := by
  obtain ⟨hvx, hix⟩ := htel x t hxt
  have hv_t : HasDerivAt (fun s => v x s) (deriv (fun s => v x s) t) t :=
    (differentiableAt_timeSlice U v hU hv x t hxt).hasDerivAt
  have hi_t : HasDerivAt (fun s => i x s) (deriv (fun s => i x s) t) t :=
    (differentiableAt_timeSlice U i hU hi x t hxt).hasDerivAt
  have hv_x : HasDerivAt (fun y => v y t) (deriv (fun y => v y t) x) x :=
    (differentiableAt_spaceSlice U v hU hv x t hxt).hasDerivAt
  have hi_x : HasDerivAt (fun y => i y t) (deriv (fun y => i y t) x) x :=
    (differentiableAt_spaceSlice U i hU hi x t hxt).hasDerivAt
  have hEv := ((hv_t.mul hv_t).const_mul C).div_const 2
  have hEi := ((hi_t.mul hi_t).const_mul L).div_const 2
  have hEmul : HasDerivAt (fun s => C * (v x s * v x s) / 2 + L * (i x s * i x s) / 2)
      (C * (deriv (fun s => v x s) t * v x t + v x t * deriv (fun s => v x s) t) / 2 +
        L * (deriv (fun s => i x s) t * i x t + i x t * deriv (fun s => i x s) t) / 2) t :=
    hEv.add hEi
  have hE : HasDerivAt (fun s => energyDensity L C v i x s)
      (C * (deriv (fun s => v x s) t * v x t + v x t * deriv (fun s => v x s) t) / 2 +
        L * (deriv (fun s => i x s) t * i x t + i x t * deriv (fun s => i x s) t) / 2) t := by
    have h := hEmul
    simp only [← pow_two] at h
    exact h
  have hP : HasDerivAt (fun y => powerFlux v i y t)
      (deriv (fun y => v y t) x * i x t + v x t * deriv (fun y => i y t) x) x :=
    hv_x.mul hi_x
  rw [hE.deriv, hP.deriv, hvx, hix]
  have hdiss : dissipationDensity R G v i x t = R * i x t ^ 2 + G * v x t ^ 2 := rfl
  rw [hdiss]
  ring

/-- Time-slice derivative of the energy density, in `fderiv`/flux form. -/
private theorem hasDerivAt_energySlice (R L G C : ℝ) (U : Set (ℝ × ℝ)) (v i : ℝ → ℝ → ℝ)
    (hU : IsOpen U) (hv : ContDiffOn ℝ 1 (Function.uncurry v) U)
    (hi : ContDiffOn ℝ 1 (Function.uncurry i) U)
    (htel : IsTelegrapherSolution R L G C U v i) (x s : ℝ) (hxs : (x, s) ∈ U) :
    HasDerivAt (fun s' => energyDensity L C v i x s')
      (-((fderiv ℝ (Function.uncurry v) (x, s) (1, 0)) * i x s +
          v x s * (fderiv ℝ (Function.uncurry i) (x, s) (1, 0))) -
        dissipationDensity R G v i x s) s := by
  have hv_t := (differentiableAt_timeSlice U v hU hv x s hxs).hasDerivAt
  have hi_t := (differentiableAt_timeSlice U i hU hi x s hxs).hasDerivAt
  have hv_x := (differentiableAt_spaceSlice U v hU hv x s hxs).hasDerivAt
  have hi_x := (differentiableAt_spaceSlice U i hU hi x s hxs).hasDerivAt
  have hEchain : HasDerivAt (fun s' => energyDensity L C v i x s')
      (C * v x s * deriv (fun s' => v x s') s + L * i x s * deriv (fun s' => i x s') s) s := by
    have hEv := ((hv_t.mul hv_t).const_mul C).div_const 2
    have hEi := ((hi_t.mul hi_t).const_mul L).div_const 2
    have hraw : HasDerivAt (fun s' => C * (v x s' * v x s') / 2 + L * (i x s' * i x s') / 2)
        (C * (deriv (fun s' => v x s') s * v x s + v x s * deriv (fun s' => v x s') s) / 2 +
          L * (deriv (fun s' => i x s') s * i x s + i x s * deriv (fun s' => i x s') s) / 2) s :=
      hEv.add hEi
    have hnorm : C * (deriv (fun s' => v x s') s * v x s + v x s * deriv (fun s' => v x s') s) / 2 +
          L * (deriv (fun s' => i x s') s * i x s + i x s * deriv (fun s' => i x s') s) / 2
        = C * v x s * deriv (fun s' => v x s') s + L * i x s * deriv (fun s' => i x s') s := by
      ring
    rw [hnorm] at hraw
    have h := hraw
    simp only [← pow_two] at h
    exact h
  have h1 := energyDensity_timeDeriv_add_powerFlux_spaceDeriv R L G C U v i hU hv hi htel x s hxs
  have hPval : deriv (fun y => powerFlux v i y s) x
      = (fderiv ℝ (Function.uncurry v) (x, s) (1, 0)) * i x s +
        v x s * (fderiv ℝ (Function.uncurry i) (x, s) (1, 0)) := by
    have h : deriv (fun y => powerFlux v i y s) x
        = deriv (fun y => v y s) x * i x s + v x s * deriv (fun y => i y s) x :=
      (hv_x.mul hi_x).deriv
    rw [sliceDeriv_eq_fderiv_space U v hU hv x s hxs,
      sliceDeriv_eq_fderiv_space U i hU hi x s hxs] at h
    exact h
  have hEval : C * v x s * deriv (fun s' => v x s') s + L * i x s * deriv (fun s' => i x s') s
      = -((fderiv ℝ (Function.uncurry v) (x, s) (1, 0)) * i x s +
          v x s * (fderiv ℝ (Function.uncurry i) (x, s) (1, 0))) -
        dissipationDensity R G v i x s := by
    have heQ : deriv (fun s' => energyDensity L C v i x s') s
        = C * v x s * deriv (fun s' => v x s') s + L * i x s * deriv (fun s' => i x s') s :=
      hEchain.deriv
    rw [← heQ]
    rw [hPval] at h1
    linarith [h1]
  rw [hEval] at hEchain
  exact hEchain

/-- Rate form of the finite-line balance: `dE/dt = S(0,t) - S(ℓ,t) - ∫₀^ℓ (R i² + G v²)`,
given C1 fields on an open set containing the segment `[0, ℓ] × {t}`. -/
lemma hasDerivAt_lineEnergy (R L G C ℓ t : ℝ) (U : Set (ℝ × ℝ)) (v i : ℝ → ℝ → ℝ)
    (hU : IsOpen U) (hv : ContDiffOn ℝ 1 (Function.uncurry v) U)
    (hi : ContDiffOn ℝ 1 (Function.uncurry i) U) (htel : IsTelegrapherSolution R L G C U v i)
    (hℓ : 0 < ℓ) (hseg : Icc 0 ℓ ×ˢ {t} ⊆ U) :
    HasDerivAt (fun s => lineEnergy L C ℓ v i s)
      (powerFlux v i 0 t - powerFlux v i ℓ t -
        ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x t) t := by
  obtain ⟨ε, hε, hslab⟩ := exists_ball_slab U ℓ t hU hseg
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  have hsub2 : Metric.ball t (ε / 2) ⊆ Metric.ball t ε :=
    Metric.ball_subset_ball (by linarith)
  have hmem_of : ∀ s ∈ Metric.ball t (ε / 2), ∀ x ∈ Set.Icc (0 : ℝ) ℓ, (x, s) ∈ U := by
    intro s hs x hx
    exact hslab (Set.mk_mem_prod hx (hsub2 hs))
  have hmem_t : ∀ x ∈ Set.Icc (0 : ℝ) ℓ, (x, t) ∈ U := fun x hx =>
    hseg (Set.mk_mem_prod hx (by simp : t ∈ ({t} : Set ℝ)))
  have hFcont : ContinuousOn (fun p : ℝ × ℝ =>
      -((fderiv ℝ (Function.uncurry v) p (1, 0)) * (Function.uncurry i) p +
        (Function.uncurry v) p * (fderiv ℝ (Function.uncurry i) p (1, 0))) -
      dissipationDensity R G v i p.1 p.2) U := by
    have hiC : ContinuousOn (Function.uncurry i) U := hi.continuousOn
    have hvC : ContinuousOn (Function.uncurry v) U := hv.continuousOn
    have hvxC : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry v) p (1, 0)) U :=
      continuousOn_fderivApply U v (1, 0) hU hv
    have hixC : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry i) p (1, 0)) U :=
      continuousOn_fderivApply U i (1, 0) hU hi
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (fderiv ℝ (Function.uncurry v) p (1, 0)) * (Function.uncurry i) p) U :=
      hvxC.mul hiC
    have h2 : ContinuousOn (fun p : ℝ × ℝ =>
        (Function.uncurry v) p * (fderiv ℝ (Function.uncurry i) p (1, 0))) U :=
      hvC.mul hixC
    have hG : ContinuousOn (fun p : ℝ × ℝ =>
        (fderiv ℝ (Function.uncurry v) p (1, 0)) * (Function.uncurry i) p +
        (Function.uncurry v) p * (fderiv ℝ (Function.uncurry i) p (1, 0))) U :=
      h1.add h2
    have hdiss : ContinuousOn (fun p : ℝ × ℝ => dissipationDensity R G v i p.1 p.2) U := by
      have hi2 : ContinuousOn (fun p : ℝ × ℝ => ((Function.uncurry i) p) ^ 2) U :=
        hiC.pow 2
      have hv2 : ContinuousOn (fun p : ℝ × ℝ => ((Function.uncurry v) p) ^ 2) U :=
        hvC.pow 2
      have hRi : ContinuousOn (fun p : ℝ × ℝ => R * ((Function.uncurry i) p) ^ 2) U :=
        hi2.const_mul R
      have hGv : ContinuousOn (fun p : ℝ × ℝ => G * ((Function.uncurry v) p) ^ 2) U :=
        hv2.const_mul G
      exact hRi.add hGv
    exact hG.neg.sub hdiss
  have hKcomp : IsCompact (Set.Icc (0 : ℝ) ℓ ×ˢ Metric.closedBall t (ε / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKU : Set.Icc (0 : ℝ) ℓ ×ˢ Metric.closedBall t (ε / 2) ⊆ U := by
    rintro ⟨x, s⟩ ⟨hx, hs⟩
    apply hslab
    refine Set.mk_mem_prod hx ?_
    rw [Metric.mem_ball]
    calc dist s t ≤ ε / 2 := Metric.mem_closedBall.mp hs
      _ < ε := by linarith
  have hFcontK : ContinuousOn (fun p : ℝ × ℝ =>
      -((fderiv ℝ (Function.uncurry v) p (1, 0)) * (Function.uncurry i) p +
        (Function.uncurry v) p * (fderiv ℝ (Function.uncurry i) p (1, 0))) -
      dissipationDensity R G v i p.1 p.2)
      (Set.Icc (0 : ℝ) ℓ ×ˢ Metric.closedBall t (ε / 2)) :=
    hFcont.mono hKU
  obtain ⟨M, hM⟩ := exists_norm_bound_of_continuousOn_compact hKcomp hFcontK
  have hF : ∀ s ∈ Metric.ball t (ε / 2),
      MeasureTheory.AEStronglyMeasurable (fun x => energyDensity L C v i x s)
        (MeasureTheory.volume.restrict (Set.uIoc 0 ℓ)) := by
    intro s hs
    have hsub : Set.uIoc (0 : ℝ) ℓ ⊆ Set.Icc 0 ℓ := by
      rw [Set.uIoc_of_le hℓ.le]
      exact Set.Ioc_subset_Icc_self
    have hmeas : MeasurableSet (Set.uIoc (0 : ℝ) ℓ) := by
      rw [Set.uIoc_of_le hℓ.le]
      exact measurableSet_Ioc
    exact ((continuousOn_energySpaceSlice L C ℓ s U v i hU hv hi
      (hmem_of s hs)).mono hsub).aestronglyMeasurable hmeas
  have hF' : MeasureTheory.AEStronglyMeasurable
      (fun x => -((fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
        v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0))) -
        dissipationDensity R G v i x t)
      (MeasureTheory.volume.restrict (Set.uIoc 0 ℓ)) := by
    have hsub : Set.uIoc (0 : ℝ) ℓ ⊆ Set.Icc 0 ℓ := by
      rw [Set.uIoc_of_le hℓ.le]
      exact Set.Ioc_subset_Icc_self
    have hmeas : MeasurableSet (Set.uIoc (0 : ℝ) ℓ) := by
      rw [Set.uIoc_of_le hℓ.le]
      exact measurableSet_Ioc
    have hmaps : Set.MapsTo (fun x : ℝ => (x, t)) (Set.Icc 0 ℓ) U := fun x hx => hmem_t x hx
    have hcurve : ContinuousOn (fun x : ℝ => (x, t)) (Set.Icc 0 ℓ) :=
      (continuous_id'.prodMk continuous_const).continuousOn
    have hc : ContinuousOn (fun x => -((fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
        v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0))) -
        dissipationDensity R G v i x t) (Set.Icc 0 ℓ) :=
      hFcont.comp hcurve hmaps
    exact (hc.mono hsub).aestronglyMeasurable hmeas
  have hs_mem : Metric.ball t (ε / 2) ∈ nhds t := Metric.ball_mem_nhds t hδ
  have hF_meas : ∀ᶠ s in nhds t,
      MeasureTheory.AEStronglyMeasurable (fun x => energyDensity L C v i x s)
        (MeasureTheory.volume.restrict (Set.uIoc 0 ℓ)) :=
    Filter.eventually_of_mem hs_mem hF
  have hF_int : IntervalIntegrable (fun x => energyDensity L C v i x t)
      MeasureTheory.volume 0 ℓ := by
    have h := continuousOn_energySpaceSlice L C ℓ t U v i hU hv hi hmem_t
    rw [← Set.uIcc_of_le hℓ.le] at h
    exact h.intervalIntegrable
  have hsubI : Set.uIoc (0 : ℝ) ℓ ⊆ Set.Icc 0 ℓ := by
    rw [Set.uIoc_of_le hℓ.le]
    exact Set.Ioc_subset_Icc_self
  have hle : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc 0 ℓ →
      ∀ s ∈ Metric.ball t (ε / 2),
      ‖-((fderiv ℝ (Function.uncurry v) (x, s) (1, 0)) * i x s +
        v x s * (fderiv ℝ (Function.uncurry i) (x, s) (1, 0))) -
        dissipationDensity R G v i x s‖ ≤ M := by
    filter_upwards [Filter.Eventually.of_forall (fun x hx => hsubI hx)] with x hxIcc
    intro hx s hs
    exact hM (x, s) (Set.mk_mem_prod (hxIcc hx) (Metric.ball_subset_closedBall hs))
  have hbound : IntervalIntegrable (fun _ : ℝ => M) MeasureTheory.volume 0 ℓ :=
    continuous_const.intervalIntegrable 0 ℓ
  have hdiff : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc 0 ℓ →
      ∀ s ∈ Metric.ball t (ε / 2),
      HasDerivAt (fun s' => energyDensity L C v i x s')
        (-((fderiv ℝ (Function.uncurry v) (x, s) (1, 0)) * i x s +
          v x s * (fderiv ℝ (Function.uncurry i) (x, s) (1, 0))) -
          dissipationDensity R G v i x s) s := by
    filter_upwards [Filter.Eventually.of_forall (fun x hx => hsubI hx)] with x hxIcc
    intro hx s hs
    exact hasDerivAt_energySlice R L G C U v i hU hv hi htel x s (hmem_of s hs x (hxIcc hx))
  have hpar : HasDerivAt (fun s => ∫ x in (0 : ℝ)..ℓ, energyDensity L C v i x s)
      (∫ x in (0 : ℝ)..ℓ, -((fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
        v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0))) -
        dissipationDensity R G v i x t) t :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs_mem hF_meas hF_int hF' hle hbound hdiff).2
  have hGderiv : ∀ x ∈ Set.uIcc (0 : ℝ) ℓ, HasDerivAt (fun y => powerFlux v i y t)
      ((fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
        v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0))) x := by
    rw [Set.uIcc_of_le hℓ.le]
    intro x hx
    have hxt : (x, t) ∈ U := hmem_t x hx
    have hv_x := (differentiableAt_spaceSlice U v hU hv x t hxt).hasDerivAt
    have hi_x := (differentiableAt_spaceSlice U i hU hi x t hxt).hasDerivAt
    have h2 : HasDerivAt (fun y => powerFlux v i y t)
        (deriv (fun y => v y t) x * i x t + v x t * deriv (fun y => i y t) x) x :=
      hv_x.mul hi_x
    have hval : deriv (fun y => v y t) x * i x t + v x t * deriv (fun y => i y t) x
        = (fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
          v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0)) := by
      rw [sliceDeriv_eq_fderiv_space U v hU hv x t hxt,
        sliceDeriv_eq_fderiv_space U i hU hi x t hxt]
    rw [hval] at h2
    exact h2
  have hGcont : ContinuousOn (fun x => (fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
      v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0))) (Set.uIcc 0 ℓ) := by
    rw [Set.uIcc_of_le hℓ.le]
    have hvxS := continuousOn_fderivSpaceSlice U v ℓ t (1, 0) hU hv hmem_t
    have hixS := continuousOn_fderivSpaceSlice U i ℓ t (1, 0) hU hi hmem_t
    have hvS := continuousOn_spaceSlice_of_mem U v ℓ t hU hv hmem_t
    have hiS := continuousOn_spaceSlice_of_mem U i ℓ t hU hi hmem_t
    exact (hvxS.mul hiS).add (hvS.mul hixS)
  have hGint : IntervalIntegrable (fun x => (fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
      v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0))) MeasureTheory.volume 0 ℓ :=
    hGcont.intervalIntegrable
  have hFTCx : (∫ x in (0 : ℝ)..ℓ, (fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
      v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0)))
      = powerFlux v i ℓ t - powerFlux v i 0 t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hGderiv hGint
  have hdiss_int : IntervalIntegrable (fun x => dissipationDensity R G v i x t)
      MeasureTheory.volume 0 ℓ := by
    have h := continuousOn_dissSpaceSlice R G ℓ t U v i hU hv hi hmem_t
    rw [← Set.uIcc_of_le hℓ.le] at h
    exact h.intervalIntegrable
  have hval : (∫ x in (0 : ℝ)..ℓ, -((fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
      v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0))) - dissipationDensity R G v i x t)
      = powerFlux v i 0 t - powerFlux v i ℓ t -
        ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x t := by
    have e1 : (∫ x in (0 : ℝ)..ℓ, -((fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
        v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0))) - dissipationDensity R G v i x t)
        = (∫ x in (0 : ℝ)..ℓ, -((fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
          v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0)))) -
          (∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x t) :=
      intervalIntegral.integral_sub hGint.neg hdiss_int
    have e2 : (∫ x in (0 : ℝ)..ℓ, -((fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
        v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0))))
        = -(∫ x in (0 : ℝ)..ℓ, (fderiv ℝ (Function.uncurry v) (x, t) (1, 0)) * i x t +
          v x t * (fderiv ℝ (Function.uncurry i) (x, t) (1, 0))) :=
      intervalIntegral.integral_neg
    rw [e1, e2, hFTCx]
    ring
  rw [hval] at hpar
  exact hpar

/-- **Finite-line integrated energy balance** over the space-time rectangle
`[0, ℓ] × [t₀, t₁]`, with the inflow at `x = 0` and the outflow at `x = ℓ`. -/
lemma lineEnergy_sub_eq_integral_endpointFlux_sub_dissipation (R L G C ℓ t₀ t₁ : ℝ)
    (U : Set (ℝ × ℝ)) (v i : ℝ → ℝ → ℝ) (hU : IsOpen U)
    (hv : ContDiffOn ℝ 1 (Function.uncurry v) U) (hi : ContDiffOn ℝ 1 (Function.uncurry i) U)
    (htel : IsTelegrapherSolution R L G C U v i) (hℓ : 0 < ℓ) (ht : t₀ ≤ t₁)
    (hrect : Icc 0 ℓ ×ˢ Icc t₀ t₁ ⊆ U) :
    lineEnergy L C ℓ v i t₁ - lineEnergy L C ℓ v i t₀ =
      (∫ s in t₀..t₁, (powerFlux v i 0 s - powerFlux v i ℓ s)) -
        ∫ s in t₀..t₁, ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s := by
  have hD : ∀ s ∈ Set.uIcc t₀ t₁, HasDerivAt (fun s' => lineEnergy L C ℓ v i s')
      (powerFlux v i 0 s - powerFlux v i ℓ s -
        ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s) s := by
    rw [Set.uIcc_of_le ht]
    intro s hs
    exact hasDerivAt_lineEnergy R L G C ℓ s U v i hU hv hi htel hℓ
      (segment_subset_of_rect ℓ t₀ t₁ s U hs hrect)
  have hAcont : ContinuousOn (fun s => powerFlux v i 0 s - powerFlux v i ℓ s)
      (Set.Icc t₀ t₁) := by
    have h0mem : ∀ s ∈ Set.Icc t₀ t₁, (0, s) ∈ U := fun s hs =>
      hrect (Set.mk_mem_prod (Set.mem_Icc.mpr ⟨le_refl 0, hℓ.le⟩) hs)
    have hℓmem : ∀ s ∈ Set.Icc t₀ t₁, (ℓ, s) ∈ U := fun s hs =>
      hrect (Set.mk_mem_prod (Set.mem_Icc.mpr ⟨hℓ.le, le_refl ℓ⟩) hs)
    have hv0 := continuousOn_timeSlice_of_mem U v t₀ t₁ 0 hU hv h0mem
    have hi0 := continuousOn_timeSlice_of_mem U i t₀ t₁ 0 hU hi h0mem
    have hvℓ := continuousOn_timeSlice_of_mem U v t₀ t₁ ℓ hU hv hℓmem
    have hiℓ := continuousOn_timeSlice_of_mem U i t₀ t₁ ℓ hU hi hℓmem
    exact (hv0.mul hi0).sub (hvℓ.mul hiℓ)
  have hBcont : ContinuousOn (fun s => ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s)
      (Set.Icc t₀ t₁) :=
    continuousOn_dissIntegral R G ℓ t₀ t₁ U v i hU hv hi hℓ ht hrect
  have hDcont : ContinuousOn (fun s => powerFlux v i 0 s - powerFlux v i ℓ s -
      ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s) (Set.Icc t₀ t₁) :=
    hAcont.sub hBcont
  have hDint : IntervalIntegrable (fun s => powerFlux v i 0 s - powerFlux v i ℓ s -
      ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s) MeasureTheory.volume t₀ t₁ := by
    have h := hDcont
    rw [← Set.uIcc_of_le ht] at h
    exact h.intervalIntegrable
  have hAint : IntervalIntegrable (fun s => powerFlux v i 0 s - powerFlux v i ℓ s)
      MeasureTheory.volume t₀ t₁ := by
    have h := hAcont
    rw [← Set.uIcc_of_le ht] at h
    exact h.intervalIntegrable
  have hBint : IntervalIntegrable (fun s => ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s)
      MeasureTheory.volume t₀ t₁ := by
    have h := hBcont
    rw [← Set.uIcc_of_le ht] at h
    exact h.intervalIntegrable
  have hFTCt : (∫ s in t₀..t₁, (powerFlux v i 0 s - powerFlux v i ℓ s -
      ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s))
      = lineEnergy L C ℓ v i t₁ - lineEnergy L C ℓ v i t₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hD hDint
  have hsplit : (∫ s in t₀..t₁, (powerFlux v i 0 s - powerFlux v i ℓ s -
      ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s))
      = (∫ s in t₀..t₁, (powerFlux v i 0 s - powerFlux v i ℓ s)) -
        (∫ s in t₀..t₁, ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s) :=
    intervalIntegral.integral_sub hAint hBint
  exact hFTCt.symm.trans hsplit

/-! ### Dissipation signs -/

/-- `R, G ≥ 0` make the dissipation density nonnegative. -/
lemma dissipationDensity_nonneg (R G : ℝ) (v i : ℝ → ℝ → ℝ) (x t : ℝ) (hR : 0 ≤ R)
    (hG : 0 ≤ G) :
    0 ≤ dissipationDensity R G v i x t := by
  rw [show dissipationDensity R G v i x t = R * i x t ^ 2 + G * v x t ^ 2 from rfl]
  exact add_nonneg (mul_nonneg hR (sq_nonneg _)) (mul_nonneg hG (sq_nonneg _))

/-- For a passive line (`R, G ≥ 0`) the stored energy grows by at most the net endpoint
inflow. -/
lemma lineEnergy_sub_le_integral_endpointFlux (R L G C ℓ t₀ t₁ : ℝ) (U : Set (ℝ × ℝ))
    (v i : ℝ → ℝ → ℝ) (hU : IsOpen U) (hv : ContDiffOn ℝ 1 (Function.uncurry v) U)
    (hi : ContDiffOn ℝ 1 (Function.uncurry i) U) (htel : IsTelegrapherSolution R L G C U v i)
    (hR : 0 ≤ R) (hG : 0 ≤ G) (hℓ : 0 < ℓ) (ht : t₀ ≤ t₁)
    (hrect : Icc 0 ℓ ×ˢ Icc t₀ t₁ ⊆ U) :
    lineEnergy L C ℓ v i t₁ - lineEnergy L C ℓ v i t₀ ≤
      ∫ s in t₀..t₁, (powerFlux v i 0 s - powerFlux v i ℓ s) := by
  have hbal := lineEnergy_sub_eq_integral_endpointFlux_sub_dissipation R L G C ℓ t₀ t₁ U v i
    hU hv hi htel hℓ ht hrect
  have hnn : 0 ≤ ∫ s in t₀..t₁, ∫ x in (0 : ℝ)..ℓ, dissipationDensity R G v i x s :=
    intervalIntegral.integral_nonneg ht
      (fun s hs => intervalIntegral.integral_nonneg hℓ.le
        (fun x hx => dissipationDensity_nonneg R G v i x s hR hG))
  linarith [hbal, hnn]

/-- Lossy example: with no current, a uniform voltage `V e^{-(G/C) t}` solves the
telegrapher equations (shunt-conductance discharge). -/
lemma shuntDischarge_isTelegrapherSolution (R L G C V : ℝ) (hC : 0 < C) :
    IsTelegrapherSolution R L G C univ (fun _ t => V * Real.exp (-(G / C) * t))
      (fun _ _ => 0) := by
  intro x t _
  have hC' : C ≠ 0 := ne_of_gt hC
  have hlin : HasDerivAt (fun s : ℝ => -(G / C) * s) (-(G / C) * 1) t :=
    (hasDerivAt_id t).const_mul (-(G / C))
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(G / C) * s))
      (Real.exp (-(G / C) * t) * (-(G / C) * 1)) t :=
    hlin.exp
  have hV : HasDerivAt (fun s : ℝ => V * Real.exp (-(G / C) * s))
      (V * (Real.exp (-(G / C) * t) * (-(G / C) * 1))) t :=
    hexp.const_mul V
  have dV : deriv (fun s : ℝ => V * Real.exp (-(G / C) * s)) t
      = V * (Real.exp (-(G / C) * t) * (-(G / C) * 1)) :=
    hV.deriv
  have dV0 : deriv (fun y : ℝ => V * Real.exp (-(G / C) * t)) x = 0 :=
    deriv_const x _
  have dI0 : deriv (fun s : ℝ => (0 : ℝ)) t = 0 := deriv_const t _
  have dI0x : deriv (fun y : ℝ => (0 : ℝ)) x = 0 := deriv_const x _
  refine ⟨?_, ?_⟩
  · show deriv (fun y : ℝ => V * Real.exp (-(G / C) * t)) x
        = -R * (0 : ℝ) - L * deriv (fun s : ℝ => (0 : ℝ)) t
    rw [dV0, dI0]
    ring
  · show deriv (fun y : ℝ => (0 : ℝ)) x
        = -G * (V * Real.exp (-(G / C) * t)) -
          C * deriv (fun s : ℝ => V * Real.exp (-(G / C) * s)) t
    rw [dI0x, dV]
    field_simp [hC']
    ring

/-- In the shunt discharge with `G > 0` and `V ≠ 0` the stored line energy strictly
decreases. -/
lemma shuntDischarge_lineEnergy_strictAnti (L G C ℓ V : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hℓ : 0 < ℓ) (hV : V ≠ 0) :
    StrictAnti (fun t => lineEnergy L C ℓ (fun _ s => V * Real.exp (-(G / C) * s))
      (fun _ _ => 0) t) := by
  have ha : -(G / C) < 0 := neg_lt_zero.mpr (div_pos hG hC)
  have hV2 : 0 < V ^ 2 := by
    rw [pow_two]
    exact lt_of_le_of_ne (mul_self_nonneg V) (Ne.symm (mul_ne_zero hV hV))
  have hK : 0 < C * V ^ 2 / 2 := div_pos (mul_pos hC hV2) two_pos
  have hE : ∀ t : ℝ, lineEnergy L C ℓ (fun _ s => V * Real.exp (-(G / C) * s))
      (fun _ _ => 0) t = ℓ * (C * (V * Real.exp (-(G / C) * t)) ^ 2 / 2) := by
    intro t
    show (∫ x in (0 : ℝ)..ℓ, energyDensity L C (fun _ s => V * Real.exp (-(G / C) * s))
        (fun _ _ => 0) x t) = ℓ * (C * (V * Real.exp (-(G / C) * t)) ^ 2 / 2)
    have hconst : (fun x : ℝ => energyDensity L C (fun _ s => V * Real.exp (-(G / C) * s))
        (fun _ _ => 0) x t)
        = fun _ => C * (V * Real.exp (-(G / C) * t)) ^ 2 / 2 + L * 0 ^ 2 / 2 := by
      ext x
      rfl
    rw [hconst, intervalIntegral.integral_const, smul_eq_mul, sub_zero,
      show L * (0 : ℝ) ^ 2 / 2 = 0 by norm_num, add_zero]
  intro a b hab
  simp only [hE]
  apply mul_lt_mul_of_pos_left _ hℓ
  have hexp_lt : Real.exp (-(G / C) * b) < Real.exp (-(G / C) * a) := by
    rw [Real.exp_lt_exp]
    exact mul_lt_mul_of_neg_left hab ha
  have hexp2 : Real.exp (-(G / C) * b) ^ 2 < Real.exp (-(G / C) * a) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_lt_mul_self (le_of_lt (Real.exp_pos _)) hexp_lt
  have e1 : C * (V * Real.exp (-(G / C) * b)) ^ 2 / 2
      = (C * V ^ 2 / 2) * Real.exp (-(G / C) * b) ^ 2 := by
    ring
  have e2 : C * (V * Real.exp (-(G / C) * a)) ^ 2 / 2
      = (C * V ^ 2 / 2) * Real.exp (-(G / C) * a) ^ 2 := by
    ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left hexp2 hK

/-! ### Lossless traveling wave -/

/-- Forward wave voltage `f (x - t / √(L C))`. -/
noncomputable def travelingWaveVoltage (L C : ℝ) (f : ℝ → ℝ) (x t : ℝ) : ℝ :=
  f (x - t / Real.sqrt (L * C))

/-- Forward wave current `f (x - t / √(L C)) / √(L / C)`. -/
noncomputable def travelingWaveCurrent (L C : ℝ) (f : ℝ → ℝ) (x t : ℝ) : ℝ :=
  f (x - t / Real.sqrt (L * C)) / Real.sqrt (L / C)

/-- A C1 forward wave with speed `1/√(LC)` and impedance `√(L/C)` solves the lossless
(`R = G = 0`) telegrapher equations everywhere. -/
lemma travelingWave_isTelegrapherSolution (L C : ℝ) (f : ℝ → ℝ) (hL : 0 < L) (hC : 0 < C)
    (hf : ContDiff ℝ 1 f) :
    IsTelegrapherSolution 0 L 0 C univ (travelingWaveVoltage L C f)
      (travelingWaveCurrent L C f) := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hC' : C ≠ 0 := ne_of_gt hC
  have hS : 0 < Real.sqrt (L * C) := Real.sqrt_pos.mpr (mul_pos hL hC)
  have hS' : Real.sqrt (L * C) ≠ 0 := ne_of_gt hS
  have hZ : 0 < Real.sqrt (L / C) := Real.sqrt_pos.mpr (div_pos hL hC)
  have hZ' : Real.sqrt (L / C) ≠ 0 := ne_of_gt hZ
  have hCZ : C * Real.sqrt (L / C) ≠ 0 := mul_ne_zero hC' hZ'
  have hSZ : Real.sqrt (L * C) * Real.sqrt (L / C) = L := sqrt_mul_sqrt_eq L C hL hC
  have hsqrt : Real.sqrt (L * C) = C * Real.sqrt (L / C) := sqrt_mul_eq L C hL hC
  have hfD : Differentiable ℝ f := hf.differentiable one_ne_zero
  intro x t _
  have hf_at : ∀ u : ℝ, HasDerivAt f (deriv f u) u := fun u => (hfD u).hasDerivAt
  have hu_x : HasDerivAt (fun y : ℝ => y - t / Real.sqrt (L * C)) 1 x :=
    (hasDerivAt_id x).sub_const _
  have hu_t : HasDerivAt (fun s : ℝ => x - s / Real.sqrt (L * C))
      (0 - 1 / Real.sqrt (L * C)) t :=
    (hasDerivAt_const t x).sub ((hasDerivAt_id t).div_const _)
  have hVx : HasDerivAt (fun y : ℝ => f (y - t / Real.sqrt (L * C)))
      (deriv f (x - t / Real.sqrt (L * C)) * 1) x :=
    (hf_at (x - t / Real.sqrt (L * C))).comp x hu_x
  have hVt : HasDerivAt (fun s : ℝ => f (x - s / Real.sqrt (L * C)))
      (deriv f (x - t / Real.sqrt (L * C)) * (0 - 1 / Real.sqrt (L * C))) t :=
    (hf_at (x - t / Real.sqrt (L * C))).comp t hu_t
  have hIx : HasDerivAt (fun y : ℝ => f (y - t / Real.sqrt (L * C)) / Real.sqrt (L / C))
      (deriv f (x - t / Real.sqrt (L * C)) * 1 / Real.sqrt (L / C)) x :=
    hVx.div_const _
  have hIt : HasDerivAt (fun s : ℝ => f (x - s / Real.sqrt (L * C)) / Real.sqrt (L / C))
      (deriv f (x - t / Real.sqrt (L * C)) * (0 - 1 / Real.sqrt (L * C)) / Real.sqrt (L / C)) t :=
    hVt.div_const _
  refine ⟨?_, ?_⟩
  · show deriv (fun y : ℝ => f (y - t / Real.sqrt (L * C))) x
        = -0 * (f (x - t / Real.sqrt (L * C)) / Real.sqrt (L / C)) -
          L * deriv (fun s : ℝ => f (x - s / Real.sqrt (L * C)) / Real.sqrt (L / C)) t
    rw [hVx.deriv, hIt.deriv]
    simp only [neg_zero, zero_mul, zero_sub]
    set D := deriv f (x - t / Real.sqrt (L * C)) with hD
    field_simp [hS', hZ']
    linear_combination D * hSZ
  · show deriv (fun y : ℝ => f (y - t / Real.sqrt (L * C)) / Real.sqrt (L / C)) x
        = -0 * f (x - t / Real.sqrt (L * C)) -
          C * deriv (fun s : ℝ => f (x - s / Real.sqrt (L * C))) t
    rw [hIx.deriv, hVt.deriv, hsqrt]
    field_simp [hC', hZ', hCZ]
    ring

/-- For the forward wave, power flux = propagation speed × energy density. -/
lemma travelingWave_powerFlux_eq_speed_mul_energyDensity (L C : ℝ) (f : ℝ → ℝ)
    (hL : 0 < L) (hC : 0 < C) (x t : ℝ) :
    powerFlux (travelingWaveVoltage L C f) (travelingWaveCurrent L C f) x t =
      1 / Real.sqrt (L * C) *
        energyDensity L C (travelingWaveVoltage L C f) (travelingWaveCurrent L C f) x t := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hC' : C ≠ 0 := ne_of_gt hC
  have hZ : 0 < Real.sqrt (L / C) := Real.sqrt_pos.mpr (div_pos hL hC)
  have hZ' : Real.sqrt (L / C) ≠ 0 := ne_of_gt hZ
  have hCZ : C * Real.sqrt (L / C) ≠ 0 := mul_ne_zero hC' hZ'
  have hLC : L / C ≠ 0 := div_ne_zero hL' hC'
  have hsqrt : Real.sqrt (L * C) = C * Real.sqrt (L / C) := sqrt_mul_eq L C hL hC
  have heq : C * (f (x - t / Real.sqrt (L * C))) ^ 2 / 2
      = L * (f (x - t / Real.sqrt (L * C)) / Real.sqrt (L / C)) ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (le_of_lt (div_pos hL hC))]
    field_simp [hLC]
  show (f (x - t / Real.sqrt (L * C))) * (f (x - t / Real.sqrt (L * C)) / Real.sqrt (L / C))
      = 1 / Real.sqrt (L * C) *
        (C * (f (x - t / Real.sqrt (L * C))) ^ 2 / 2 +
          L * (f (x - t / Real.sqrt (L * C)) / Real.sqrt (L / C)) ^ 2 / 2)
  have hE : C * (f (x - t / Real.sqrt (L * C))) ^ 2 / 2 +
      L * (f (x - t / Real.sqrt (L * C)) / Real.sqrt (L / C)) ^ 2 / 2
      = C * (f (x - t / Real.sqrt (L * C))) ^ 2 := by
    linarith [heq]
  rw [hE, hsqrt]
  field_simp [hC', hZ', hCZ]

/-- For the forward wave, electric and magnetic energy densities are equal. -/
lemma travelingWave_electric_eq_magnetic (L C : ℝ) (f : ℝ → ℝ) (hL : 0 < L) (hC : 0 < C)
    (x t : ℝ) :
    C * travelingWaveVoltage L C f x t ^ 2 / 2 = L * travelingWaveCurrent L C f x t ^ 2 / 2 := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hC' : C ≠ 0 := ne_of_gt hC
  have hLC : L / C ≠ 0 := div_ne_zero hL' hC'
  show C * (f (x - t / Real.sqrt (L * C))) ^ 2 / 2
      = L * (f (x - t / Real.sqrt (L * C)) / Real.sqrt (L / C)) ^ 2 / 2
  rw [div_pow, Real.sq_sqrt (le_of_lt (div_pos hL hC))]
  field_simp [hLC]

/-! ### Swapped endpoint sign -/

/-- The ramp `v = i = x - t` solves the lossless line with `L = C = 1`. -/
lemma rampWave_isTelegrapherSolution :
    IsTelegrapherSolution 0 1 0 1 univ (fun x t => x - t) (fun x t => x - t) := by
  intro x t _
  have h1 : deriv (fun y : ℝ => y - t) x = 1 := by
    have h : HasDerivAt (fun y : ℝ => y - t) 1 x := (hasDerivAt_id x).sub_const t
    exact h.deriv
  have h2 : deriv (fun s : ℝ => x - s) t = -1 := by
    have h1' : HasDerivAt (fun _ : ℝ => x) 0 t := hasDerivAt_const t x
    have h2' : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h := h1'.sub h2'
    have h' : HasDerivAt (fun s : ℝ => x - s) (0 - 1) t := h
    rw [h'.deriv]
    norm_num
  refine ⟨?_, ?_⟩
  · show deriv (fun y : ℝ => y - t) x = -0 * (x - t) - 1 * deriv (fun s : ℝ => x - s) t
    rw [h1, h2]
    norm_num
  · show deriv (fun y : ℝ => y - t) x = -0 * (x - t) - 1 * deriv (fun s : ℝ => x - s) t
    rw [h1, h2]
    norm_num

/-- With the endpoint fluxes swapped (outflow at `x = 0`, inflow at `x = ℓ`), the balance
fails for the ramp on `[0, 1] × [0, 1/2]`: the true change is `-1/4`, the swapped
right-hand side is `+1/4`. -/
lemma swappedEndpointFlux_balance_fails :
    lineEnergy 1 1 1 (fun x t => x - t) (fun x t => x - t) (1 / 2) -
        lineEnergy 1 1 1 (fun x t => x - t) (fun x t => x - t) 0 ≠
      (∫ s in (0 : ℝ)..(1 / 2),
          (powerFlux (fun x t => x - t) (fun x t => x - t) 1 s -
            powerFlux (fun x t => x - t) (fun x t => x - t) 0 s)) -
        ∫ s in (0 : ℝ)..(1 / 2), ∫ x in (0 : ℝ)..1,
          dissipationDensity 0 0 (fun x t => x - t) (fun x t => x - t) x s := by
  have hint2 : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume a b :=
    fun a b => (continuous_pow 2).intervalIntegrable a b
  have hint1 : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume a b :=
    fun a b => continuous_id.intervalIntegrable a b
  have hintC : ∀ (c a b : ℝ), IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b :=
    fun c a b => continuous_const.intervalIntegrable a b
  have hEint : ∀ t : ℝ, (fun x : ℝ => energyDensity 1 1 (fun x t => x - t) (fun x t => x - t) x t)
      = fun x => (x - t) ^ 2 := by
    intro t
    ext x
    show 1 * (x - t) ^ 2 / 2 + 1 * (x - t) ^ 2 / 2 = (x - t) ^ 2
    ring
  have hEhalf : lineEnergy 1 1 1 (fun x t => x - t) (fun x t => x - t) (1 / 2) = 1 / 12 := by
    show (∫ x in (0 : ℝ)..1, energyDensity 1 1 (fun x t => x - t) (fun x t => x - t) x (1 / 2))
      = 1 / 12
    rw [hEint (1 / 2)]
    have hexp1 : (fun x : ℝ => (x - 1 / 2) ^ 2) = fun x => x ^ 2 - x + 1 / 4 := by
      ext x
      ring
    rw [hexp1]
    have hsub : IntervalIntegrable (fun x : ℝ => x ^ 2 - x) MeasureTheory.volume 0 1 :=
      (hint2 0 1).sub (hint1 0 1)
    simp only [intervalIntegral.integral_add hsub (hintC (1 / 4) 0 1),
      intervalIntegral.integral_sub (hint2 0 1) (hint1 0 1),
      integral_sq, integral_id, intervalIntegral.integral_const,
      smul_eq_mul, sub_zero]
    norm_num
  have hE0 : lineEnergy 1 1 1 (fun x t => x - t) (fun x t => x - t) 0 = 1 / 3 := by
    show (∫ x in (0 : ℝ)..1, energyDensity 1 1 (fun x t => x - t) (fun x t => x - t) x 0)
      = 1 / 3
    rw [hEint 0]
    have hexp0 : (fun x : ℝ => (x - 0) ^ 2) = fun x => x ^ 2 := by
      ext x
      ring
    rw [hexp0, integral_sq]
    norm_num
  have hflux : (∫ s in (0 : ℝ)..(1 / 2),
        (powerFlux (fun x t => x - t) (fun x t => x - t) 1 s -
          powerFlux (fun x t => x - t) (fun x t => x - t) 0 s)) = 1 / 4 := by
    have hexpF : (fun s : ℝ => powerFlux (fun x t => x - t) (fun x t => x - t) 1 s -
          powerFlux (fun x t => x - t) (fun x t => x - t) 0 s)
        = fun s => 1 - 2 * s := by
      ext s
      show (1 - s) * (1 - s) - (0 - s) * (0 - s) = 1 - 2 * s
      ring
    rw [hexpF]
    have e1 : (∫ s in (0 : ℝ)..(1 / 2), (1 - 2 * s))
        = (∫ s in (0 : ℝ)..(1 / 2), (1 : ℝ)) - (∫ s in (0 : ℝ)..(1 / 2), 2 * s) :=
      intervalIntegral.integral_sub (hintC 1 0 (1 / 2)) ((hint1 0 (1 / 2)).const_mul 2)
    have e2 : (∫ s in (0 : ℝ)..(1 / 2), (1 : ℝ)) = 1 / 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      norm_num
    have e3 : (∫ s in (0 : ℝ)..(1 / 2), 2 * s) = 1 / 4 := by
      have hcm : (∫ s in (0 : ℝ)..(1 / 2), 2 * s) = 2 * (∫ s in (0 : ℝ)..(1 / 2), s) :=
        intervalIntegral.integral_const_mul 2 _
      rw [hcm, integral_id]
      norm_num
    rw [e1, e2, e3]
    norm_num
  have hdiss0 : (∫ s in (0 : ℝ)..(1 / 2), ∫ x in (0 : ℝ)..1,
        dissipationDensity 0 0 (fun x t => x - t) (fun x t => x - t) x s) = 0 := by
    have hzero : ∀ s : ℝ, (∫ x in (0 : ℝ)..1,
        dissipationDensity 0 0 (fun x t => x - t) (fun x t => x - t) x s) = 0 := by
      intro s
      have hz : (fun x : ℝ => dissipationDensity 0 0 (fun x t => x - t) (fun x t => x - t) x s)
          = fun _ => (0 : ℝ) := by
        ext x
        show (0 : ℝ) * (x - s) ^ 2 + 0 * (x - s) ^ 2 = 0
        ring
      rw [hz, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      norm_num
    simp only [hzero]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    norm_num
  rw [hEhalf, hE0, hflux, hdiss0]
  norm_num

end PhyslibExt.Circuits.DistributedLineEnergy
