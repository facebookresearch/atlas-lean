/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Physlib.FluidDynamics.CauchyFlow.NavierStokes
public import PhyslibExt.FluidDynamics.LaminarFlowPorts
public import PhyslibExt.HeatTransfer.ConductionPorts
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parallel shear flow: reduction to the heat equation and the wall-work energy balance

For a parallel shear velocity `(U(t, y), 0, 0)` with a jointly `C²` profile, constant density
`ρ > 0` and viscosity `μ`, and no pressure gradient, Physlib's Navier-Stokes equations reduce to
`U_t = ν U_yy`, `ν = μ / ρ`. The kinetic energy per unit wall area then changes by the viscous
term, a dissipation for `μ ≥ 0`, plus the work of the wall shear stress. For `μ, L > 0` and a
nonzero wall speed, a single-mode transient driven by a moving wall gains kinetic energy for
`t ≥ 0` although it dissipates.

## i. Overview

A point `x : Space` has wall-normal coordinate `y = x 1`, and the walls are the planes `y = 0`
and `y = L`. The velocity `(U(t, y), 0, 0)` is a smooth representative on all of `Space` and time
(`U` jointly `C²`); the density `ρ > 0`, the shear viscosity `μ` and the second viscosity `lam`
are constants, the pressure `p(t)` is uniform in space, and there is no body force. The stress
is Physlib's Newtonian stress tensor of this velocity: normal entries `-p(t)` and shear entries
`μ U_y`. Through `FluidDynamics.navier_stokes_iff_convective_navier_stokes`, the flow satisfies
Physlib's Navier-Stokes equations exactly when `U_t = (μ / ρ) U_yy` everywhere. The steady
member `U = Uwall y / H` is the plane Couette field.

The kinetic energy per unit wall area is `K(t) = ∫₀ᴸ ρ U² / 2 dy`. For a Navier-Stokes shear flow
with `ρ > 0`, a jointly `C²` profile and `0 ≤ L`, applying the quadratic heat-energy identity with
explicit boundary work (`ConductionPorts.heatEnergy_hasDerivAt`) to the reduced equation gives
`K'(t) = -μ ∫₀ᴸ U_y² dy + μ (U U_y)(t, L) - μ (U U_y)(t, 0)`. The first term is the viscous
dissipation, nonpositive when `μ ≥ 0`; the boundary terms are the power `U σ_xy` delivered by the
wall shear stress `σ_xy = μ U_y`.

The single-mode transient `U = A y / L - (A / π) sin(π y / L) exp(-ν (π / L)² t)`,
`ν = μ / ρ`, is the plane Couette profile `A y / L` minus one decaying sine mode. It solves the
reduced equation at every time and height, and for `L ≠ 0` its wall velocities are `0` at `y = 0`
and `A` at `y = L` at every time. It is not a start from rest: for `L > 0` and `A ≠ 0` its
initial data `A y / L - (A / π) sin(π y / L)` is nonzero at every interior point `0 < y < L`
(`1/2 - 1/π` at `y = 1/2` when `A = L = 1`). For `ρ > 0` and `L > 0`, with
`s = exp(-ν (π / L)² t)`, its dissipation is `μ A² (1 + s² / 2) / L`, its wall work is
`μ A² (1 + s) / L`, and `K'(t) = μ A² s (2 - s) / (2 L)`; the dissipation is positive when also
`μ > 0` and `A ≠ 0`. For `ρ, μ, L > 0` and `A ≠ 0` the kinetic energy is positive at every
`t ≥ 0` and strictly increasing on `t ≥ 0` although energy is dissipated, and at each `t ≥ 0`
dropping the wall-work term would predict `K' < 0`, which is false for this flow. For `ν > 0` and
`L > 0` the sine mode decays as `t → ∞`, so the profile tends to the plane Couette profile; no
limit statement is proved here.

Existence for other data, uniqueness, stability and boundary-layer limits are not treated.

## ii. Key results

- `ShearReduction.shearFlow_stress`: the Newtonian stress of the shear flow.
- `ShearReduction.shearFlow_navierStokes_iff`: for `ρ > 0` and a jointly `C²` profile,
  Navier-Stokes holds exactly when `U_t = (μ / ρ) U_yy`.
- `ShearReduction.shearFlow_kineticEnergy_hasDerivAt`: the energy balance with wall work, for
  `ρ > 0`, a jointly `C²` profile and `0 ≤ L`.
- `ShearReduction.singleModeFlow_navierStokes`: for `ρ > 0` the single-mode transient with
  `ν = μ / ρ` is a Navier-Stokes solution.
- `ShearReduction.singleModeProfile_energy_balance`: dissipation, wall work and `K'`, for
  `ρ, L > 0`.
- `ShearReduction.singleModeProfile_energy_strictMonoOn`: for `ρ, μ, L > 0` and `A ≠ 0` the
  kinetic energy increases on `t ≥ 0`.
- `ShearReduction.singleModeProfile_no_wall_work`: for `ρ, μ, L > 0`, `A ≠ 0` and `t ≥ 0` the
  identity without wall work fails.

## iii. Table of contents

- A. Parallel shear flow
- B. Reduction to the heat equation
- C. Kinetic energy with wall work
- D. A single-mode transient with a moving wall

## iv. References

- F. M. White, *Viscous Fluid Flow*, 3rd ed., McGraw-Hill (2006), Chapter 3: unsteady parallel
  flows.
- R. B. Bird, W. E. Stewart and E. N. Lightfoot, *Transport Phenomena*, 2nd ed., Wiley (2002),
  Chapter 3: the mechanical energy balance.
- `ConductionPorts.heatEnergy_hasDerivAt` (`PhyslibExt.HeatTransfer.ConductionPorts`) and
  Physlib's `FluidDynamics.navier_stokes_iff_convective_navier_stokes`.
-/

@[expose] public section

namespace ShearReduction

open Space FluidDynamics

/-! ## A. Parallel shear flow -/

/-- Parallel shear velocity `(U(t, y), 0, 0)` with `y = x 1` the wall-normal coordinate. -/
noncomputable def shearVelocity (U : ℝ → ℝ → ℝ) : Time → Space → EuclideanSpace ℝ (Fin 3) :=
  fun t x => WithLp.toLp 2 ![U t.val (x 1), 0, 0]

/-- Density and velocity of the parallel shear flow with constant density `ρ`. -/
noncomputable def shearFluid (ρ : ℝ) (U : ℝ → ℝ → ℝ) : FluidFlow 3 where
  rho := fun _ _ => ρ
  velocity := shearVelocity U

/-- Parallel shear flow: constant density `ρ`, the velocity `(U(t, y), 0, 0)`, Physlib's
Newtonian stress for the spatially uniform pressure `p(t)`, shear viscosity `μ` and second
viscosity `lam`, and no body force. -/
noncomputable def shearFlow (ρ μ lam : ℝ) (p : Time → ℝ) (U : ℝ → ℝ → ℝ) : CauchyFlow 3 where
  toFluidFlow := shearFluid ρ U
  stress := FluidFlow.newtonianStressTensor 3 (shearFluid ρ U) (fun t _ => p t)
    (fun _ _ => μ) (fun _ _ => lam)
  specificBodyForce := fun _ _ => 0

/-- Kinetic energy per unit wall area of the shear layer `0 ≤ y ≤ L`,
`K(t) = ∫₀ᴸ ρ U(t, y)² / 2 dy`. For `L < 0` the interval integral is signed and is not the energy
of a layer. -/
noncomputable def shearKineticEnergy (ρ L : ℝ) (U : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..L, ρ * U t y ^ 2 / 2

/-- The steady member `U = Uwall y / H` of the shear family is the plane Couette velocity. -/
lemma shearVelocity_couette (Uwall H : ℝ) (t : Time) :
    shearVelocity (fun _ y => Uwall * y / H) t =
      FlowCoordinateBernoulli.couetteVelocity Uwall H := by
  rfl

/-- The coordinate map `x ↦ x i` has derivative `coordCLM i`. -/
private lemma hasFDerivAt_coord (i : Fin 3) (x : Space) :
    HasFDerivAt (fun x' : Space => x' i) (coordCLM i) x := by
  convert (coordCLM i).hasFDerivAt (x := x) using 1
  funext y
  simp [coordCLM_apply, coord_apply]

/-- Directional derivative of a function of one coordinate. -/
private lemma deriv_comp_coord {g : ℝ → ℝ} {g' : ℝ} (i j : Fin 3) {x : Space}
    (hg : HasDerivAt g g' (x i)) :
    ∂[j] (fun x' : Space => g (x' i)) x = if j = i then g' else 0 := by
  have h := hg.comp_hasFDerivAt x (hasFDerivAt_coord i x)
  rw [Space.deriv_eq, show (fun x' : Space => g (x' i)) = g ∘ (fun x' : Space => x' i) from rfl,
    h.fderiv]
  simp [coordCLM_apply, coord_apply, basis_apply]

private lemma contDiff_slice {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U)) (τ : ℝ) :
    ContDiff ℝ 2 (U τ) :=
  hU.comp (contDiff_const.prodMk contDiff_id)

private lemma contDiff_slice_time {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U))
    (y : ℝ) : ContDiff ℝ 2 (fun s => U s y) :=
  hU.comp (contDiff_id.prodMk contDiff_const)

private lemma hasDerivAt_slice {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U))
    (τ y : ℝ) : HasDerivAt (U τ) (deriv (U τ) y) y :=
  ((contDiff_slice hU τ).differentiable (by norm_num) y).hasDerivAt

private lemma hasDerivAt_slice_time {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U))
    (τ y : ℝ) : HasDerivAt (fun s => U s y) (deriv (fun s => U s y) τ) τ :=
  ((contDiff_slice_time hU y).differentiable (by norm_num) τ).hasDerivAt

private lemma hasDerivAt_deriv_slice {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U))
    (τ y : ℝ) : HasDerivAt (deriv (U τ)) (iteratedDeriv 2 (U τ) y) y := by
  have h := (contDiff_slice hU τ).differentiable_iteratedDeriv 1 (by norm_num) y
  rw [iteratedDeriv_one] at h
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact h.hasDerivAt

private lemma shearVelocity_differentiable {U : ℝ → ℝ → ℝ}
    (hU : ContDiff ℝ 2 (Function.uncurry U)) (t : Time) :
    Differentiable ℝ (shearVelocity U t) := by
  refine differentiable_euclidean.mpr fun i => ?_
  fin_cases i
  · exact ((contDiff_slice hU t.val).differentiable (by norm_num)).comp (eval_differentiable 1)
  · simp [shearVelocity]
  · simp [shearVelocity]

private lemma shearVelocity_differentiable_time {U : ℝ → ℝ → ℝ}
    (hU : ContDiff ℝ 2 (Function.uncurry U)) (x : Space) :
    Differentiable ℝ (fun s : Time => shearVelocity U s x) := by
  refine Time.differentiable_euclid fun i => ?_
  fin_cases i
  · exact ((contDiff_slice_time hU (x 1)).differentiable (by norm_num)).comp
      ((Time.val_contDiff (n := 1)).differentiable (by norm_num))
  · simp [shearVelocity]
  · simp [shearVelocity]

private lemma deriv_shearVelocity {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U))
    (t : Time) (x : Space) (i j : Fin 3) :
    ∂[j] (fun x' => shearVelocity U t x' i) x =
      if i = 0 ∧ j = 1 then deriv (U t.val) (x 1) else 0 := by
  fin_cases i
  · have h := deriv_comp_coord 1 j (hasDerivAt_slice hU t.val (x 1))
    simp only [Fin.zero_eta, Fin.isValue, true_and]
    rw [← h]
    rfl
  · simp [shearVelocity]
  · simp [shearVelocity]

private lemma div_shearVelocity {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U))
    (t : Time) (x : Space) : (∇ ⬝ shearVelocity U t) x = 0 := by
  unfold Space.div
  simp [Fin.sum_univ_three, deriv_shearVelocity hU]

private lemma div_smul_shearVelocity {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U))
    (ρ : ℝ) (t : Time) (x : Space) : (∇ ⬝ fun x' => ρ • shearVelocity U t x') x = 0 := by
  have hd0 := shearVelocity_differentiable hU t
  have hd : Differentiable ℝ (fun x' => ρ • shearVelocity U t x') := hd0.const_smul ρ
  have h : ∀ i, ∂[i] (fun x' => ρ • shearVelocity U t x') x = ρ • ∂[i] (shearVelocity U t) x := by
    intro i
    change fderiv ℝ (ρ • shearVelocity U t) x (basis i) = _
    rw [fderiv_const_smul (hd0 x), _root_.smul_apply, ← Space.deriv_eq]
  unfold Space.div
  simp only [deriv_euclid hd, h, Fin.sum_univ_three]
  simp [← deriv_euclid hd0, deriv_shearVelocity hU]

private lemma timeDeriv_shearVelocity {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U))
    (t : Time) (x : Space) :
    Time.deriv (fun s => shearVelocity U s x) t =
      WithLp.toLp 2 ![deriv (fun τ => U τ (x 1)) t.val, 0, 0] := by
  have hd := shearVelocity_differentiable_time hU x
  ext k
  rw [show (Time.deriv (fun s => shearVelocity U s x) t).ofLp k =
      Time.deriv (fun s => shearVelocity U s x k) t from (Time.deriv_euclid hd t).symm]
  fin_cases k
  · exact Time.deriv_eq_of_hasDerivAt (hasDerivAt_slice_time hU t.val (x 1))
  · simp [shearVelocity]
  · simp [shearVelocity]

/-- Differentiation under the integral sign for a jointly continuous time derivative. -/
private lemma integral_hasDerivAt' (F F' : ℝ → ℝ → ℝ) (a b t : ℝ)
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hderiv : ∀ s x, HasDerivAt (fun r => F r x) (F' s x) s) :
    HasDerivAt (fun s => ∫ x in a..b, F s x) (∫ x in a..b, F' t x) t := by
  have hcompact : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ Set.uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hF'.continuousOn
  have hc (s : ℝ) : Continuous (F s) := hF.comp (continuous_const.prodMk continuous_id)
  have hc' (s : ℝ) : Continuous (F' s) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (Filter.Eventually.of_forall fun s => (hc s).aestronglyMeasurable)
    ((hc t).intervalIntegrable a b) (hc' t).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun x hx s hs => hC (s, x) ⟨hs, Set.uIoc_subset_uIcc hx⟩)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C)
      MeasureTheory.volume a b)
    (MeasureTheory.ae_of_all _ fun x _ s _ => hderiv s x)).2
/-! ## B. Reduction to the heat equation -/

/-- For jointly `C²` profiles the Newtonian stress of the shear flow has normal entries `-p(t)`
and shear entries `μ U_y`; the second viscosity drops out. -/
lemma shearFlow_stress {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U))
    (ρ μ lam : ℝ) (p : Time → ℝ) (t : Time) (x : Space) :
    (shearFlow ρ μ lam p U).stress t x =
      !![-p t, μ * deriv (U t.val) (x 1), 0;
        μ * deriv (U t.val) (x 1), -p t, 0;
        0, 0, -p t] := by
  ext i j
  simp only [shearFlow, FluidFlow.newtonianStressTensor]
  have hdiv : (∇ ⬝ (shearFluid ρ U).velocity t) x = 0 := div_shearVelocity hU t x
  rw [hdiv]
  fin_cases i <;> fin_cases j <;>
    simp [FluidFlow.velocityGradient, shearFluid, deriv_shearVelocity hU, Matrix.transpose_apply]

/-- Reduction: for `ρ > 0` and a jointly `C²` profile `U`, the shear flow satisfies Physlib's
Navier-Stokes equations with the uniform pressure `p(t)`, shear viscosity `μ` and second
viscosity `lam` exactly when `U_t = (μ / ρ) U_yy` at every time and height. -/
lemma shearFlow_navierStokes_iff {ρ : ℝ} (hρ : 0 < ρ) (μ lam : ℝ) (p : Time → ℝ)
    {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U)) :
    NavierStokes 3 (shearFlow ρ μ lam p U) (fun t _ => p t) (fun _ _ => μ) (fun _ _ => lam) ↔
      ∀ τ y, deriv (fun s => U s y) τ = μ / ρ * iteratedDeriv 2 (U τ) y := by
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have h1 : ∀ t x, DifferentiableAt ℝ ((shearFlow ρ μ lam p U).rho · x) t :=
    fun t x => differentiableAt_const ρ
  have h2 : ∀ t x, DifferentiableAt ℝ ((shearFlow ρ μ lam p U).velocity · x) t :=
    fun t x => shearVelocity_differentiable_time hU x t
  have h3 : ∀ t, Differentiable ℝ
      (FluidFlow.momentumDensity 3 (shearFlow ρ μ lam p U).toFluidFlow t) :=
    fun t => (shearVelocity_differentiable hU t).const_smul ρ
  have h4 : ∀ t, Differentiable ℝ ((shearFlow ρ μ lam p U).velocity t) :=
    fun t => shearVelocity_differentiable hU t
  rw [navier_stokes_iff_convective_navier_stokes 3 _ _ _ _ h1 h2 h3 h4]
  have hcont : FluidFlow.ClassicalContinuityEquation 3 (shearFlow ρ μ lam p U).toFluidFlow := by
    refine FluidFlow.classicalContinuityEquation_of_smoothContinuityEquation 3 _
      ⟨fun x => differentiable_const ρ, fun t => (shearVelocity_differentiable hU t).const_smul ρ,
        fun t x => ?_⟩
    simp only [FluidFlow.continuityResidual, shearFlow, shearFluid]
    rw [Time.deriv_const, zero_add]
    exact div_smul_shearVelocity hU ρ t x
  have hmom : ∀ t x,
      ((shearFlow ρ μ lam p U).rho t x •
          FluidFlow.materialAcceleration 3 (shearFlow ρ μ lam p U).toFluidFlow t x =
        matrixDiv 3 ((shearFlow ρ μ lam p U).stress t) x +
          (shearFlow ρ μ lam p U).rho t x • (shearFlow ρ μ lam p U).specificBodyForce t x) ↔
        ρ * deriv (fun τ => U τ (x 1)) t.val = μ * iteratedDeriv 2 (U t.val) (x 1) := by
    intro t x
    have hσ : (shearFlow ρ μ lam p U).stress t = fun y : Space =>
        !![-p t, μ * deriv (U t.val) (y 1), 0; μ * deriv (U t.val) (y 1), -p t, 0; 0, 0, -p t] :=
      funext fun y => shearFlow_stress hU ρ μ lam p t y
    have d1 : ∀ j, ∂[j] (fun y : Space => μ * deriv (U t.val) (y 1)) x =
        if j = 1 then μ * iteratedDeriv 2 (U t.val) (x 1) else 0 := fun j =>
      deriv_comp_coord (g := fun r => μ * deriv (U t.val) r) 1 j
        ((hasDerivAt_deriv_slice hU t.val (x 1)).const_mul μ)
    have hd := shearVelocity_differentiable hU t
    have hD0 : Space.deriv 0 (shearVelocity U t) x = 0 := by
      ext k
      rw [show (Space.deriv 0 (shearVelocity U t) x).ofLp k =
          Space.deriv 0 (fun x' => shearVelocity U t x' k) x from (deriv_euclid hd x).symm,
        deriv_shearVelocity hU]
      simp
    have hL : (shearFlow ρ μ lam p U).rho t x •
        FluidFlow.materialAcceleration 3 (shearFlow ρ μ lam p U).toFluidFlow t x =
          WithLp.toLp 2 ![ρ * deriv (fun τ => U τ (x 1)) t.val, 0, 0] := by
      simp only [FluidFlow.materialAcceleration, FluidFlow.convectiveTerm, shearFlow, shearFluid,
        Fin.sum_univ_three, hD0, timeDeriv_shearVelocity hU]
      ext k
      fin_cases k <;> simp [shearVelocity]
    have hR : matrixDiv 3 ((shearFlow ρ μ lam p U).stress t) x +
        (shearFlow ρ μ lam p U).rho t x • (shearFlow ρ μ lam p U).specificBodyForce t x =
          WithLp.toLp 2 ![μ * iteratedDeriv 2 (U t.val) (x 1), 0, 0] := by
      rw [hσ]
      ext k
      fin_cases k <;> simp [matrixDiv_apply, Fin.sum_univ_three, d1, shearFlow]
    rw [hL, hR]
    constructor
    · intro h
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
      simpa using this
    · intro h
      rw [h]
  constructor
  · rintro ⟨_, hm, _⟩ τ y
    have h := (hmom ⟨τ⟩ ⟨![0, y, 0]⟩).mp (hm ⟨τ⟩ ⟨![0, y, 0]⟩)
    have hy : (⟨![0, y, 0]⟩ : Space) 1 = y := rfl
    rw [hy] at h
    field_simp
    linarith
  · intro hheat
    refine ⟨hcont, fun t x => (hmom t x).mpr ?_, fun t x => rfl⟩
    rw [hheat]
    field_simp

/-! ## C. Kinetic energy with wall work -/

/-- Kinetic-energy balance with wall work: for a Navier-Stokes shear flow with `ρ > 0`, a
jointly `C²` profile and `0 ≤ L`, the kinetic energy per unit wall area has derivative
`-μ ∫₀ᴸ U_y² dy + μ (U U_y)(t, L) - μ (U U_y)(t, 0)`. The boundary terms are the wall velocity
times the wall shear stress `μ U_y` at each wall; they are retained, not discarded. -/
lemma shearFlow_kineticEnergy_hasDerivAt {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L) (μ lam : ℝ)
    (p : Time → ℝ) {U : ℝ → ℝ → ℝ} (hU : ContDiff ℝ 2 (Function.uncurry U))
    (hNS : NavierStokes 3 (shearFlow ρ μ lam p U) (fun t _ => p t) (fun _ _ => μ)
      (fun _ _ => lam)) (t : ℝ) :
    HasDerivAt (shearKineticEnergy ρ L U)
      (-μ * (∫ y in (0 : ℝ)..L, deriv (U t) y ^ 2) +
        μ * (U t L * deriv (U t) L - U t 0 * deriv (U t) 0)) t := by
  have hheat := (shearFlow_navierStokes_iff hρ μ lam p hU).mp hNS
  have hU1 : ContDiff ℝ 1 (Function.uncurry U) := hU.of_le (by norm_num)
  have hut0 : ∀ τ y, HasDerivAt (fun s => U s y)
      (fderiv ℝ (Function.uncurry U) (τ, y) (1, 0)) τ := by
    intro τ y
    have h := (hU1.differentiable (by norm_num) (τ, y)).hasFDerivAt
    simpa [Function.comp_def] using
      h.comp_hasDerivAt τ ((hasDerivAt_id τ).prodMk (hasDerivAt_const τ y))
  have hutc : Continuous fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry U) q (1, 0) :=
    (hU1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hE : HasDerivAt (fun τ => ∫ y in (0 : ℝ)..L, U τ y ^ 2 / 2)
      (∫ y in (0 : ℝ)..L, U t y * deriv (fun s => U s y) t) t := by
    have hc := hU.continuous
    have hcF : Continuous (Function.uncurry fun τ y => U τ y ^ 2 / 2) := by
      simp only [Function.uncurry_def] at hc ⊢
      fun_prop
    have hcF' : Continuous (Function.uncurry fun τ y =>
        U τ y * fderiv ℝ (Function.uncurry U) (τ, y) (1, 0)) := by
      simp only [Function.uncurry_def] at hc ⊢
      exact hc.mul hutc
    have h := integral_hasDerivAt' (fun τ y => U τ y ^ 2 / 2)
      (fun τ y => U τ y * fderiv ℝ (Function.uncurry U) (τ, y) (1, 0)) 0 L t hcF hcF'
      (fun s y => ((hut0 s y).pow 2).div_const 2 |>.congr_deriv (by push_cast; ring))
    convert h using 2
    funext y
    rw [(hut0 t y).deriv]
  have hint : IntervalIntegrable (fun y => U t y * deriv (fun s => U s y) t)
      MeasureTheory.volume 0 L := by
    have : (fun y => U t y * deriv (fun s => U s y) t) =
        fun y => U t y * fderiv ℝ (Function.uncurry U) (t, y) (1, 0) := by
      funext y
      rw [(hut0 t y).deriv]
    rw [this]
    exact ((contDiff_slice hU t).continuous.mul
      (hutc.comp (continuous_const.prodMk continuous_id))).intervalIntegrable 0 L
  have hcux : Continuous (deriv (U t)) := (contDiff_slice hU t).continuous_deriv (by norm_num)
  have hcuxx : Continuous (iteratedDeriv 2 (U t)) :=
    (contDiff_slice hU t).continuous_iteratedDeriv 2 le_rfl
  have hI := ConductionPorts.heatEnergy_hasDerivAt (D := μ / ρ) (src := fun _ _ => 0) hL
    (u := U) (ut := fun τ y => deriv (fun s => U s y) τ) (ux := fun τ y => deriv (U τ) y)
    (uxx := fun τ y => iteratedDeriv 2 (U τ) y) (t := t)
    (fun y _ => hasDerivAt_slice_time hU t y) (fun y _ => hasDerivAt_slice hU t y)
    (fun y _ => hasDerivAt_deriv_slice hU t y) (fun y _ => by rw [hheat t y, add_zero])
    (contDiff_slice hU t).continuous.continuousOn hcux.continuousOn hcuxx.continuousOn hE hint
  have hK : shearKineticEnergy ρ L U = fun τ => ρ * ∫ y in (0 : ℝ)..L, U τ y ^ 2 / 2 := by
    funext τ
    unfold shearKineticEnergy
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext y
    ring
  rw [hK]
  convert hI.const_mul ρ using 1
  simp only [mul_zero, intervalIntegral.integral_zero, add_zero]
  field_simp

/-! ## D. A single-mode transient with a moving wall -/

/-- Single-mode transient between a wall at rest at `y = 0` and a wall moving with velocity `A`
at `y = L` (for `L ≠ 0`, `singleModeProfile_walls`):
`U(t, y) = A y / L - (A / π) sin(π y / L) exp(-ν (π / L)² t)`, the plane Couette profile minus one
decaying sine mode. It is not a start from rest: for `L > 0` and `A ≠ 0` the initial data
`A y / L - (A / π) sin(π y / L)` is nonzero at every interior point `0 < y < L`, and the wall
`y = L` moves at every time. -/
noncomputable def singleModeProfile (A L ν t y : ℝ) : ℝ :=
  A * y / L - A / Real.pi * Real.sin (Real.pi * y / L) * Real.exp (-ν * (Real.pi / L) ^ 2 * t)

/-- Phase derivative used by the single-mode profile. -/
private lemma hasDerivAt_phase (L y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.pi * y / L) (Real.pi / L) y :=
  (((hasDerivAt_id y).const_mul Real.pi).div_const L).congr_deriv (by simp)

private lemma hasDerivAt_singleModeProfile_space (A L ν t y : ℝ) :
    HasDerivAt (singleModeProfile A L ν t)
      (A / L - A / L * Real.exp (-ν * (Real.pi / L) ^ 2 * t) * Real.cos (Real.pi * y / L)) y := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : HasDerivAt (fun y : ℝ => A * y / L) (A / L) y :=
    (((hasDerivAt_id y).const_mul A).div_const L).congr_deriv (by simp)
  have h2 := (((Real.hasDerivAt_sin _).comp y (hasDerivAt_phase L y)).const_mul
    (A / Real.pi)).mul_const (Real.exp (-ν * (Real.pi / L) ^ 2 * t))
  exact (h1.sub h2).congr_deriv (by field_simp)

private lemma deriv_singleModeProfile_space (A L ν t : ℝ) :
    deriv (singleModeProfile A L ν t) = fun y =>
      A / L - A / L * Real.exp (-ν * (Real.pi / L) ^ 2 * t) * Real.cos (Real.pi * y / L) :=
  funext fun y => (hasDerivAt_singleModeProfile_space A L ν t y).deriv
/-- The single-mode profile is jointly `C²`. -/
lemma singleModeProfile_contDiff (A L ν : ℝ) :
    ContDiff ℝ 2 (Function.uncurry (singleModeProfile A L ν)) := by
  have h : Function.uncurry (singleModeProfile A L ν) = fun q : ℝ × ℝ =>
      A * q.2 / L - A / Real.pi * Real.sin (Real.pi * q.2 / L) *
        Real.exp (-ν * (Real.pi / L) ^ 2 * q.1) := by
    funext q
    rfl
  rw [h]
  fun_prop

/-- The single-mode profile solves `U_t = ν U_yy` at every time and height; its derivatives are
computed from the explicit formula. -/
lemma singleModeProfile_heat (A L ν t y : ℝ) :
    deriv (fun s => singleModeProfile A L ν s y) t =
      ν * iteratedDeriv 2 (singleModeProfile A L ν t) y := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have ht : HasDerivAt (fun s => singleModeProfile A L ν s y)
      (-(A / Real.pi * Real.sin (Real.pi * y / L)) *
        (Real.exp (-ν * (Real.pi / L) ^ 2 * t) * (-ν * (Real.pi / L) ^ 2))) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (-ν * (Real.pi / L) ^ 2 * s))
        (Real.exp (-ν * (Real.pi / L) ^ 2 * t) * (-ν * (Real.pi / L) ^ 2)) t :=
      (((hasDerivAt_id t).const_mul (-ν * (Real.pi / L) ^ 2)).exp).congr_deriv (by simp)
    exact ((he.const_mul (A / Real.pi * Real.sin (Real.pi * y / L))).const_sub
      (A * y / L)).congr_deriv (by ring)
  have hxx : HasDerivAt (deriv (singleModeProfile A L ν t))
      (A / L * Real.exp (-ν * (Real.pi / L) ^ 2 * t) * Real.sin (Real.pi * y / L) *
        (Real.pi / L)) y := by
    rw [deriv_singleModeProfile_space]
    exact ((((Real.hasDerivAt_cos _).comp y (hasDerivAt_phase L y)).const_mul
      (A / L * Real.exp (-ν * (Real.pi / L) ^ 2 * t))).const_sub (A / L)).congr_deriv
        (by ring)
  rw [ht.deriv, iteratedDeriv_succ, iteratedDeriv_one, hxx.deriv]
  field_simp

/-- For `L ≠ 0` the single-mode profile is at rest on the wall `y = 0` and moves with velocity `A`
on the wall `y = L`. -/
lemma singleModeProfile_walls {L : ℝ} (hL : L ≠ 0) (A ν t : ℝ) :
    singleModeProfile A L ν t 0 = 0 ∧ singleModeProfile A L ν t L = A := by
  refine ⟨?_, ?_⟩
  · simp [singleModeProfile]
  · simp only [singleModeProfile]
    rw [show Real.pi * L / L = Real.pi by field_simp, Real.sin_pi]
    field_simp
    ring

/-- With `ν = μ / ρ` and `ρ > 0` the single-mode flow satisfies Physlib's Navier-Stokes
equations. -/
lemma singleModeFlow_navierStokes {ρ : ℝ} (hρ : 0 < ρ) (A L μ lam : ℝ) (p : Time → ℝ) :
    NavierStokes 3 (shearFlow ρ μ lam p (singleModeProfile A L (μ / ρ))) (fun t _ => p t)
      (fun _ _ => μ) (fun _ _ => lam) := by
  refine (shearFlow_navierStokes_iff hρ μ lam p (singleModeProfile_contDiff A L (μ / ρ))).mpr ?_
  intro τ y
  exact singleModeProfile_heat A L (μ / ρ) τ y

/-- Energy balance of the single-mode flow for `ρ, L > 0`, with `ν = μ / ρ` and
`s = exp(-ν (π / L)² t)`: the dissipation is `μ A² (1 + s² / 2) / L`, the work of the moving wall
is `μ A² (1 + s) / L`, and the kinetic energy has derivative `μ A² s (2 - s) / (2 L)`. -/
lemma singleModeProfile_energy_balance {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 < L) (A μ t : ℝ) :
    μ * (∫ y in (0 : ℝ)..L, deriv (singleModeProfile A L (μ / ρ) t) y ^ 2) =
        μ * A ^ 2 * (1 + Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) ^ 2 / 2) / L ∧
      μ * deriv (singleModeProfile A L (μ / ρ) t) L * A =
        μ * A ^ 2 * (1 + Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t)) / L ∧
      HasDerivAt (shearKineticEnergy ρ L (singleModeProfile A L (μ / ρ)))
        (μ * A ^ 2 * Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) *
          (2 - Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t)) / (2 * L)) t := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hL0 : L ≠ 0 := hL.ne'
  set s := Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) with hs
  have hdx := deriv_singleModeProfile_space A L (μ / ρ) t
  rw [← hs] at hdx
  have hdiss : (∫ y in (0 : ℝ)..L, deriv (singleModeProfile A L (μ / ρ) t) y ^ 2) =
      A ^ 2 * (1 + s ^ 2 / 2) / L := by
    rw [hdx]
    have hF : ∀ y ∈ Set.uIcc (0 : ℝ) L, HasDerivAt
        (fun y => (A / L) ^ 2 * (y - 2 * s * (L / Real.pi) * Real.sin (Real.pi * y / L) +
          s ^ 2 * (y / 2 + L / (4 * Real.pi) * Real.sin (2 * (Real.pi * y / L)))))
        ((A / L - A / L * s * Real.cos (Real.pi * y / L)) ^ 2) y := by
      intro y _
      have hph := hasDerivAt_phase L y
      have h2 : HasDerivAt (fun y : ℝ => 2 * (Real.pi * y / L)) (2 * (Real.pi / L)) y :=
        hph.const_mul 2
      have hs1 := ((Real.hasDerivAt_sin _).comp y hph).const_mul (2 * s * (L / Real.pi))
      have hs2 := ((Real.hasDerivAt_sin _).comp y h2).const_mul (L / (4 * Real.pi))
      have hlin : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) y := (hasDerivAt_id y).div_const 2
      have htot := (((hasDerivAt_id y).sub hs1).add ((hlin.add hs2).const_mul (s ^ 2))).const_mul
        ((A / L) ^ 2)
      refine htot.congr_deriv ?_
      rw [Real.cos_two_mul]
      field_simp
      ring
    have hint : IntervalIntegrable (fun y => (A / L - A / L * s * Real.cos (Real.pi * y / L)) ^ 2)
        MeasureTheory.volume 0 L := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
    rw [show Real.pi * L / L = Real.pi by field_simp, show 2 * Real.pi = 2 * Real.pi from rfl]
    simp only [mul_zero, zero_div, Real.sin_zero, Real.sin_pi, Real.sin_two_pi]
    field_simp
    ring
  have hwall : deriv (singleModeProfile A L (μ / ρ) t) L = A * (1 + s) / L := by
    rw [hdx]
    simp only
    rw [show Real.pi * L / L = Real.pi by field_simp, Real.cos_pi]
    field_simp
    ring
  have hwalls := singleModeProfile_walls hL0 A (μ / ρ) t
  have hK := shearFlow_kineticEnergy_hasDerivAt hρ hL.le μ 0 (fun _ => 0)
    (singleModeProfile_contDiff A L (μ / ρ)) (singleModeFlow_navierStokes hρ A L μ 0 (fun _ => 0)) t
  refine ⟨by rw [hdiss]; ring, by rw [hwall]; ring, ?_⟩
  refine hK.congr_deriv ?_
  rw [hdiss, hwalls.1, hwalls.2, hwall]
  field_simp
  ring

/-- Nonzero kinetic energy: for `ρ, μ, L > 0`, `A ≠ 0` and `t ≥ 0` the single-mode flow has
positive kinetic energy. -/
lemma singleModeProfile_energy_pos {ρ μ L A t : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (hL : 0 < L)
    (hA : A ≠ 0) (ht : 0 ≤ t) :
    0 < shearKineticEnergy ρ L (singleModeProfile A L (μ / ρ)) t := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hν : 0 ≤ μ / ρ := (div_pos hμ hρ).le
  have hs1 : Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ μ / ρ * (Real.pi / L) ^ 2 * t := by positivity
    linarith
  have hs0 := Real.exp_pos (-(μ / ρ) * (Real.pi / L) ^ 2 * t)
  unfold shearKineticEnergy
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hL
  · apply Continuous.intervalIntegrable
    have := (singleModeProfile_contDiff A L (μ / ρ)).continuous
    have hc : Continuous (singleModeProfile A L (μ / ρ) t) :=
      this.comp (continuous_const.prodMk continuous_id)
    fun_prop
  · intro y hy
    have hz0 : 0 < Real.pi * y / L := by have := hy.1; positivity
    have hzπ : Real.pi * y / L < Real.pi := by
      rw [div_lt_iff₀ hL]
      nlinarith [hy.2]
    have hsin : 0 < Real.sin (Real.pi * y / L) := Real.sin_pos_of_pos_of_lt_pi hz0 hzπ
    have hlt := Real.sin_lt hz0
    have hU : singleModeProfile A L (μ / ρ) t y = A / Real.pi * (Real.pi * y / L -
        Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) * Real.sin (Real.pi * y / L)) := by
      unfold singleModeProfile
      field_simp
    have hpos : 0 < Real.pi * y / L -
        Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) * Real.sin (Real.pi * y / L) := by
      nlinarith
    have hne : singleModeProfile A L (μ / ρ) t y ≠ 0 := by
      rw [hU]
      exact mul_ne_zero (div_ne_zero hA hπ.ne') hpos.ne'
    have := pow_pos (abs_pos.mpr hne) 2
    rw [sq_abs] at this
    positivity

/-- Increasing kinetic energy despite viscous dissipation: for `ρ, μ, L > 0` and `A ≠ 0` the
kinetic energy of the single-mode flow is strictly increasing on `t ≥ 0`. -/
lemma singleModeProfile_energy_strictMonoOn {ρ μ L A : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (hL : 0 < L)
    (hA : A ≠ 0) :
    StrictMonoOn (shearKineticEnergy ρ L (singleModeProfile A L (μ / ρ))) (Set.Ici 0) := by
  have hd : ∀ t, HasDerivAt (shearKineticEnergy ρ L (singleModeProfile A L (μ / ρ)))
      (μ * A ^ 2 * Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) *
        (2 - Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t)) / (2 * L)) t :=
    fun t => (singleModeProfile_energy_balance hρ hL A μ t).2.2
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact fun t _ => (hd t).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    rw [(hd t).deriv]
    have hν : 0 < μ / ρ := div_pos hμ hρ
    have hs1 : Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) < 1 := by
      have : 0 < μ / ρ * (Real.pi / L) ^ 2 * t := by
        have := Real.pi_pos
        positivity
      calc Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) < Real.exp 0 :=
            Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    have hs0 := Real.exp_pos (-(μ / ρ) * (Real.pi / L) ^ 2 * t)
    have h2 : 0 < 2 - Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) := by linarith
    have hA2 : 0 < A ^ 2 := by positivity
    positivity

/-- Dropping the moving-wall term falsely predicts decay: for `ρ, μ, L > 0`, `A ≠ 0` and
`t ≥ 0` the kinetic energy of the single-mode flow does not have the derivative
`-μ ∫₀ᴸ U_y² dy`, which is negative. -/
lemma singleModeProfile_no_wall_work {ρ μ L A t : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (hL : 0 < L)
    (hA : A ≠ 0) (ht : 0 ≤ t) :
    ¬ HasDerivAt (shearKineticEnergy ρ L (singleModeProfile A L (μ / ρ)))
      (-μ * ∫ y in (0 : ℝ)..L, deriv (singleModeProfile A L (μ / ρ) t) y ^ 2) t := by
  intro h
  obtain ⟨hdiss, -, hK⟩ := singleModeProfile_energy_balance hρ hL A μ t
  have heq := h.unique hK
  have hs0 := Real.exp_pos (-(μ / ρ) * (Real.pi / L) ^ 2 * t)
  have hs1 : Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ μ / ρ * (Real.pi / L) ^ 2 * t := by
      have := Real.pi_pos
      have := div_pos hμ hρ
      positivity
    linarith
  have hA2 : 0 < A ^ 2 := by positivity
  have hpos : 0 < μ * A ^ 2 * Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) *
      (2 - Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t)) / (2 * L) := by
    have h2 : 0 < 2 - Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) := by linarith
    positivity
  have hneg : -μ * (∫ y in (0 : ℝ)..L, deriv (singleModeProfile A L (μ / ρ) t) y ^ 2) < 0 := by
    rw [neg_mul, hdiss]
    have : 0 < μ * A ^ 2 * (1 + Real.exp (-(μ / ρ) * (Real.pi / L) ^ 2 * t) ^ 2 / 2) / L := by
      positivity
    linarith
  linarith

end ShearReduction
