/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Physlib.SpaceAndTime.Space.Derivatives.Grad
public import Physlib.FluidDynamics.Euler.Basic
public import Physlib.FluidDynamics.CauchyFlow.BodyForce
public import Physlib.FluidDynamics.ThermodynamicCauchyFlow.Bernoulli
public import Physlib.FluidDynamics.CauchyFlow.NavierStokes
public import Physlib.FluidDynamics.FluidFlow.Incompressible
public import PhyslibExt.EarthScience.BernoulliStreamline
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Flow coordinates for Bernoulli's theorem and plane Couette and Poiseuille flow

Physlib's derivatives, Euler equations and Bernoulli function, read in affine coordinates about an
arbitrary origin, discharge the hypotheses of the coordinate streamline Bernoulli theorem. Plane
Couette flow, with its Newtonian stress, satisfies Physlib's incompressibility, continuity and
Navier-Stokes predicates, and so does plane Poiseuille flow, which carries the flow rate
`G H³ / (12 μ)` per unit width.

## i. Overview

A point `o : Space` is fixed as origin. The affine coordinate identification is the torsor action
`v ↦ v +ᵥ o : EuclideanSpace ℝ (Fin 3) → Space` with inverse `p ↦ p -ᵥ o`. Physlib's own `∇`,
`Space.deriv`, Euler predicate and Bernoulli function are used as they are; this file adds no
instance and no new space or rotation type. Physlib's spatial derivatives are defined through the
normed-space instance Physlib registers on `Space d` (`Physlib.SpaceAndTime.Space.Module`), and
the proofs use that registered module structure (including its addition on `Space`) exactly where
Physlib's own derivative definitions do; no statement writes addition of points, and nothing here
asserts that the point carrier is a vector space beyond Physlib's existing instance.

Part A transports derivatives, gradients and integral curves through the chart. Part B discharges
the projected Euler premise of `EarthScience.bernoulli_along_streamline` from Physlib's `Euler`
predicate for a steady constant-density inviscid flow with a body-force potential, then
specializes the streamline theorem to `Space` and to Physlib's enthalpy Bernoulli function under
an explicit `h = p / ρ + e₀` hypothesis. Part C is a nonzero rotating fixture with gravity in both
representations, and an invalid example where a polytropic enthalpy is not of the form
`p / ρ + e₀`.

Parts D-G treat plane Couette flow in the channel `0 ≤ y ≤ H`, `H > 0`, where `y = x 1` is the
second coordinate of a point `x : Space`. The lower wall `y = 0` is at rest and the upper wall
`y = H` moves with speed `Uwall` along the first axis. The velocity `u = (Uwall y / H, 0, 0)` is
defined on all of `Space` as a smooth representative and restricts to the channel. The density
`ρ`, the pressure `p₀`, the shear viscosity `μ` and the second viscosity `lam` are constants, and
there is no body force. The stress is Physlib's Newtonian stress tensor
`-p I + μ (∇u + ∇uᵀ) + lam (div u) I` of this velocity; it is the constant matrix with normal
entries `-p₀` and shear entries `μ Uwall / H`. The flow satisfies Physlib's smooth continuity and
smooth incompressibility predicates, whose differentiability clauses are proved, not assumed; the
four differentiability premises of `FluidDynamics.navier_stokes_iff_convective_navier_stokes`
hold; and the flow satisfies both the convective and the conservative Navier-Stokes predicates.
The velocity vanishes on the lower wall and equals `(Uwall, 0, 0)` on the upper wall.

Parts H-K treat plane Poiseuille flow in the channel `0 ≤ y ≤ H` between two stationary walls,
driven by the pressure `p = p₀ - G x` with `x = x 0` the streamwise coordinate; `G = -∂p/∂x` is a
signed parameter. The velocity `u = (G y (H - y) / (2 μ), 0, 0)` is a smooth representative on
all of `Space`. For `μ ≠ 0` its Newtonian stress has normal entries `-p` and shear entries
`G (H - 2 y) / 2`, and the flow satisfies Physlib's smooth continuity and smooth
incompressibility predicates and both Navier-Stokes forms. Both walls are at rest, and the flow
rate per unit width is `∫₀ᴴ u dy = G H³ / (12 μ)`, nonzero for `G ≠ 0`. With `G = 0` and
stationary walls the flow vanishes, while plane Couette flow moves without a pressure gradient.

## ii. Key results

- `FlowCoordinateBernoulli.fderiv_comp_vadd`: derivatives transport through the chart.
- `FlowCoordinateBernoulli.gradient_comp_vadd`: Mathlib's gradient of the coordinate expression is
  Physlib's `∇`.
- `FlowCoordinateBernoulli.isMIntegralCurveOn_iff_coord`: integral curves in `Space` are exactly
  the coordinate integral curves.
- `FlowCoordinateBernoulli.projected_euler_coord`: Physlib's Euler equations give the projected
  Euler premise at every coordinate point.
- `FlowCoordinateBernoulli.bernoulli_along_streamline_space`: the head `p / ρ + ‖u‖² / 2 + Φ` is
  constant along a streamline in `Space`.
- `FlowCoordinateBernoulli.bernoulliFunction_along_streamline`: Physlib's Bernoulli function is
  constant along a streamline when `h = p / ρ + e₀`.
- `FlowCoordinateBernoulli.rotFlow_euler`: solid-body rotation under gravity satisfies Physlib's
  Euler equations.
- `FlowCoordinateBernoulli.rot_head_differs_across_streamlines`: the head differs between
  streamlines of the fixture.
- `FlowCoordinateBernoulli.polytropic_enthalpy_not_pOverRho`: a polytropic enthalpy is not of the
  form `p / ρ + e₀`.
- `FlowCoordinateBernoulli.couetteFlow_stress`: the Newtonian stress of plane Couette flow.
- `FlowCoordinateBernoulli.couetteFlow_smoothContinuityEquation`: smooth continuity.
- `FlowCoordinateBernoulli.couetteFlow_smoothIncompressible`: smooth incompressibility.
- `FlowCoordinateBernoulli.couetteFlow_navierStokes_premises`: the differentiability premises
  of the conservative-convective equivalence.
- `FlowCoordinateBernoulli.couetteFlow_convectiveNavierStokes`: convective Navier-Stokes.
- `FlowCoordinateBernoulli.couetteFlow_navierStokes`: conservative Navier-Stokes.
- `FlowCoordinateBernoulli.couetteVelocity_lower_wall`,
  `FlowCoordinateBernoulli.couetteVelocity_upper_wall`: the two no-slip walls.
- `FlowCoordinateBernoulli.couetteFlow_witness`: plane Couette flow with the physical hypotheses
  `H, μ, ρ > 0` and `Uwall ≠ 0`.
- `FlowCoordinateBernoulli.planePoiseuilleFlow_stress`: the Newtonian stress of plane Poiseuille
  flow.
- `FlowCoordinateBernoulli.planePoiseuilleFlow_navierStokes`: plane Poiseuille flow satisfies the
  conservative Navier-Stokes equations; the convective form, smooth continuity, smooth
  incompressibility and the differentiability premises are proved alongside.
- `FlowCoordinateBernoulli.planePoiseuilleVelocity_lower_wall`,
  `FlowCoordinateBernoulli.planePoiseuilleVelocity_upper_wall`: the two no-slip walls.
- `FlowCoordinateBernoulli.planePoiseuille_flowRate`: the flow rate `G H³ / (12 μ)`.
- `FlowCoordinateBernoulli.planePoiseuilleFlow_witness`: plane Poiseuille flow with the physical
  hypotheses `H, μ, ρ > 0` and `G ≠ 0`.
- `FlowCoordinateBernoulli.planePoiseuille_zero_gradient_vs_couette`: no pressure gradient and
  stationary walls give no flow, unlike a moving wall.

## iii. Table of contents

- A. Transport through the fixed-origin chart
- B. Discharging the projected Euler premise
- C. Fixtures
- D. Plane Couette flow
- E. Newtonian stress
- F. Continuity, incompressibility and Navier-Stokes
- G. No-slip walls
- H. Plane Poiseuille flow
- I. Newtonian stress, continuity and Navier-Stokes for plane Poiseuille flow
- J. No-slip walls and flow rate
- K. No pressure gradient versus a moving wall

## iv. References

- `EarthScience.bernoulli_along_streamline` (`PhyslibExt.EarthScience.BernoulliStreamline`).
- Physlib's `FluidDynamics.Euler`, `FluidDynamics.CauchyFlow.HasBodyForcePotential` and
  `FluidDynamics.bernoulliFunction`.
- F. M. White, *Viscous Fluid Flow*, 3rd ed., McGraw-Hill (2006), Chapter 3: Couette and
  Poiseuille flow between parallel plates.
- Physlib's `FluidDynamics.NavierStokes`, `FluidDynamics.ConvectiveNavierStokes`,
  `FluidDynamics.CauchyFlow.IsNewtonian`, `FluidDynamics.FluidFlow.SmoothIncompressible` and
  `FluidDynamics.navier_stokes_iff_convective_navier_stokes`.
-/

@[expose] public section

namespace FlowCoordinateBernoulli

open Space FluidDynamics Manifold

/-! ## A. Transport through the fixed-origin chart -/

/-- The torsor action at `o` is Physlib's coordinate map followed by addition of `o`. -/
private lemma vadd_eq_repr_symm_add (o : Space) (v : EuclideanSpace ℝ (Fin 3)) :
    v +ᵥ o = Space.basis.repr.symm v + o := by
  ext i
  simp

/-- Derivatives transport: the coordinate expression of `f` at the chart point of `p`
has derivative `fderiv f p` precomposed with the linear part of the chart. -/
lemma fderiv_comp_vadd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) (o p : Space) (w : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 3) => f (v +ᵥ o)) (p -ᵥ o) w =
      fderiv ℝ f p (Space.basis.repr.symm w) := by
  have h : (fun v : EuclideanSpace ℝ (Fin 3) => f (v +ᵥ o)) =
      (fun y : Space => f (y + o)) ∘ ⇑(Space.basis.repr.symm.toContinuousLinearEquiv) := by
    funext v
    simp [vadd_eq_repr_symm_add]
  have hp : Space.basis.repr.symm.toContinuousLinearEquiv (p -ᵥ o) + o = p := by
    simp [← vadd_eq_repr_symm_add]
  rw [h, ContinuousLinearEquiv.comp_right_fderiv, fderiv_comp_add_right, hp]
  rfl

/-- Directional derivatives of a scalar field in coordinates are inner products with
Physlib's gradient. -/
lemma fderiv_comp_vadd_eq_inner_grad (f : Space → ℝ) (o p : Space)
    (w : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 3) => f (v +ᵥ o)) (p -ᵥ o) w =
      @inner ℝ _ _ (∇ f p) w := by
  rw [fderiv_comp_vadd, ← grad_inner_repr_eq, LinearIsometryEquiv.apply_symm_apply]

/-- Gradients transport: Mathlib's gradient of the coordinate expression is Physlib's
`∇`. -/
lemma gradient_comp_vadd (f : Space → ℝ) (o p : Space) :
    gradient (fun v : EuclideanSpace ℝ (Fin 3) => f (v +ᵥ o)) (p -ᵥ o) = ∇ f p := by
  rw [gradient, LinearIsometryEquiv.symm_apply_eq]
  ext w
  rw [InnerProductSpace.toDual_apply_apply, fderiv_comp_vadd_eq_inner_grad]

/-- The coordinate convective derivative `(fderiv u) u` is Physlib's convective term
`(u · ∇) u`. -/
lemma fderiv_comp_vadd_velocity_eq_convectiveTerm (fluid : FluidFlow 3) (t : Time)
    (o p : Space) :
    fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 3) => fluid.velocity t (v +ᵥ o)) (p -ᵥ o)
        (fluid.velocity t p) =
      FluidFlow.convectiveTerm 3 fluid t p := by
  rw [fderiv_comp_vadd, fderiv_eq_sum_deriv]
  rfl

/-- Integral curves transport: a curve in `Space` is an integral curve of `u` for
Physlib's manifold structure exactly when its coordinate curve is an integral curve of
the coordinate expression of `u`. -/
lemma isMIntegralCurveOn_iff_coord (u : Space → EuclideanSpace ℝ (Fin 3))
    (γ : ℝ → Space) (s : Set ℝ) (o : Space) :
    IsMIntegralCurveOn (I := 𝓡 3) γ u s ↔
      IsIntegralCurveOn (fun t => γ t -ᵥ o)
        (fun _ v => u (v +ᵥ o)) s := by
  unfold IsMIntegralCurveOn IsIntegralCurveOn
  refine forall₂_congr fun t _ => ?_
  simp only [HasMFDerivWithinAt, mfld_simps, Space.chartAt_eq, vsub_vadd]
  -- Physlib's single chart differs from the chart at `o` by a constant vector.
  have hE : (⇑(homEuclideanSpaceSpace 3).symm ∘ γ) =
      fun τ => (γ τ -ᵥ o) + (homEuclideanSpaceSpace 3).symm o := by
    funext τ
    ext i
    simp [homEuclideanSpaceSpace]
  change ContinuousWithinAt γ s t ∧ HasDerivWithinAt (⇑(homEuclideanSpaceSpace 3).symm ∘ γ)
    (u (γ t)) s t ↔ _
  rw [hE, hasDerivWithinAt_add_const_iff]
  refine and_iff_right_of_imp fun h => ?_
  have hc := h.continuousWithinAt.vadd (continuousWithinAt_const (b := o))
  have hγ : ((fun τ => γ τ -ᵥ o) +ᵥ fun _ => o) = γ := by
    funext τ
    exact vsub_vadd (γ τ) o
  rwa [hγ] at hc

/-! ## B. Discharging the projected Euler premise -/

/-- The convective Euler balance of a steady constant-density inviscid flow with a body-force
potential, at one point: `ρ (u · ∇) u = -∇p - ρ ∇Φ`. -/
private lemma convective_balance
    (flow : CauchyFlow 3) (pressure : ScalarField 3) (Φ : Space → ℝ) (ρ : ℝ)
    (hrho : ∀ t x, flow.rho t x = ρ)
    (hsteady : ∀ t t' x, flow.velocity t x = flow.velocity t' x)
    (hu : ∀ t, Differentiable ℝ (flow.velocity t))
    (hEuler : Euler 3 flow pressure)
    (hΦ : CauchyFlow.HasBodyForcePotential 3 flow Φ) (t₀ : Time) (x : Space) :
    ρ • FluidFlow.convectiveTerm 3 flow.toFluidFlow t₀ x =
      -∇ (pressure t₀) x + ρ • -∇ Φ x := by
  have hconst : ∀ x, (fun t => flow.velocity t x) = fun _ => flow.velocity t₀ x :=
    fun x => funext fun t => hsteady t t₀ x
  have hconv := ((euler_iff_convectiveEuler 3 flow pressure
    (fun t x => by simp only [hrho]; exact differentiableAt_const ρ)
    (fun t x => by rw [hconst x]; exact differentiableAt_const _)
    (fun t => by
      unfold FluidFlow.momentumDensity
      simp only [hrho]
      exact (hu t).const_smul ρ)
    hu).mp hEuler).2.1 t₀ x
  rw [CauchyFlow.matrixDiv_stress_eq_neg_grad_pressure_of_is_inviscid 3 flow pressure
    hEuler.2.2 t₀, hΦ t₀ x, hrho t₀ x] at hconv
  unfold FluidFlow.materialAcceleration at hconv
  rw [hconst x, Time.deriv_const, zero_add] at hconv
  simpa using hconv

/-- For a steady constant-density inviscid flow satisfying Physlib's Euler equations
with body-force potential `Φ`, the projected Euler premise of
`EarthScience.bernoulli_along_streamline` holds at every coordinate point. -/
lemma projected_euler_coord
    (flow : CauchyFlow 3) (pressure : ScalarField 3) (Φ : Space → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (hrho : ∀ t x, flow.rho t x = ρ)
    (hsteady : ∀ t t' x, flow.velocity t x = flow.velocity t' x)
    (hu : ∀ t, Differentiable ℝ (flow.velocity t))
    (hEuler : Euler 3 flow pressure)
    (hΦ : CauchyFlow.HasBodyForcePotential 3 flow Φ)
    (t₀ : Time) (o : Space) (v : EuclideanSpace ℝ (Fin 3)) :
    let uE := fun w : EuclideanSpace ℝ (Fin 3) => flow.velocity t₀ (w +ᵥ o)
    let pE := fun w : EuclideanSpace ℝ (Fin 3) => pressure t₀ (w +ᵥ o)
    let ΦE := fun w : EuclideanSpace ℝ (Fin 3) => Φ (w +ᵥ o)
    @inner ℝ _ _ (uE v) ((fderiv ℝ uE v) (uE v)) +
      (1 / ρ) * (fderiv ℝ pE v) (uE v) + (fderiv ℝ ΦE v) (uE v) = 0 := by
  intro uE pE ΦE
  have hC : fderiv ℝ uE v (uE v) =
      FluidFlow.convectiveTerm 3 flow.toFluidFlow t₀ (v +ᵥ o) := by
    simpa using fderiv_comp_vadd_velocity_eq_convectiveTerm flow.toFluidFlow t₀ o (v +ᵥ o)
  have hP : fderiv ℝ pE v (uE v) = @inner ℝ _ _ (∇ (pressure t₀) (v +ᵥ o)) (uE v) := by
    simpa using fderiv_comp_vadd_eq_inner_grad (pressure t₀) o (v +ᵥ o) (uE v)
  have hF : fderiv ℝ ΦE v (uE v) = @inner ℝ _ _ (∇ Φ (v +ᵥ o)) (uE v) := by
    simpa using fderiv_comp_vadd_eq_inner_grad Φ o (v +ᵥ o) (uE v)
  -- Dot the convective balance with `u`.
  have hbal := congrArg (fun z => @inner ℝ _ _ (uE v) z)
    (convective_balance flow pressure Φ ρ hrho hsteady hu hEuler hΦ t₀ (v +ᵥ o))
  simp only [inner_smul_right, inner_add_right, inner_neg_right] at hbal
  rw [real_inner_comm (∇ (pressure t₀) (v +ᵥ o)), real_inner_comm (∇ Φ (v +ᵥ o))] at hbal
  rw [hC, hP, hF]
  field_simp
  linear_combination hbal

/-- Bernoulli's theorem along a streamline in `Space`, for a steady constant-density
inviscid Physlib Euler flow with body-force potential: the head `p / ρ + ‖u‖² / 2 + Φ`
takes the same value at any two points of an integral curve of the velocity. -/
lemma bernoulli_along_streamline_space
    (flow : CauchyFlow 3) (pressure : ScalarField 3) (Φ : Space → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (hrho : ∀ t x, flow.rho t x = ρ)
    (hsteady : ∀ t t' x, flow.velocity t x = flow.velocity t' x)
    (hu : ∀ t, Differentiable ℝ (flow.velocity t))
    (hEuler : Euler 3 flow pressure)
    (hΦ : CauchyFlow.HasBodyForcePotential 3 flow Φ)
    (t₀ : Time) (γ : ℝ → Space) {s : Set ℝ} (hs : IsOpen s) (hs' : IsPreconnected s)
    (hγ : IsMIntegralCurveOn (I := 𝓡 3) γ (flow.velocity t₀) s)
    (hp : ∀ t ∈ s, DifferentiableAt ℝ (pressure t₀) (γ t))
    (hΦd : ∀ t ∈ s, DifferentiableAt ℝ Φ (γ t))
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    pressure t₀ (γ a) / ρ + ‖flow.velocity t₀ (γ a)‖ ^ 2 / 2 + Φ (γ a) =
      pressure t₀ (γ b) / ρ + ‖flow.velocity t₀ (γ b)‖ ^ 2 / 2 + Φ (γ b) := by
  -- Coordinates about the point `γ a` of the streamline.
  have hvadd := vadd_differentiable (γ a)
  have key := EarthScience.bernoulli_along_streamline
    (fun w => flow.velocity t₀ (w +ᵥ γ a)) (fun w => pressure t₀ (w +ᵥ γ a))
    (fun w => Φ (w +ᵥ γ a)) ρ hρ (fun t => γ t -ᵥ γ a) hs hs'
    ((isMIntegralCurveOn_iff_coord _ γ s (γ a)).mp hγ)
    (fun t _ => ((hu t₀) _).comp _ (hvadd _))
    (fun t ht => by
      refine DifferentiableAt.comp _ ?_ (hvadd _)
      simpa using hp t ht)
    (fun t ht => by
      refine DifferentiableAt.comp _ ?_ (hvadd _)
      simpa using hΦd t ht)
    (fun t _ => projected_euler_coord flow pressure Φ ρ hρ hrho hsteady hu hEuler hΦ t₀ (γ a) _)
    ha hb
  simpa only [vsub_vadd] using key

/-- Physlib's enthalpy Bernoulli function is constant along a streamline when the
specific enthalpy is `p / ρ + e₀` (constant specific internal energy `e₀`). Without that
hypothesis the enthalpy field is independent data; see `polytropic_enthalpy_not_pOverRho`. -/
lemma bernoulliFunction_along_streamline
    (flow : ThermodynamicCauchyFlow 3) (pressure : ScalarField 3) (Φ : Space → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (hrho : ∀ t x, flow.rho t x = ρ)
    (hsteady : ∀ t t' x, flow.velocity t x = flow.velocity t' x)
    (hu : ∀ t, Differentiable ℝ (flow.velocity t))
    (hEuler : Euler 3 flow.toCauchyFlow pressure)
    (hΦ : CauchyFlow.HasBodyForcePotential 3 flow.toCauchyFlow Φ)
    (t₀ : Time) (e₀ : ℝ) (henth : ∀ x, flow.enthalpy t₀ x = pressure t₀ x / ρ + e₀)
    (γ : ℝ → Space) {s : Set ℝ} (hs : IsOpen s) (hs' : IsPreconnected s)
    (hγ : IsMIntegralCurveOn (I := 𝓡 3) γ (flow.velocity t₀) s)
    (hp : ∀ t ∈ s, DifferentiableAt ℝ (pressure t₀) (γ t))
    (hΦd : ∀ t ∈ s, DifferentiableAt ℝ Φ (γ t))
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    bernoulliFunction 3 flow Φ t₀ (γ a) = bernoulliFunction 3 flow Φ t₀ (γ b) := by
  have key := bernoulli_along_streamline_space flow.toCauchyFlow pressure Φ ρ hρ hrho hsteady hu
    hEuler hΦ t₀ γ hs hs' hγ hp hΦd ha hb
  simp only [bernoulliFunction, FluidFlow.specificKineticEnergy, henth,
    real_inner_self_eq_norm_sq]
  linear_combination key

/-! ## C. Fixtures -/

/-- Solid-body rotation about the third axis with angular speed `Ω`. -/
noncomputable def rotVelocity (Ω : ℝ) : Space → EuclideanSpace ℝ (Fin 3) :=
  fun x => WithLp.toLp 2 ![-Ω * x 1, Ω * x 0, 0]

/-- Gravitational potential `g x₃`. -/
def gravPotential (g : ℝ) : Space → ℝ := fun x => g * x 2

/-- Pressure balancing rotation and gravity. -/
noncomputable def rotPressure (ρ Ω g : ℝ) : Space → ℝ :=
  fun x => ρ * Ω ^ 2 * (x 0 ^ 2 + x 1 ^ 2) / 2 - ρ * g * x 2

/-- Steady constant-density rotating flow under gravity, with inviscid stress. -/
noncomputable def rotFlow (ρ Ω g : ℝ) : CauchyFlow 3 where
  rho := fun _ _ => ρ
  velocity := fun _ => rotVelocity Ω
  stress := fun _ x => (-(rotPressure ρ Ω g x)) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
  specificBodyForce := fun _ _ => WithLp.toLp 2 ![0, 0, -g]

/-- A circular streamline of radius `R` at height `z`. -/
noncomputable def circle (R Ω z : ℝ) : ℝ → Space :=
  fun t => ⟨![R * Real.cos (Ω * t), R * Real.sin (Ω * t), z]⟩

private lemma rotVelocity_differentiable (Ω : ℝ) : Differentiable ℝ (rotVelocity Ω) := by
  refine differentiable_euclidean.mpr fun i => ?_
  unfold rotVelocity
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, neg_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, differentiable_fun_neg_iff,
      differentiable_const] <;>
    fun_prop

/-- The rotation field is linear, so its directional derivatives are its values on the basis. -/
private lemma deriv_rotVelocity (Ω : ℝ) (x : Space) (i : Fin 3) :
    ∂[i] (rotVelocity Ω) x = rotVelocity Ω (basis i) := by
  ext j
  rw [← deriv_euclid (rotVelocity_differentiable Ω), Space.deriv_eq]
  unfold rotVelocity
  fin_cases j <;> simp (disch := fun_prop) [fderiv_const_mul]

private lemma deriv_rotPressure (ρ Ω g : ℝ) (x : Space) (i : Fin 3) :
    ∂[i] (rotPressure ρ Ω g) x = ![ρ * Ω ^ 2 * x 0, ρ * Ω ^ 2 * x 1, -(ρ * g)] i := by
  have h : rotPressure ρ Ω g =
      fun x => ρ * Ω ^ 2 / 2 * (x 0 ^ 2 + x 1 ^ 2) - ρ * g * x 2 := by
    funext x
    simp only [rotPressure]
    ring
  rw [Space.deriv_eq, h]
  simp (disch := fun_prop) only [Fin.isValue, fderiv_fun_sub, fderiv_const_mul, fderiv_fun_add,
    smul_add, _root_.sub_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul, fderiv_eval_apply]
  simp only [← Space.deriv_eq, deriv_component_sq]
  fin_cases i <;> simp [basis_apply] <;> ring

private lemma grad_rotPressure (ρ Ω g : ℝ) (x : Space) :
    ∇ (rotPressure ρ Ω g) x = WithLp.toLp 2 ![ρ * Ω ^ 2 * x 0, ρ * Ω ^ 2 * x 1, -(ρ * g)] := by
  ext i
  rw [grad_apply, deriv_rotPressure]

private lemma grad_gravPotential (g : ℝ) (x : Space) :
    ∇ (gravPotential g) x = WithLp.toLp 2 ![0, 0, g] := by
  ext i
  rw [grad_apply, Space.deriv_eq]
  unfold gravPotential
  simp (disch := fun_prop) only [Fin.isValue, fderiv_const_mul, _root_.smul_apply,
    fderiv_eval_apply, smul_eq_mul]
  fin_cases i <;> simp [basis_apply]

/-- The rotation field is divergence free. -/
private lemma div_smul_rotVelocity (ρ Ω : ℝ) (x : Space) :
    Space.div (fun x' => ρ • rotVelocity Ω x') x = 0 := by
  have hd : Differentiable ℝ (fun x' => ρ • rotVelocity Ω x') :=
    (rotVelocity_differentiable Ω).const_smul ρ
  have h : ∀ i, ∂[i] (fun x' => ρ • rotVelocity Ω x') x = ρ • rotVelocity Ω (basis i) := by
    intro i
    change fderiv ℝ (ρ • rotVelocity Ω) x (basis i) = _
    rw [fderiv_const_smul ((rotVelocity_differentiable Ω) x), _root_.smul_apply,
      ← Space.deriv_eq, deriv_rotVelocity]
  unfold Space.div
  simp only [deriv_euclid hd, h, Fin.sum_univ_three]
  simp [rotVelocity, basis_apply]

/-- The rotating fixture satisfies Physlib's Euler equations with the balancing pressure. -/
lemma rotFlow_euler (ρ Ω g : ℝ) :
    Euler 3 (rotFlow ρ Ω g) (fun _ => rotPressure ρ Ω g) := by
  have hInv : CauchyFlow.IsInviscid 3 (rotFlow ρ Ω g) (fun _ => rotPressure ρ Ω g) :=
    fun _ _ => rfl
  have hCont : FluidFlow.ClassicalContinuityEquation 3 (rotFlow ρ Ω g).toFluidFlow := by
    intro t x _ _
    simp only [rotFlow]
    rw [Time.deriv_const, zero_add]
    exact div_smul_rotVelocity ρ Ω x
  -- Check the convective form, which is equivalent for these differentiable fields.
  refine (euler_iff_convectiveEuler 3 (rotFlow ρ Ω g) (fun _ => rotPressure ρ Ω g)
    (fun _ _ => differentiableAt_const ρ)
    (fun _ x => differentiableAt_const (rotVelocity Ω x))
    (fun _ => (rotVelocity_differentiable Ω).const_smul ρ)
    (fun _ => rotVelocity_differentiable Ω)).mpr ⟨hCont, ?_, hInv⟩
  intro t x
  rw [CauchyFlow.matrixDiv_stress_eq_neg_grad_pressure_of_is_inviscid 3 _ _ hInv t]
  simp only [FluidFlow.materialAcceleration, FluidFlow.convectiveTerm, rotFlow, Time.deriv_const,
    zero_add, Pi.neg_apply, grad_rotPressure, deriv_rotVelocity, Fin.sum_univ_three]
  ext i
  fin_cases i <;> simp [rotVelocity, basis_apply] <;> ring

/-- Gravity in the rotating fixture has the potential `g x₃`. -/
lemma rotFlow_bodyForcePotential (ρ Ω g : ℝ) :
    CauchyFlow.HasBodyForcePotential 3 (rotFlow ρ Ω g) (gravPotential g) := by
  intro t x
  rw [grad_gravPotential]
  ext i
  fin_cases i <;> simp [rotFlow]

/-- The fixture is a nonzero flow. -/
lemma rotVelocity_ne_zero {Ω : ℝ} (hΩ : Ω ≠ 0) :
    rotVelocity Ω (circle 1 Ω 0 0) ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
  simp [rotVelocity, circle, hΩ] at h1

/-- The coordinate curve of the circle about `o` has velocity `rotVelocity Ω`. -/
private lemma circle_hasDerivAt_coord (R Ω z : ℝ) (o : Space) (t : ℝ) :
    HasDerivAt (fun τ => circle R Ω z τ -ᵥ o) (rotVelocity Ω (circle R Ω z t)) t := by
  have hθ : HasDerivAt (fun τ : ℝ => Ω * τ) Ω t := by
    simpa using (hasDerivAt_id t).const_mul Ω
  have h0 : HasDerivAt (fun τ => circle R Ω z τ 0 - o 0) (rotVelocity Ω (circle R Ω z t) 0) t := by
    have := (((Real.hasDerivAt_cos (Ω * t)).comp t hθ).const_mul R).sub_const (o 0)
    convert this using 1
    · simp [circle]
    · unfold rotVelocity circle
      simp
      ring
  have h1 : HasDerivAt (fun τ => circle R Ω z τ 1 - o 1) (rotVelocity Ω (circle R Ω z t) 1) t := by
    have := (((Real.hasDerivAt_sin (Ω * t)).comp t hθ).const_mul R).sub_const (o 1)
    convert this using 1
    · simp [circle]
    · unfold rotVelocity circle
      simp
      ring
  have h2 : HasDerivAt (fun τ => circle R Ω z τ 2 - o 2) (rotVelocity Ω (circle R Ω z t) 2) t := by
    simpa [rotVelocity, circle] using hasDerivAt_const t (z - o 2)
  have h : HasDerivAt (fun τ : ℝ => fun i : Fin 3 => circle R Ω z τ i - o i)
      (fun i => rotVelocity Ω (circle R Ω z t) i) t := by
    refine hasDerivAt_pi.mpr fun i => ?_
    fin_cases i
    exacts [h0, h1, h2]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t h

/-- The circle is a streamline in `Space`. -/
lemma circle_isMIntegralCurveOn (R Ω z : ℝ) :
    IsMIntegralCurveOn (I := 𝓡 3) (circle R Ω z) (rotVelocity Ω) Set.univ :=
  (isMIntegralCurveOn_iff_coord _ _ _ (circle R Ω z 0)).mpr fun t _ => by
    simpa only [vsub_vadd] using (circle_hasDerivAt_coord R Ω z (circle R Ω z 0) t).hasDerivWithinAt

/-- The circle is a streamline in coordinates about any origin. -/
lemma circle_isIntegralCurveOn_coord (R Ω z : ℝ) (o : Space) :
    IsIntegralCurveOn (fun t => circle R Ω z t -ᵥ o)
      (fun _ v => rotVelocity Ω (v +ᵥ o)) Set.univ := by
  intro t _
  simpa only [vsub_vadd] using (circle_hasDerivAt_coord R Ω z o t).hasDerivWithinAt

/-- The head is constant along each streamline but differs between streamlines, so the
result is streamline constancy, not global constancy. -/
lemma rot_head_differs_across_streamlines {ρ Ω g : ℝ} (hρ : 0 < ρ) (hΩ : Ω ≠ 0) :
    rotPressure ρ Ω g (circle 1 Ω 0 0) / ρ + ‖rotVelocity Ω (circle 1 Ω 0 0)‖ ^ 2 / 2 +
        gravPotential g (circle 1 Ω 0 0) ≠
      rotPressure ρ Ω g (circle 2 Ω 0 0) / ρ + ‖rotVelocity Ω (circle 2 Ω 0 0)‖ ^ 2 / 2 +
        gravPotential g (circle 2 Ω 0 0) := by
  simp only [rotPressure, rotVelocity, gravPotential, circle, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_three, mul_zero, Real.cos_zero, mul_one, Real.sin_zero, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add, sub_zero,
    Real.norm_eq_abs, sq_abs]
  intro h
  have hρ0 : ρ ≠ 0 := hρ.ne'
  -- The head is `Ω²` on the unit circle and `4 Ω²` on the circle of radius two.
  have e1 : ρ * Ω ^ 2 / 2 / ρ = Ω ^ 2 / 2 := by field_simp
  have e2 : ρ * Ω ^ 2 * 2 ^ 2 / 2 / ρ = 2 * Ω ^ 2 := by field_simp
  rw [e1, e2] at h
  have hsq : Ω ^ 2 = 0 := by linarith
  exact hΩ (pow_eq_zero_iff two_ne_zero |>.mp hsq)

/-- The rotating fixture with a polytropic enthalpy `h = (γ / (γ - 1)) p / ρ`, `γ = 7/5`. -/
noncomputable def polytropicFlow (ρ Ω g : ℝ) : ThermodynamicCauchyFlow 3 :=
  { rotFlow ρ Ω g with
    entropy := fun _ _ => 0
    enthalpy := fun _ x => (7 / 2 : ℝ) * rotPressure ρ Ω g x / ρ }

/-- The enthalpy hypothesis is not automatic: a compressible-gas enthalpy
`(7 / 2) p / ρ` is not of the form `p / ρ + e₀`, so
`bernoulliFunction_along_streamline` cannot be applied to this fixture without
checking the hypothesis. (Along each circular streamline of the fixture the
Bernoulli function is nevertheless constant, since pressure, enthalpy, kinetic
energy and potential are each constant there; this example shows the hypothesis
must be checked, not that constancy fails without it.) -/
lemma polytropic_enthalpy_not_pOverRho {ρ Ω g : ℝ} (hρ : 0 < ρ) (hg : g ≠ 0) :
    ¬ ∃ e₀ : ℝ, ∀ t x,
      (polytropicFlow ρ Ω g).enthalpy t x = rotPressure ρ Ω g x / ρ + e₀ := by
  rintro ⟨e₀, he⟩
  -- Compare the origin with the point at unit height.
  have h0 := he ⟨0⟩ ⟨![0, 0, 0]⟩
  have h1 := he ⟨0⟩ ⟨![0, 0, 1]⟩
  simp only [polytropicFlow, rotPressure, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero,
    zero_div, sub_self, zero_add, mul_one, zero_sub, mul_neg] at h0 h1
  rw [← h0, add_zero] at h1
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have e1 : -(7 / 2 * (ρ * g)) / ρ = -(7 / 2 * g) := by field_simp
  have e2 : -(ρ * g) / ρ = -g := by field_simp
  rw [e1, e2] at h1
  exact hg (by linarith)

/-! ## D. Plane Couette flow -/

/-- Plane Couette velocity `(Uwall * y / H, 0, 0)` with `y = x 1` the wall-normal coordinate.
-/
noncomputable def couetteVelocity (Uwall H : ℝ) : Space → EuclideanSpace ℝ (Fin 3) :=
  fun x => WithLp.toLp 2 ![Uwall * x 1 / H, 0, 0]

/-- Density and velocity of plane Couette flow with constant density `ρ`. -/
noncomputable def couetteFluid (ρ Uwall H : ℝ) : FluidFlow 3 where
  rho := fun _ _ => ρ
  velocity := fun _ => couetteVelocity Uwall H

/-- Plane Couette flow: constant density `ρ`, the steady Couette velocity, Physlib's Newtonian
stress for constant pressure `p₀`, shear viscosity `μ` and second viscosity `lam`, and no body
force. -/
noncomputable def couetteFlow (ρ μ lam p₀ Uwall H : ℝ) : CauchyFlow 3 where
  toFluidFlow := couetteFluid ρ Uwall H
  stress := FluidFlow.newtonianStressTensor 3 (couetteFluid ρ Uwall H) (fun _ _ => p₀)
    (fun _ _ => μ) (fun _ _ => lam)
  specificBodyForce := fun _ _ => 0

/-- The plane Couette velocity is differentiable. -/
private lemma couetteVelocity_differentiable (Uwall H : ℝ) :
    Differentiable ℝ (couetteVelocity Uwall H) := by
  refine differentiable_euclidean.mpr fun i => ?_
  unfold couetteVelocity
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    fun_prop
  · simp
  · simp

/-- The plane Couette velocity is linear, so its directional derivatives are its values on the
basis. -/
private lemma deriv_couetteVelocity (Uwall H : ℝ) (x : Space) (i : Fin 3) :
    ∂[i] (couetteVelocity Uwall H) x = couetteVelocity Uwall H (basis i) := by
  ext j
  rw [← deriv_euclid (couetteVelocity_differentiable Uwall H), Space.deriv_eq]
  unfold couetteVelocity
  fin_cases j
  · simp (disch := fun_prop) [fderiv_const_mul, div_eq_mul_inv, fderiv_mul_const]
    ring
  · simp
  · simp

/-- The plane Couette velocity on the basis: only `basis 1` has a nonzero image, with first
component `Uwall / H`. -/
private lemma couetteVelocity_basis (Uwall H : ℝ) (i j : Fin 3) :
    couetteVelocity Uwall H (basis i) j =
      if j = 0 ∧ i = 1 then Uwall / H else 0 := by
  unfold couetteVelocity
  fin_cases i <;> fin_cases j <;> simp [basis_apply]

/-- The plane Couette velocity is divergence free. -/
private lemma div_couetteVelocity (Uwall H : ℝ) (x : Space) :
    (∇ ⬝ couetteVelocity Uwall H) x = 0 := by
  unfold Space.div
  simp only [deriv_euclid (couetteVelocity_differentiable Uwall H), deriv_couetteVelocity,
    Fin.sum_univ_three, couetteVelocity_basis]
  simp

/-- The plane Couette mass flux `ρ u` is divergence free. -/
private lemma div_smul_couetteVelocity (ρ Uwall H : ℝ) (x : Space) :
    (∇ ⬝ fun x' => ρ • couetteVelocity Uwall H x') x = 0 := by
  have hd : Differentiable ℝ (fun x' => ρ • couetteVelocity Uwall H x') :=
    (couetteVelocity_differentiable Uwall H).const_smul ρ
  have h : ∀ i, ∂[i] (fun x' => ρ • couetteVelocity Uwall H x') x =
      ρ • couetteVelocity Uwall H (basis i) := by
    intro i
    change fderiv ℝ (ρ • couetteVelocity Uwall H) x (basis i) = _
    rw [fderiv_const_smul ((couetteVelocity_differentiable Uwall H) x), _root_.smul_apply,
      ← Space.deriv_eq, deriv_couetteVelocity]
  unfold Space.div
  simp only [deriv_euclid hd, h, Fin.sum_univ_three]
  simp [couetteVelocity_basis]

/-- The velocity gradient of plane Couette flow has the single nonzero entry
`∂₁ u₀ = Uwall / H`. -/
private lemma velocityGradient_couette (ρ Uwall H : ℝ) (t : Time) (x : Space) (i j : Fin 3) :
    FluidFlow.velocityGradient 3 (couetteFluid ρ Uwall H) t x i j =
      if i = 0 ∧ j = 1 then Uwall / H else 0 := by
  unfold FluidFlow.velocityGradient
  simp only [couetteFluid]
  rw [deriv_euclid (couetteVelocity_differentiable Uwall H), deriv_couetteVelocity,
    couetteVelocity_basis]

/-! ## E. Newtonian stress -/

/-- The Newtonian stress of plane Couette flow is the constant matrix with normal entries
`-p₀` and shear entries `μ Uwall / H`; the second viscosity drops out. -/
lemma couetteFlow_stress (ρ μ lam p₀ Uwall H : ℝ) (t : Time) (x : Space) :
    (couetteFlow ρ μ lam p₀ Uwall H).stress t x =
      !![-p₀, μ * Uwall / H, 0; μ * Uwall / H, -p₀, 0; 0, 0, -p₀] := by
  ext i j
  simp only [couetteFlow, FluidFlow.newtonianStressTensor]
  have hdiv : (∇ ⬝ (couetteFluid ρ Uwall H).velocity t) x = 0 := div_couetteVelocity Uwall H x
  rw [hdiv]
  fin_cases i <;> fin_cases j <;>
    simp [velocityGradient_couette, Matrix.transpose_apply] <;> ring

/-! ## F. Continuity, incompressibility and Navier-Stokes -/

/-- Plane Couette flow satisfies Physlib's smooth continuity equation: the density is
differentiable in time, the mass flux is differentiable in space, and the continuity residual
vanishes. -/
lemma couetteFlow_smoothContinuityEquation (ρ μ lam p₀ Uwall H : ℝ) :
    FluidFlow.SmoothContinuityEquation 3 (couetteFlow ρ μ lam p₀ Uwall H).toFluidFlow := by
  refine ⟨fun x => differentiable_const ρ,
    fun t => (couetteVelocity_differentiable Uwall H).const_smul ρ, fun t x => ?_⟩
  simp only [FluidFlow.continuityResidual, couetteFlow, couetteFluid]
  rw [Time.deriv_const, zero_add]
  exact div_smul_couetteVelocity ρ Uwall H x

/-- Plane Couette flow is smoothly incompressible: the velocity is differentiable and
divergence free. -/
lemma couetteFlow_smoothIncompressible (ρ μ lam p₀ Uwall H : ℝ) :
    FluidFlow.SmoothIncompressible 3 (couetteFlow ρ μ lam p₀ Uwall H).toFluidFlow := by
  exact ⟨fun t => couetteVelocity_differentiable Uwall H,
    fun t x => div_couetteVelocity Uwall H x⟩

/-- The four differentiability premises of
`FluidDynamics.navier_stokes_iff_convective_navier_stokes` hold for plane Couette flow. -/
lemma couetteFlow_navierStokes_premises (ρ μ lam p₀ Uwall H : ℝ) :
    (∀ t x, DifferentiableAt ℝ ((couetteFlow ρ μ lam p₀ Uwall H).rho · x) t) ∧
      (∀ t x, DifferentiableAt ℝ ((couetteFlow ρ μ lam p₀ Uwall H).velocity · x) t) ∧
      (∀ t, Differentiable ℝ
        (FluidFlow.momentumDensity 3 (couetteFlow ρ μ lam p₀ Uwall H).toFluidFlow t)) ∧
      ∀ t, Differentiable ℝ ((couetteFlow ρ μ lam p₀ Uwall H).velocity t) := by
  refine ⟨fun t x => differentiableAt_const ρ, fun t x => differentiableAt_const _, fun t => ?_,
    fun t => couetteVelocity_differentiable Uwall H⟩
  unfold FluidFlow.momentumDensity
  exact (couetteVelocity_differentiable Uwall H).const_smul ρ

/-- Plane Couette flow satisfies Physlib's convective Navier-Stokes equations with constant
pressure `p₀`, shear viscosity `μ` and second viscosity `lam`. -/
lemma couetteFlow_convectiveNavierStokes (ρ μ lam p₀ Uwall H : ℝ) :
    ConvectiveNavierStokes 3 (couetteFlow ρ μ lam p₀ Uwall H) (fun _ _ => p₀) (fun _ _ => μ)
      (fun _ _ => lam) := by
  refine ⟨FluidFlow.classicalContinuityEquation_of_smoothContinuityEquation 3 _
    (couetteFlow_smoothContinuityEquation ρ μ lam p₀ Uwall H), fun t x => ?_, fun t x => rfl⟩
  have hσ : (couetteFlow ρ μ lam p₀ Uwall H).stress t =
      fun _ => !![-p₀, μ * Uwall / H, 0; μ * Uwall / H, -p₀, 0; 0, 0, -p₀] := by
    funext y
    exact couetteFlow_stress ρ μ lam p₀ Uwall H t y
  rw [hσ, matrixDiv_const]
  simp only [FluidFlow.materialAcceleration, FluidFlow.convectiveTerm, couetteFlow, couetteFluid,
    Time.deriv_const, zero_add, deriv_couetteVelocity, Fin.sum_univ_three]
  ext i
  fin_cases i <;> simp [couetteVelocity, basis_apply]

/-- Plane Couette flow satisfies Physlib's conservative Navier-Stokes equations with constant
pressure `p₀`, shear viscosity `μ` and second viscosity `lam`. -/
lemma couetteFlow_navierStokes (ρ μ lam p₀ Uwall H : ℝ) :
    NavierStokes 3 (couetteFlow ρ μ lam p₀ Uwall H) (fun _ _ => p₀) (fun _ _ => μ)
      (fun _ _ => lam) := by
  obtain ⟨h1, h2, h3, h4⟩ := couetteFlow_navierStokes_premises ρ μ lam p₀ Uwall H
  exact (navier_stokes_iff_convective_navier_stokes 3 _ _ _ _ h1 h2 h3 h4).mpr
    (couetteFlow_convectiveNavierStokes ρ μ lam p₀ Uwall H)

/-! ## G. No-slip walls -/

/-- The lower wall `y = 0` is at rest. -/
lemma couetteVelocity_lower_wall (Uwall H : ℝ) (x : Space) (hx : x 1 = 0) :
    couetteVelocity Uwall H x = 0 := by
  ext i
  fin_cases i <;> simp [couetteVelocity, hx]

/-- The upper wall `y = H` moves with velocity `(Uwall, 0, 0)`. -/
lemma couetteVelocity_upper_wall {Uwall H : ℝ} (hH : 0 < H) (x : Space) (hx : x 1 = H) :
    couetteVelocity Uwall H x = WithLp.toLp 2 ![Uwall, 0, 0] := by
  ext i
  fin_cases i <;> simp [couetteVelocity, hx, hH.ne']

/-- Plane Couette flow with the physical hypotheses `H, μ, ρ > 0`, constant pressure and
`Uwall ≠ 0`: the density is positive, the flow is smoothly incompressible and satisfies the
conservative Navier-Stokes equations, the lower wall is at rest, the upper wall moves with
velocity `(Uwall, 0, 0)`, and the shear stress `μ Uwall / H` is nonzero. -/
lemma couetteFlow_witness {ρ μ H Uwall : ℝ} (lam p₀ : ℝ) (hH : 0 < H) (hμ : 0 < μ)
    (hρ : 0 < ρ) (hU : Uwall ≠ 0) :
    (∀ t x, 0 < (couetteFlow ρ μ lam p₀ Uwall H).rho t x) ∧
      FluidFlow.SmoothIncompressible 3 (couetteFlow ρ μ lam p₀ Uwall H).toFluidFlow ∧
      NavierStokes 3 (couetteFlow ρ μ lam p₀ Uwall H) (fun _ _ => p₀) (fun _ _ => μ)
        (fun _ _ => lam) ∧
      (∀ t (x : Space), x 1 = 0 → (couetteFlow ρ μ lam p₀ Uwall H).velocity t x = 0) ∧
      (∀ t (x : Space), x 1 = H →
        (couetteFlow ρ μ lam p₀ Uwall H).velocity t x = WithLp.toLp 2 ![Uwall, 0, 0]) ∧
      ∀ t x, (couetteFlow ρ μ lam p₀ Uwall H).stress t x 0 1 ≠ 0 := by
  refine ⟨fun t x => hρ, couetteFlow_smoothIncompressible ρ μ lam p₀ Uwall H,
    couetteFlow_navierStokes ρ μ lam p₀ Uwall H,
    fun t x hx => couetteVelocity_lower_wall Uwall H x hx,
    fun t x hx => couetteVelocity_upper_wall hH x hx, fun t x => ?_⟩
  rw [couetteFlow_stress]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  exact div_ne_zero (mul_ne_zero hμ.ne' hU) hH.ne'

/-! ## H. Plane Poiseuille flow -/

/-- Plane Poiseuille velocity `(G y (H - y) / (2 μ), 0, 0)` with `y = x 1` the wall-normal
coordinate and `G = -∂p/∂x` the signed pressure-drop rate. -/
noncomputable def planePoiseuilleVelocity (G μ H : ℝ) : Space → EuclideanSpace ℝ (Fin 3) :=
  fun x => WithLp.toLp 2 ![G * x 1 * (H - x 1) / (2 * μ), 0, 0]

/-- The linear pressure `p₀ - G x` with `x = x 0` the streamwise coordinate. -/
def planePoiseuillePressure (p₀ G : ℝ) : Space → ℝ :=
  fun x => p₀ - G * x 0

/-- Density and velocity of plane Poiseuille flow with constant density `ρ`. -/
noncomputable def planePoiseuilleFluid (ρ G μ H : ℝ) : FluidFlow 3 where
  rho := fun _ _ => ρ
  velocity := fun _ => planePoiseuilleVelocity G μ H

/-- Plane Poiseuille flow: constant density `ρ`, the steady Poiseuille velocity, Physlib's
Newtonian stress for the pressure `p₀ - G x`, shear viscosity `μ` and second viscosity `lam`,
and no body force. -/
noncomputable def planePoiseuilleFlow (ρ μ lam p₀ G H : ℝ) : CauchyFlow 3 where
  toFluidFlow := planePoiseuilleFluid ρ G μ H
  stress := FluidFlow.newtonianStressTensor 3 (planePoiseuilleFluid ρ G μ H)
    (fun _ x => planePoiseuillePressure p₀ G x) (fun _ _ => μ) (fun _ _ => lam)
  specificBodyForce := fun _ _ => 0

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

private lemma planePoiseuilleVelocity_differentiable (G μ H : ℝ) :
    Differentiable ℝ (planePoiseuilleVelocity G μ H) := by
  refine differentiable_euclidean.mpr fun i => ?_
  unfold planePoiseuilleVelocity
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    fun_prop
  · simp
  · simp

private lemma deriv_planePoiseuilleVelocity (G μ H : ℝ) (x : Space) (i j : Fin 3) :
    ∂[j] (fun x' => planePoiseuilleVelocity G μ H x' i) x =
      if i = 0 ∧ j = 1 then G * (H - 2 * x 1) / (2 * μ) else 0 := by
  fin_cases i
  · have hg : HasDerivAt (fun y : ℝ => G * y * (H - y) / (2 * μ))
        (G * (H - 2 * x 1) / (2 * μ)) (x 1) :=
      ((((hasDerivAt_id (x 1)).const_mul G).mul ((hasDerivAt_id (x 1)).const_sub H)).div_const
        (2 * μ)).congr_deriv (by simp only [id]; ring)
    have h := deriv_comp_coord 1 j hg
    simp only [Fin.zero_eta, Fin.isValue, true_and]
    rw [← h]
    rfl
  · simp [planePoiseuilleVelocity]
  · simp [planePoiseuilleVelocity]

private lemma div_planePoiseuilleVelocity (G μ H : ℝ) (x : Space) :
    (∇ ⬝ planePoiseuilleVelocity G μ H) x = 0 := by
  unfold Space.div
  simp [Fin.sum_univ_three, deriv_planePoiseuilleVelocity]

private lemma div_smul_planePoiseuilleVelocity (ρ G μ H : ℝ) (x : Space) :
    (∇ ⬝ fun x' => ρ • planePoiseuilleVelocity G μ H x') x = 0 := by
  have hd : Differentiable ℝ (fun x' => ρ • planePoiseuilleVelocity G μ H x') :=
    (planePoiseuilleVelocity_differentiable G μ H).const_smul ρ
  have h : ∀ i, ∂[i] (fun x' => ρ • planePoiseuilleVelocity G μ H x') x =
      ρ • ∂[i] (planePoiseuilleVelocity G μ H) x := by
    intro i
    change fderiv ℝ (ρ • planePoiseuilleVelocity G μ H) x (basis i) = _
    rw [fderiv_const_smul ((planePoiseuilleVelocity_differentiable G μ H) x), _root_.smul_apply,
      ← Space.deriv_eq]
  unfold Space.div
  simp only [deriv_euclid hd, h, Fin.sum_univ_three]
  simp [← deriv_euclid (planePoiseuilleVelocity_differentiable G μ H),
    deriv_planePoiseuilleVelocity]

private lemma velocityGradient_planePoiseuille (ρ G μ H : ℝ) (t : Time) (x : Space)
    (i j : Fin 3) :
    FluidFlow.velocityGradient 3 (planePoiseuilleFluid ρ G μ H) t x i j =
      if i = 0 ∧ j = 1 then G * (H - 2 * x 1) / (2 * μ) else 0 := by
  unfold FluidFlow.velocityGradient
  exact deriv_planePoiseuilleVelocity G μ H x i j
/-! ## I. Newtonian stress, continuity and Navier-Stokes for plane Poiseuille flow -/

/-- For `μ ≠ 0` the Newtonian stress of plane Poiseuille flow has normal entries `-p` and shear
entries `G (H - 2 y) / 2`; the second viscosity drops out. -/
lemma planePoiseuilleFlow_stress {μ : ℝ} (hμ : μ ≠ 0) (ρ lam p₀ G H : ℝ) (t : Time)
    (x : Space) :
    (planePoiseuilleFlow ρ μ lam p₀ G H).stress t x =
      !![-(p₀ - G * x 0), G * (H - 2 * x 1) / 2, 0;
        G * (H - 2 * x 1) / 2, -(p₀ - G * x 0), 0;
        0, 0, -(p₀ - G * x 0)] := by
  ext i j
  simp only [planePoiseuilleFlow, FluidFlow.newtonianStressTensor]
  have hdiv : (∇ ⬝ (planePoiseuilleFluid ρ G μ H).velocity t) x = 0 :=
    div_planePoiseuilleVelocity G μ H x
  rw [hdiv]
  fin_cases i <;> fin_cases j <;>
    simp [velocityGradient_planePoiseuille, Matrix.transpose_apply, planePoiseuillePressure] <;>
    field_simp

/-- Plane Poiseuille flow satisfies Physlib's smooth continuity equation: the density is
differentiable in time, the mass flux is differentiable in space, and the continuity residual
vanishes. -/
lemma planePoiseuilleFlow_smoothContinuityEquation (ρ μ lam p₀ G H : ℝ) :
    FluidFlow.SmoothContinuityEquation 3 (planePoiseuilleFlow ρ μ lam p₀ G H).toFluidFlow := by
  refine ⟨fun x => differentiable_const ρ,
    fun t => (planePoiseuilleVelocity_differentiable G μ H).const_smul ρ, fun t x => ?_⟩
  simp only [FluidFlow.continuityResidual, planePoiseuilleFlow, planePoiseuilleFluid]
  rw [Time.deriv_const, zero_add]
  exact div_smul_planePoiseuilleVelocity ρ G μ H x

/-- Plane Poiseuille flow is smoothly incompressible: the velocity is differentiable and
divergence free. -/
lemma planePoiseuilleFlow_smoothIncompressible (ρ μ lam p₀ G H : ℝ) :
    FluidFlow.SmoothIncompressible 3 (planePoiseuilleFlow ρ μ lam p₀ G H).toFluidFlow := by
  exact ⟨fun t => planePoiseuilleVelocity_differentiable G μ H,
    fun t x => div_planePoiseuilleVelocity G μ H x⟩

/-- The four differentiability premises of
`FluidDynamics.navier_stokes_iff_convective_navier_stokes` hold for plane Poiseuille flow. -/
lemma planePoiseuilleFlow_navierStokes_premises (ρ μ lam p₀ G H : ℝ) :
    (∀ t x, DifferentiableAt ℝ ((planePoiseuilleFlow ρ μ lam p₀ G H).rho · x) t) ∧
      (∀ t x, DifferentiableAt ℝ ((planePoiseuilleFlow ρ μ lam p₀ G H).velocity · x) t) ∧
      (∀ t, Differentiable ℝ
        (FluidFlow.momentumDensity 3 (planePoiseuilleFlow ρ μ lam p₀ G H).toFluidFlow t)) ∧
      ∀ t, Differentiable ℝ ((planePoiseuilleFlow ρ μ lam p₀ G H).velocity t) := by
  refine ⟨fun t x => differentiableAt_const ρ, fun t x => differentiableAt_const _, fun t => ?_,
    fun t => planePoiseuilleVelocity_differentiable G μ H⟩
  unfold FluidFlow.momentumDensity
  exact (planePoiseuilleVelocity_differentiable G μ H).const_smul ρ

/-- For `μ ≠ 0` plane Poiseuille flow satisfies Physlib's convective Navier-Stokes equations
with the pressure `p₀ - G x`, shear viscosity `μ` and second viscosity `lam`. -/
lemma planePoiseuilleFlow_convectiveNavierStokes {μ : ℝ} (hμ : μ ≠ 0) (ρ lam p₀ G H : ℝ) :
    ConvectiveNavierStokes 3 (planePoiseuilleFlow ρ μ lam p₀ G H)
      (fun _ x => planePoiseuillePressure p₀ G x) (fun _ _ => μ) (fun _ _ => lam) := by
  refine ⟨FluidFlow.classicalContinuityEquation_of_smoothContinuityEquation 3 _
    (planePoiseuilleFlow_smoothContinuityEquation ρ μ lam p₀ G H), fun t x => ?_, fun t x => rfl⟩
  have hσ : (planePoiseuilleFlow ρ μ lam p₀ G H).stress t = fun y : Space =>
      !![-(p₀ - G * y 0), G * (H - 2 * y 1) / 2, 0;
        G * (H - 2 * y 1) / 2, -(p₀ - G * y 0), 0;
        0, 0, -(p₀ - G * y 0)] := by
    funext y
    exact planePoiseuilleFlow_stress hμ ρ lam p₀ G H t y
  have d0 : ∀ j, ∂[j] (fun y : Space => G * y 0 - p₀) x = if j = 0 then G else 0 := fun j =>
    deriv_comp_coord (g := fun r => G * r - p₀) 0 j
      ((((hasDerivAt_id (x 0)).const_mul G).sub_const p₀).congr_deriv (by simp))
  have d1 : ∀ j, ∂[j] (fun y : Space => G * (H - 2 * y 1) / 2) x = if j = 1 then -G else 0 :=
    fun j => deriv_comp_coord (g := fun r => G * (H - 2 * r) / 2) 1 j
      (((((hasDerivAt_id (x 1)).const_mul 2).const_sub H).const_mul G).div_const 2 |>.congr_deriv
        (by ring))
  have hu0 : ∀ k, ∂[0] (fun x' => planePoiseuilleVelocity G μ H x' k) x = 0 := fun k => by
    rw [deriv_planePoiseuilleVelocity]
    simp
  have hd := planePoiseuilleVelocity_differentiable G μ H
  have hD0 : Space.deriv 0 (planePoiseuilleVelocity G μ H) x = 0 := by
    ext k
    rw [show (Space.deriv 0 (planePoiseuilleVelocity G μ H) x).ofLp k =
        Space.deriv 0 (fun x' => planePoiseuilleVelocity G μ H x' k) x from
          (deriv_euclid hd x).symm, hu0 k]
    rfl
  rw [hσ]
  simp only [FluidFlow.materialAcceleration, FluidFlow.convectiveTerm, planePoiseuilleFlow,
    planePoiseuilleFluid, Time.deriv_const, zero_add, Fin.sum_univ_three, hD0]
  ext i
  fin_cases i <;> simp [matrixDiv_apply, Fin.sum_univ_three, d0, d1, planePoiseuilleVelocity]

/-- For `μ ≠ 0` plane Poiseuille flow satisfies Physlib's conservative Navier-Stokes equations
with the pressure `p₀ - G x`, shear viscosity `μ` and second viscosity `lam`. -/
lemma planePoiseuilleFlow_navierStokes {μ : ℝ} (hμ : μ ≠ 0) (ρ lam p₀ G H : ℝ) :
    NavierStokes 3 (planePoiseuilleFlow ρ μ lam p₀ G H)
      (fun _ x => planePoiseuillePressure p₀ G x) (fun _ _ => μ) (fun _ _ => lam) := by
  obtain ⟨h1, h2, h3, h4⟩ := planePoiseuilleFlow_navierStokes_premises ρ μ lam p₀ G H
  exact (navier_stokes_iff_convective_navier_stokes 3 _ _ _ _ h1 h2 h3 h4).mpr
    (planePoiseuilleFlow_convectiveNavierStokes hμ ρ lam p₀ G H)

/-! ## J. No-slip walls and flow rate -/

/-- No slip on the lower wall `y = 0`. -/
lemma planePoiseuilleVelocity_lower_wall (G μ H : ℝ) (x : Space) (hx : x 1 = 0) :
    planePoiseuilleVelocity G μ H x = 0 := by
  ext i
  fin_cases i <;> simp [planePoiseuilleVelocity, hx]

/-- No slip on the upper wall `y = H`. -/
lemma planePoiseuilleVelocity_upper_wall (G μ H : ℝ) (x : Space) (hx : x 1 = H) :
    planePoiseuilleVelocity G μ H x = 0 := by
  ext i
  fin_cases i <;> simp [planePoiseuilleVelocity, hx]

/-- The flow rate per unit width through any cross-section `x = s`, `z` fixed, is
`∫₀ᴴ u dy = G H³ / (12 μ)`. -/
lemma planePoiseuille_flowRate (G μ H s z : ℝ) :
    ∫ y in (0 : ℝ)..H, planePoiseuilleVelocity G μ H ⟨![s, y, z]⟩ 0 = G * H ^ 3 / (12 * μ) := by
  have hF : ∀ y ∈ Set.uIcc (0 : ℝ) H, HasDerivAt
      (fun y => G / (2 * μ) * (H * y ^ 2 / 2 - y ^ 3 / 3)) (G * y * (H - y) / (2 * μ)) y := by
    intro y _
    exact ((((hasDerivAt_pow 2 y).const_mul H).div_const 2).sub
      ((hasDerivAt_pow 3 y).div_const 3)).const_mul (G / (2 * μ)) |>.congr_deriv
        (by push_cast; ring)
  have hint : IntervalIntegrable (fun y : ℝ => G * y * (H - y) / (2 * μ))
      MeasureTheory.volume 0 H :=
    (by fun_prop : Continuous fun y : ℝ => G * y * (H - y) / (2 * μ)).intervalIntegrable 0 H
  have he : (fun y : ℝ => planePoiseuilleVelocity G μ H ⟨![s, y, z]⟩ 0) =
      fun y => G * y * (H - y) / (2 * μ) := by
    funext y
    simp [planePoiseuilleVelocity]
  rw [he, intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  ring

/-- Plane Poiseuille flow with the physical hypotheses `H, μ, ρ > 0` and `G ≠ 0`: the density is
positive, the flow is smoothly incompressible and satisfies the conservative Navier-Stokes
equations, both walls are at rest, and the flow rate per unit width is `G H³ / (12 μ) ≠ 0`. -/
lemma planePoiseuilleFlow_witness {ρ μ H G : ℝ} (lam p₀ : ℝ) (hH : 0 < H) (hμ : 0 < μ)
    (hρ : 0 < ρ) (hG : G ≠ 0) :
    (∀ t x, 0 < (planePoiseuilleFlow ρ μ lam p₀ G H).rho t x) ∧
      FluidFlow.SmoothIncompressible 3 (planePoiseuilleFlow ρ μ lam p₀ G H).toFluidFlow ∧
      NavierStokes 3 (planePoiseuilleFlow ρ μ lam p₀ G H)
        (fun _ x => planePoiseuillePressure p₀ G x) (fun _ _ => μ) (fun _ _ => lam) ∧
      (∀ t (x : Space), x 1 = 0 → (planePoiseuilleFlow ρ μ lam p₀ G H).velocity t x = 0) ∧
      (∀ t (x : Space), x 1 = H → (planePoiseuilleFlow ρ μ lam p₀ G H).velocity t x = 0) ∧
      ∀ t s z, (∫ y in (0 : ℝ)..H, (planePoiseuilleFlow ρ μ lam p₀ G H).velocity t ⟨![s, y, z]⟩ 0) =
          G * H ^ 3 / (12 * μ) ∧ G * H ^ 3 / (12 * μ) ≠ 0 := by
  refine ⟨fun t x => hρ, planePoiseuilleFlow_smoothIncompressible ρ μ lam p₀ G H,
    planePoiseuilleFlow_navierStokes hμ.ne' ρ lam p₀ G H,
    fun t x hx => planePoiseuilleVelocity_lower_wall G μ H x hx,
    fun t x hx => planePoiseuilleVelocity_upper_wall G μ H x hx, fun t s z => ⟨?_, ?_⟩⟩
  · exact planePoiseuille_flowRate G μ H s z
  · have : 0 < 12 * μ := by positivity
    exact div_ne_zero (mul_ne_zero hG (pow_ne_zero 3 hH.ne')) this.ne'

/-! ## K. No pressure gradient versus a moving wall -/

/-- No pressure gradient and stationary walls give no flow: with `G = 0` the Poiseuille velocity
vanishes everywhere, whereas plane Couette flow, also without a pressure gradient, has the
nonzero flow rate `Uwall H / 2` when its upper wall moves with speed `Uwall ≠ 0`. -/
lemma planePoiseuille_zero_gradient_vs_couette {Uwall H : ℝ} (hU : Uwall ≠ 0) (hH : 0 < H)
    (μ s z : ℝ) :
    (∀ x, planePoiseuilleVelocity 0 μ H x = 0) ∧
      (∫ y in (0 : ℝ)..H, couetteVelocity Uwall H ⟨![s, y, z]⟩ 0) = Uwall * H / 2 ∧
      Uwall * H / 2 ≠ 0 := by
  refine ⟨fun x => ?_, ?_, div_ne_zero (mul_ne_zero hU hH.ne') two_ne_zero⟩
  · ext i
    fin_cases i <;> simp [planePoiseuilleVelocity]
  · have hF : ∀ y ∈ Set.uIcc (0 : ℝ) H,
        HasDerivAt (fun y => Uwall * y ^ 2 / (2 * H)) (Uwall * y / H) y := by
      intro y _
      exact (((hasDerivAt_pow 2 y).const_mul Uwall).div_const (2 * H)).congr_deriv (by
        field_simp
        ring)
    have hint : IntervalIntegrable (fun y : ℝ => Uwall * y / H) MeasureTheory.volume 0 H :=
      (by fun_prop : Continuous fun y : ℝ => Uwall * y / H).intervalIntegrable 0 H
    have he : (fun y : ℝ => couetteVelocity Uwall H ⟨![s, y, z]⟩ 0) = fun y => Uwall * y / H := by
      funext y
      simp [couetteVelocity]
    rw [he, intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
    field_simp
    ring

end FlowCoordinateBernoulli
