/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.LaminarFlowPorts
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.FluidDynamics.LaminarFlowPorts`

Checked consumers:

- gradient transport for the gravitational potential;
- the circle as a streamline, in `Space` and in coordinates about an
  arbitrary origin;
- the end-to-end Bernoulli head constancy along the unit circle of
  the rotating fixture, assembling the fixture's Euler and
  body-force-potential lemmas with the streamline theorem, and the
  corresponding constancy of Physlib's Bernoulli function for the
  thermodynamic fixture with enthalpy `p / ρ + e₀`;
- the head differing across streamlines, and the polytropic enthalpy
  not being of the form `p / ρ + e₀`;
- plane Couette flow: a nonzero shear stress and wall speed; the
  witness applied and destructured for a water-like film, with the
  smooth continuity and convective momentum results; and, for positive
  density, a Bernoulli head that is constant along each streamline but
  differs between streamlines;
- plane Poiseuille flow: the centerline velocity and the flow rate for
  `G = 12`, `μ = 1`, `H = 1`, and the witness applied and destructured
  at water-like parameters;
- cylindrical Poiseuille flow: the centerline velocity and a wall point
  at rest for `G = 4`, `μ = 1`, `R = 1`, and the witness and the
  reversed-gradient failure at water-like parameters;
- the pipe flow rate `π / 200000`, mean velocity `1 / 20`, centerline
  speed `1 / 10`, Reynolds number `1000` and laminar Darcy factor
  `8 / 125 = 64 / 1000` of a water-like pipe; the reversed flow of the
  same pipe with the same Reynolds number and the same positive Darcy
  and Fanning factors, against the negative value of an unoriented
  `V²` form; the pressure drop `8` (forward) and `-8` (reverse) given
  back by the Darcy-Weisbach loss of `PipeFrictionPorts` with the
  laminar factor over a duct of length `2`; the integrability, disk
  area and positive mean velocity of the water-like pipe; and the factor
  checks: a Reynolds number on the radius, and the Darcy and Fanning
  laws swapped, each fail at the water-like pipe.
-/

@[expose] public section

namespace PhyslibExtTest.FluidDynamics.LaminarFlowPorts

open Space Manifold FlowCoordinateBernoulli

-- The coordinate gradient of the gravitational potential is Physlib's `∇`.
example (g : ℝ) (o p : Space) :
    gradient (fun v : EuclideanSpace ℝ (Fin 3) => gravPotential g (v +ᵥ o)) (p -ᵥ o) =
      ∇ (gravPotential g) p :=
  gradient_comp_vadd _ o p

-- The circle is a streamline in `Space`, and in coordinates about any origin.
example (Ω : ℝ) :
    IsMIntegralCurveOn (I := 𝓡 3) (circle 1 Ω 0) (rotVelocity Ω) Set.univ ∧
      ∀ o : Space, IsIntegralCurveOn (fun t => circle 1 Ω 0 t -ᵥ o)
        (fun _ v => rotVelocity Ω (v +ᵥ o)) Set.univ :=
  ⟨circle_isMIntegralCurveOn 1 Ω 0, fun o => circle_isIntegralCurveOn_coord 1 Ω 0 o⟩

-- The rotating fixture is a nonzero flow when `Ω ≠ 0`.
example : rotVelocity 1 (circle 1 1 0 0) ≠ 0 :=
  rotVelocity_ne_zero one_ne_zero

/-- End-to-end: the Bernoulli head of the rotating fixture takes the
same value at times `0` and `1` on the unit circle. The fixture's
Euler and body-force-potential lemmas discharge the streamline
theorem's premises; the differentiability facts are the fixture
fields' own. -/
example {ρ Ω g : ℝ} (hρ : 0 < ρ) (t₀ : Time) :
    rotPressure ρ Ω g (circle 1 Ω 0 0) / ρ + ‖rotVelocity Ω (circle 1 Ω 0 0)‖ ^ 2 / 2 +
        gravPotential g (circle 1 Ω 0 0) =
      rotPressure ρ Ω g (circle 1 Ω 0 1) / ρ + ‖rotVelocity Ω (circle 1 Ω 0 1)‖ ^ 2 / 2 +
        gravPotential g (circle 1 Ω 0 1) := by
  have hvel : Differentiable ℝ (rotVelocity Ω) := by
    refine differentiable_euclidean.mpr fun i => ?_
    unfold rotVelocity
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, neg_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, differentiable_fun_neg_iff,
        differentiable_const] <;>
      fun_prop
  have hpd : Differentiable ℝ (rotPressure ρ Ω g) := by
    unfold rotPressure
    fun_prop
  have hgd : Differentiable ℝ (gravPotential g) := by
    unfold gravPotential
    fun_prop
  exact bernoulli_along_streamline_space (rotFlow ρ Ω g) (fun _ => rotPressure ρ Ω g)
    (gravPotential g) ρ hρ (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => hvel)
    (rotFlow_euler ρ Ω g) (rotFlow_bodyForcePotential ρ Ω g) t₀ (circle 1 Ω 0)
    isOpen_univ isPreconnected_univ (circle_isMIntegralCurveOn 1 Ω 0)
    (fun t _ => hpd _) (fun t _ => hgd _) trivial trivial

/-- The rotating fixture as a thermodynamic flow with enthalpy
`p / ρ + e₀` (constant specific internal energy `e₀`). -/
noncomputable def thermoRotFlow (ρ Ω g e₀ : ℝ) : _root_.FluidDynamics.ThermodynamicCauchyFlow 3 :=
  { rotFlow ρ Ω g with
    entropy := fun _ _ => 0
    enthalpy := fun _ x => rotPressure ρ Ω g x / ρ + e₀ }

/-- End-to-end: Physlib's Bernoulli function is constant along the
unit circle of the thermodynamic rotating fixture, assembled from
the fixture's Euler and body-force-potential lemmas. -/
example {ρ Ω g e₀ : ℝ} (hρ : 0 < ρ) (t₀ : Time) :
    _root_.FluidDynamics.bernoulliFunction 3 (thermoRotFlow ρ Ω g e₀) (gravPotential g) t₀ (circle 1 Ω 0 0) =
      _root_.FluidDynamics.bernoulliFunction 3 (thermoRotFlow ρ Ω g e₀) (gravPotential g) t₀ (circle 1 Ω 0 1) := by
  have hvel : Differentiable ℝ (rotVelocity Ω) := by
    refine differentiable_euclidean.mpr fun i => ?_
    unfold rotVelocity
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, neg_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, differentiable_fun_neg_iff,
        differentiable_const] <;>
      fun_prop
  have hpd : Differentiable ℝ (rotPressure ρ Ω g) := by
    unfold rotPressure
    fun_prop
  have hgd : Differentiable ℝ (gravPotential g) := by
    unfold gravPotential
    fun_prop
  exact bernoulliFunction_along_streamline (thermoRotFlow ρ Ω g e₀)
    (fun _ => rotPressure ρ Ω g) (gravPotential g) ρ hρ (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ => hvel) (rotFlow_euler ρ Ω g) (rotFlow_bodyForcePotential ρ Ω g) t₀ e₀
    (fun _ => rfl) (circle 1 Ω 0) isOpen_univ isPreconnected_univ
    (circle_isMIntegralCurveOn 1 Ω 0) (fun t _ => hpd _) (fun t _ => hgd _) trivial trivial

-- The head differs across streamlines (unit circle vs radius two),
-- and a polytropic enthalpy is not of the form `p / ρ + e₀`.
example {ρ Ω g : ℝ} (hρ : 0 < ρ) (hΩ : Ω ≠ 0) (hg : g ≠ 0) :
    (rotPressure ρ Ω g (circle 1 Ω 0 0) / ρ + ‖rotVelocity Ω (circle 1 Ω 0 0)‖ ^ 2 / 2 +
        gravPotential g (circle 1 Ω 0 0) ≠
      rotPressure ρ Ω g (circle 2 Ω 0 0) / ρ + ‖rotVelocity Ω (circle 2 Ω 0 0)‖ ^ 2 / 2 +
        gravPotential g (circle 2 Ω 0 0)) ∧
      ¬ ∃ e₀ : ℝ, ∀ t x,
        (polytropicFlow ρ Ω g).enthalpy t x = rotPressure ρ Ω g x / ρ + e₀ :=
  ⟨rot_head_differs_across_streamlines hρ hΩ, polytropic_enthalpy_not_pOverRho hρ hg⟩

/-- Nonzero shear and wall speed: with `μ = 3`, `Uwall = 2` and `H = 1` the shear stress is `6`
everywhere, and the upper wall point `(0, 1, 0)` moves with velocity `(2, 0, 0)`. -/
example (ρ lam p₀ : ℝ) (t : Time) (x : Space) :
    (couetteFlow ρ 3 lam p₀ 2 1).stress t x 0 1 = 6 ∧
      couetteVelocity 2 1 ⟨![0, 1, 0]⟩ = WithLp.toLp 2 ![2, 0, 0] := by
  refine ⟨?_, ?_⟩
  · rw [couetteFlow_stress]
    norm_num
  · ext i
    fin_cases i <;> simp [couetteVelocity]

/-- End-to-end consumer of the plane Couette witness at concrete positive parameters: a
water-like film with `ρ = 1000`, `μ = 1 / 1000`, `lam = 0`, `p₀ = 100000`, wall speed `Uwall = 1`
and gap `H = 1 / 1000`. Applying and destructuring `couetteFlow_witness` gives a positive density
and a vanishing incompressibility residual at the mid-gap point `y = 1 / 2000`, the conservative
momentum balance, both wall velocities and a nonzero shear stress there; the smooth continuity
equation gives a vanishing continuity residual at the same point, and the convective momentum
balance holds too. -/
example (t : Time) :
    0 < (couetteFlow 1000 (1 / 1000) 0 100000 1 (1 / 1000)).rho t ⟨![0, 1 / 2000, 0]⟩ ∧
      _root_.FluidDynamics.FluidFlow.continuityResidual 3
        (couetteFlow 1000 (1 / 1000) 0 100000 1 (1 / 1000)).toFluidFlow t ⟨![0, 1 / 2000, 0]⟩ =
          0 ∧
      _root_.FluidDynamics.FluidFlow.incompressibilityResidual 3
        (couetteFlow 1000 (1 / 1000) 0 100000 1 (1 / 1000)).toFluidFlow t ⟨![0, 1 / 2000, 0]⟩ =
          0 ∧
      _root_.FluidDynamics.CauchyFlow.CauchyMomentumEquation 3
        (couetteFlow 1000 (1 / 1000) 0 100000 1 (1 / 1000)) ∧
      _root_.FluidDynamics.CauchyFlow.ConvectiveCauchyMomentumEquation 3
        (couetteFlow 1000 (1 / 1000) 0 100000 1 (1 / 1000)) ∧
      (couetteFlow 1000 (1 / 1000) 0 100000 1 (1 / 1000)).velocity t ⟨![0, 0, 0]⟩ = 0 ∧
      (couetteFlow 1000 (1 / 1000) 0 100000 1 (1 / 1000)).velocity t ⟨![0, 1 / 1000, 0]⟩ =
        WithLp.toLp 2 ![1, 0, 0] ∧
      (couetteFlow 1000 (1 / 1000) 0 100000 1 (1 / 1000)).stress t ⟨![0, 1 / 2000, 0]⟩ 0 1 ≠
        0 := by
  obtain ⟨hρ, hinc, hNS, hlow, hup, hshear⟩ := couetteFlow_witness (ρ := 1000) (μ := 1 / 1000)
    (H := 1 / 1000) (Uwall := 1) 0 100000 (by norm_num) (by norm_num) (by norm_num) one_ne_zero
  exact ⟨hρ t _,
    (couetteFlow_smoothContinuityEquation 1000 (1 / 1000) 0 100000 1 (1 / 1000)).2.2 t _,
    hinc.2 t _, hNS.2.1,
    (couetteFlow_convectiveNavierStokes 1000 (1 / 1000) 0 100000 1 (1 / 1000)).2.1,
    hlow t _ rfl, hup t _ rfl, hshear t _⟩

/-- The Bernoulli head varies across streamlines. For `Uwall = H = 2`, so `u = (y, 0, 0)` on the
channel `0 ≤ y ≤ 2`, and a positive density `ρ`, the head `p₀ / ρ + ‖u‖² / 2` is `p₀ / ρ + 1/2`
all along the streamline `y = 1, z = 0` and `p₀ / ρ + 2` all along the streamline `y = 2, z = 0`
(the moving wall), and the total pressure `p₀ + ρ ‖u‖² / 2` is larger on the second. The head is
constant along each streamline but not across them, so no global Bernoulli constant follows. -/
example (ρ p₀ s : ℝ) (hρ : 0 < ρ) :
    p₀ / ρ + ‖couetteVelocity 2 2 ⟨![s, 1, 0]⟩‖ ^ 2 / 2 = p₀ / ρ + 1 / 2 ∧
      p₀ / ρ + ‖couetteVelocity 2 2 ⟨![s, 2, 0]⟩‖ ^ 2 / 2 = p₀ / ρ + 2 ∧
      p₀ + ρ * ‖couetteVelocity 2 2 ⟨![s, 1, 0]⟩‖ ^ 2 / 2 <
        p₀ + ρ * ‖couetteVelocity 2 2 ⟨![s, 2, 0]⟩‖ ^ 2 / 2 := by
  have h1 : ‖couetteVelocity 2 2 ⟨![s, 1, 0]⟩‖ ^ 2 = 1 := by
    norm_num [couetteVelocity, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  have h2 : ‖couetteVelocity 2 2 ⟨![s, 2, 0]⟩‖ ^ 2 = 4 := by
    norm_num [couetteVelocity, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  rw [h1, h2]
  exact ⟨by ring, by ring, by linarith⟩

/-- Nonzero throughput: with `G = 12`, `μ = 1` and `H = 1` the centerline velocity at `y = 1/2`
is `(3/2, 0, 0)` and the flow rate per unit width is `1`. -/
example (s z : ℝ) :
    planePoiseuilleVelocity 12 1 1 ⟨![s, 1 / 2, z]⟩ = WithLp.toLp 2 ![3 / 2, 0, 0] ∧
      ∫ y in (0 : ℝ)..1, planePoiseuilleVelocity 12 1 1 ⟨![s, y, z]⟩ 0 = 1 := by
  refine ⟨?_, ?_⟩
  · ext i
    fin_cases i <;> norm_num [planePoiseuilleVelocity]
  · rw [planePoiseuille_flowRate]
    norm_num

/-- Plane Poiseuille witness at water-like parameters: `ρ = 1000`, `μ = 1/1000`, gap
`H = 1/100` and `G = 12`. Applying and destructuring `planePoiseuilleFlow_witness` gives the
conservative momentum balance, the two wall velocities and the flow rate `1/1000` per unit
width. -/
example (lam p₀ : ℝ) (t : Time) :
    _root_.FluidDynamics.NavierStokes 3 (planePoiseuilleFlow 1000 (1 / 1000) lam p₀ 12 (1 / 100))
        (fun _ x => planePoiseuillePressure p₀ 12 x) (fun _ _ => 1 / 1000) (fun _ _ => lam) ∧
      (planePoiseuilleFlow 1000 (1 / 1000) lam p₀ 12 (1 / 100)).velocity t ⟨![0, 0, 0]⟩ = 0 ∧
      (planePoiseuilleFlow 1000 (1 / 1000) lam p₀ 12 (1 / 100)).velocity t ⟨![0, 1 / 100, 0]⟩ =
        0 ∧
      (∫ y in (0 : ℝ)..(1 / 100),
        (planePoiseuilleFlow 1000 (1 / 1000) lam p₀ 12 (1 / 100)).velocity t ⟨![0, y, 0]⟩ 0) =
        1 / 1000 := by
  obtain ⟨-, -, hNS, h0, hH, hQ⟩ := planePoiseuilleFlow_witness (ρ := 1000) (μ := 1 / 1000)
    (H := 1 / 100) (G := 12) lam p₀ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hNS, h0 t _ rfl, hH t _ rfl, ?_⟩
  rw [(hQ t 0 0).1]
  norm_num

/-- Nonzero `G` and positive centerline flow: with `G = 4`, `μ = 1` and `R = 1` the centerline
velocity is `(0, 0, 1)` and the wall point `(1, 0, z)` is at rest. -/
example (z : ℝ) :
    pipePoiseuilleVelocity 4 1 1 ⟨![0, 0, z]⟩ = WithLp.toLp 2 ![0, 0, 1] ∧
      pipePoiseuilleVelocity 4 1 1 ⟨![1, 0, z]⟩ = 0 := by
  refine ⟨?_, ?_⟩
  · ext i
    fin_cases i <;> norm_num [pipePoiseuilleVelocity]
  · ext i
    fin_cases i <;> norm_num [pipePoiseuilleVelocity]

/-- Cylindrical Poiseuille witness for a water-like pipe: `ρ = 1000`, `μ = 1/1000`, radius
`R = 1/100` and `G = 4`. Applying and destructuring `pipePoiseuilleFlow_witness` gives the
conservative momentum balance, a wall point at rest and the centerline velocity `(0, 0, 1/10)`;
with the pressure gradient reversed the same velocity is not a Navier-Stokes solution. -/
example (lam p₀ : ℝ) (t : Time) :
    _root_.FluidDynamics.NavierStokes 3 (pipePoiseuilleFlow 1000 (1 / 1000) lam p₀ 4 (1 / 100))
        (fun _ x => pipePoiseuillePressure p₀ 4 x) (fun _ _ => 1 / 1000) (fun _ _ => lam) ∧
      (pipePoiseuilleFlow 1000 (1 / 1000) lam p₀ 4 (1 / 100)).velocity t ⟨![1 / 100, 0, 0]⟩ = 0 ∧
      (pipePoiseuilleFlow 1000 (1 / 1000) lam p₀ 4 (1 / 100)).velocity t ⟨![0, 0, 0]⟩ =
        WithLp.toLp 2 ![0, 0, 1 / 10] ∧
      ¬ _root_.FluidDynamics.NavierStokes 3 (pipeReversedFlow 1000 (1 / 1000) lam p₀ 4 (1 / 100))
        (fun _ x => pipePoiseuillePressure p₀ (-4) x) (fun _ _ => 1 / 1000) (fun _ _ => lam) := by
  obtain ⟨-, -, -, hNS, hwall, hc⟩ := pipePoiseuilleFlow_witness (ρ := 1000) (μ := 1 / 1000)
    (G := 4) (R := 1 / 100) lam p₀ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hNS, hwall t _ (by norm_num), ?_, pipeReversedFlow_not_navierStokes (by norm_num)
    (by norm_num) 1000 lam p₀ (1 / 100)⟩
  rw [(hc t 0).1]
  norm_num

section PipeFlowRate

open Real EngineeringScaling _root_.FluidDynamics.PipeFrictionPorts

/-- **Water-like fixture.** A pipe of radius `1 / 100` carrying a fluid of viscosity `1 / 1000`
and density `1000` under the pressure-drop rate `G = 4`: flow rate `π / 200000`, mean velocity
`1 / 20`, centerline speed `1 / 10 = 2 (1 / 20)`, Reynolds number `1000` on the diameter and
Darcy factor `8 / 125 = 64 / 1000` over the length `1`. -/
lemma pipe_fixture (z : ℝ) :
    pipeFlowRate 4 (1 / 1000) (1 / 100) z = π / 200000 ∧
      pipeMeanVelocity 4 (1 / 1000) (1 / 100) z = 1 / 20 ∧
      pipePoiseuilleVelocity 4 (1 / 1000) (1 / 100) (crossSectionPoint z (0, 0)) 2 = 1 / 10 ∧
      reynoldsNumber ⟨1000⟩ ⟨pipeMeanVelocity 4 (1 / 1000) (1 / 100) z⟩ ⟨2 * (1 / 100)⟩
        ⟨1 / 1000⟩ (by norm_num) = 1000 ∧
      darcyFactorOfDrop (4 * 1) 1 (2 * (1 / 100)) 1000
        (pipeMeanVelocity 4 (1 / 1000) (1 / 100) z) (by norm_num) (by norm_num) (by norm_num)
        (pipe_drop_mul_meanVelocity_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) z) =
        8 / 125 := by
  have hV : pipeMeanVelocity 4 (1 / 1000) (1 / 100) z = 1 / 20 := by
    rw [pipeMeanVelocity_eq (by norm_num) (by norm_num)]
    norm_num
  refine ⟨by rw [pipeFlowRate_eq (by norm_num) (by norm_num)]; ring, hV, ?_, ?_, ?_⟩
  · rw [pipeCenterline_eq_two_mul_meanVelocity (by norm_num) (by norm_num), hV]
    norm_num
  · rw [reynoldsNumber_val]
    simp only [hV]
    norm_num
  · rw [darcyFactorOfDrop, hV]
    norm_num

-- Reverse flow: with `G = -4` (the pressure rises along `x 2`) the same pipe carries the flow
-- rate `-π / 200000` at the nonzero mean velocity `-1 / 20`, so the oriented pressure drop
-- `G L = -4` over the length `1` has the direction of the flow (`pipe_drop_mul_meanVelocity_pos`
-- discharges `0 < Δp V`). The Reynolds number on the speed `|V|` is still `1000`, and by
-- `pipe_darcyFactor_eq` and `pipe_fanningFactor_eq` at `G = -4` the Darcy factor is the positive
-- `8 / 125 = 64 / 1000` and the Fanning factor is `2 / 125 = 16 / 1000`.
example :
    pipeFlowRate (-4) (1 / 1000) (1 / 100) 0 = -(π / 200000) ∧
      pipeMeanVelocity (-4) (1 / 1000) (1 / 100) 0 = -(1 / 20) ∧
      pipeMeanVelocity (-4) (1 / 1000) (1 / 100) 0 ≠ 0 ∧
      reynoldsNumber ⟨1000⟩ ⟨pipeMeanVelocity (-4) (1 / 1000) (1 / 100) 0⟩ ⟨2 * (1 / 100)⟩
        ⟨1 / 1000⟩ (by norm_num) = 1000 ∧
      darcyFactorOfDrop (-4 * 1) 1 (2 * (1 / 100)) 1000
          (pipeMeanVelocity (-4) (1 / 1000) (1 / 100) 0) (by norm_num) (by norm_num) (by norm_num)
          (pipe_drop_mul_meanVelocity_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            0) = 8 / 125 ∧
      darcyFactorOfDrop (-4 * 1) 1 (2 * (1 / 100)) 1000
          (pipeMeanVelocity (-4) (1 / 1000) (1 / 100) 0) (by norm_num) (by norm_num) (by norm_num)
          (pipe_drop_mul_meanVelocity_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            0) / 4 =
        2 / 125 := by
  have hV : pipeMeanVelocity (-4) (1 / 1000) (1 / 100) 0 = -(1 / 20) := by
    rw [pipeMeanVelocity_eq (by norm_num) (by norm_num)]
    norm_num
  have hRe : reynoldsNumber ⟨1000⟩ ⟨pipeMeanVelocity (-4) (1 / 1000) (1 / 100) 0⟩
      ⟨2 * (1 / 100)⟩ ⟨1 / 1000⟩ (by norm_num) = 1000 := by
    rw [reynoldsNumber_val]
    simp only [hV]
    norm_num
  have hf := pipe_darcyFactor_eq (ρ := 1000) (μ := 1 / 1000) (G := -4) (R := 1 / 100) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  have hF := pipe_fanningFactor_eq (ρ := 1000) (μ := 1 / 1000) (G := -4) (R := 1 / 100) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  rw [hRe] at hf hF
  refine ⟨by rw [pipeFlowRate_eq (by norm_num) (by norm_num)]; ring, hV,
    pipeMeanVelocity_ne_zero (by norm_num) (by norm_num) (by norm_num) 0, hRe, ?_, ?_⟩
  · rw [hf]
    norm_num
  · rw [hF]
    norm_num

-- An unoriented form `2 D Δp / (ρ V² L)` would give the reversed flow the negative value
-- `-8 / 125`.
example :
    2 * (2 * (1 / 100)) * (-4 * 1) /
        (1000 * pipeMeanVelocity (-4) (1 / 1000) (1 / 100) 0 ^ 2 * 1) = (-8 / 125 : ℝ) := by
  rw [pipeMeanVelocity_eq (by norm_num) (by norm_num)]
  norm_num

-- With the laminar factor `64 / Re`, the Darcy-Weisbach loss of `PipeFrictionPorts` over a duct of
-- length `2` gives back the pressure drop `G L`: `8` for the forward flow `G = 4` of the
-- water-like pipe and `-8` for the reversed flow `G = -4`.
example :
    _root_.FluidDynamics.PipeFrictionPorts.frictionPressureDrop
        (_root_.FluidDynamics.PipeFrictionPorts.darcyCoefficient
          (64 / reynoldsNumber ⟨1000⟩ ⟨pipeMeanVelocity 4 (1 / 1000) (1 / 100) 0⟩
            ⟨2 * (1 / 100)⟩ ⟨1 / 1000⟩ (by norm_num)) 2 (2 * (1 / 100)) (π * (1 / 100) ^ 2)
          1000) (pipeFlowRate 4 (1 / 1000) (1 / 100) 0) = 8 ∧
      _root_.FluidDynamics.PipeFrictionPorts.frictionPressureDrop
        (_root_.FluidDynamics.PipeFrictionPorts.darcyCoefficient
          (64 / reynoldsNumber ⟨1000⟩ ⟨pipeMeanVelocity (-4) (1 / 1000) (1 / 100) 0⟩
            ⟨2 * (1 / 100)⟩ ⟨1 / 1000⟩ (by norm_num)) 2 (2 * (1 / 100)) (π * (1 / 100) ^ 2)
          1000) (pipeFlowRate (-4) (1 / 1000) (1 / 100) 0) = -8 := by
  obtain ⟨h1, -⟩ := pipe_frictionPressureDrop_eq (ρ := 1000) (μ := 1 / 1000) (R := 1 / 100)
    (G := 4) (L := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  obtain ⟨h2, -⟩ := pipe_frictionPressureDrop_eq (ρ := 1000) (μ := 1 / 1000) (R := 1 / 100)
    (G := -4) (L := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  exact ⟨h1.trans (by norm_num), h2.trans (by norm_num)⟩

open MeasureTheory in
-- The water-like pipe: the disk-restricted axial velocity is integrable, the pipe disk of radius
-- `1 / 100` has area `π / 10000`, and the mean velocity is positive.
example :
    Integrable (pipeAxialFlux 4 (1 / 1000) (1 / 100) 0) ∧
      volume.real (pipeDisk (1 / 100)) = π / 10000 ∧
      0 < pipeMeanVelocity 4 (1 / 1000) (1 / 100) 0 := by
  refine ⟨integrable_pipeAxialFlux 4 (1 / 1000) (1 / 100) 0, ?_,
    pipeMeanVelocity_pos (by norm_num) (by norm_num) (by norm_num) 0⟩
  rw [pipeDisk_measureReal (by norm_num)]
  ring

-- Factor check, Reynolds number on the radius: at the water-like pipe (Darcy factor `8 / 125`)
-- the Reynolds number `500` on the radius gives `64 / 500 = 16 / 125`, not the Darcy factor.
example :
    darcyFactorOfDrop (4 * 1) 1 (2 * (1 / 100)) 1000
        (pipeMeanVelocity 4 (1 / 1000) (1 / 100) 0) (by norm_num) (by norm_num) (by norm_num)
        (pipe_drop_mul_meanVelocity_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          0) ≠
      64 / reynoldsNumber ⟨1000⟩ ⟨pipeMeanVelocity 4 (1 / 1000) (1 / 100) 0⟩ ⟨1 / 100⟩
        ⟨1 / 1000⟩ (by norm_num) := by
  obtain ⟨-, hV, -, -, hf⟩ := pipe_fixture 0
  rw [hf, reynoldsNumber_val]
  simp only [hV]
  norm_num

-- Factor check, Darcy law read as Fanning: the Fanning factor `2 / 125` is not
-- `64 / Re = 8 / 125`.
example :
    darcyFactorOfDrop (4 * 1) 1 (2 * (1 / 100)) 1000
        (pipeMeanVelocity 4 (1 / 1000) (1 / 100) 0) (by norm_num) (by norm_num) (by norm_num)
        (pipe_drop_mul_meanVelocity_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          0) / 4 ≠
      64 / reynoldsNumber ⟨1000⟩ ⟨pipeMeanVelocity 4 (1 / 1000) (1 / 100) 0⟩ ⟨2 * (1 / 100)⟩
        ⟨1 / 1000⟩ (by norm_num) := by
  obtain ⟨-, -, -, hRe, hf⟩ := pipe_fixture 0
  rw [hf, hRe]
  norm_num

-- Factor check, Fanning law read as Darcy: the Darcy factor `8 / 125` is not
-- `16 / Re = 2 / 125`.
example :
    darcyFactorOfDrop (4 * 1) 1 (2 * (1 / 100)) 1000
        (pipeMeanVelocity 4 (1 / 1000) (1 / 100) 0) (by norm_num) (by norm_num) (by norm_num)
        (pipe_drop_mul_meanVelocity_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          0) ≠
      16 / reynoldsNumber ⟨1000⟩ ⟨pipeMeanVelocity 4 (1 / 1000) (1 / 100) 0⟩ ⟨2 * (1 / 100)⟩
        ⟨1 / 1000⟩ (by norm_num) := by
  obtain ⟨-, -, -, hRe, hf⟩ := pipe_fixture 0
  rw [hf, hRe]
  norm_num

end PipeFlowRate

end PhyslibExtTest.FluidDynamics.LaminarFlowPorts
