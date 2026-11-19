/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.LaminarFlowPorts

/-!
# Tests for `PhyslibExt.FluidDynamics.LaminarFlowPorts`

Checked consumers:

- gradient transport for the gravitational potential;
- the circle as a streamline, in `Space` and in coordinates about an
  arbitrary origin;
- the end-to-end Bernoulli head constancy along the unit circle of
  the rotating fixture, assembling the fixture's Euler and
  body-force-potential lemmas with the streamline theorem;
- the head differing across streamlines, and the polytropic enthalpy
  not being of the form `p / ρ + e₀`.
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

end PhyslibExtTest.FluidDynamics.LaminarFlowPorts
