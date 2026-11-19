/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.ScalarShockPorts
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Tests for `PhyslibExt.FluidDynamics.ScalarShockPorts`

Checked consumers, each discharging the transport input with `movingJumpTransport_holds`:

- the Burgers front with states `2 | 0` moving at speed `1` conserves mass on `[-1, 1]`;
- the same states with a stationary front do not: the incorrect speed leaves the nonzero
  interface residual `0 * (0 - 2) - (0 ^ 2 / 2 - 2 ^ 2 / 2) = 2`.
- the weak-residual formula of the straight moving step, for any admissible test;
- non-vacuity of the test hypotheses: a smooth bump on the plane with value `1` at the origin
  meets them, and for it the Burgers step `2 | 0` has zero residual at speed `1` and residual
  `2 * ∫ φ (t, 0) dt` at the incorrect speed `0`.
-/

@[expose] public section

namespace PhyslibExtTest.FluidDynamics.ScalarShockPorts

open ScalarShock

-- The transport input holds.
example : MovingJumpTransport := movingJumpTransport_holds

/-- Burgers flux `u ^ 2 / 2`, states `2 | 0`, front `x = τ` (speed `1`): the mass on `[-1, 1]`
changes at the conservation rate `f 2 - f 0` at time `0`. -/
example :
    HasDerivAt (fun τ : ℝ => (∫ _x in (-1 : ℝ)..τ, (2 : ℝ)) + (∫ _x in τ..(1 : ℝ), (0 : ℝ)))
      ((2 : ℝ) ^ 2 / 2 - (0 : ℝ) ^ 2 / 2) 0 := by
  have key := conservation_iff_rankineHugoniot (f := fun u : ℝ => u ^ 2 / 2)
    (uL := fun _ _ => 2) (uR := fun _ _ => 0) (vL := fun _ _ => 0) (vR := fun _ _ => 0)
    (gL := fun _ => 0) (gR := fun _ => 0) (s := fun τ => τ) (c := 1) (a := -1) (b := 1)
    (t := 0) (UL := Set.univ) (UR := Set.univ) movingJumpTransport_holds (hasDerivAt_id' 0)
    (by norm_num) (by norm_num) isOpen_univ (Set.subset_univ _) continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) continuousOn_const continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp)
    isOpen_univ (Set.subset_univ _) continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) continuousOn_const continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp)
  exact key.mpr (by norm_num)

/-- The same states with a stationary front (speed `0`) do not conserve mass on `[-1, 1]`: the
Rankine-Hugoniot identity `0 * (0 - 2) = 0 ^ 2 / 2 - 2 ^ 2 / 2` fails. -/
example :
    ¬ HasDerivAt
      (fun _τ : ℝ => (∫ _x in (-1 : ℝ)..(0 : ℝ), (2 : ℝ)) + (∫ _x in (0 : ℝ)..(1 : ℝ), (0 : ℝ)))
      ((2 : ℝ) ^ 2 / 2 - (0 : ℝ) ^ 2 / 2) 0 := by
  have key := conservation_iff_rankineHugoniot (f := fun u : ℝ => u ^ 2 / 2)
    (uL := fun _ _ => 2) (uR := fun _ _ => 0) (vL := fun _ _ => 0) (vR := fun _ _ => 0)
    (gL := fun _ => 0) (gR := fun _ => 0) (s := fun _ => 0) (c := 0) (a := -1) (b := 1)
    (t := 0) (UL := Set.univ) (UR := Set.univ) movingJumpTransport_holds (hasDerivAt_const 0 0)
    (by norm_num) (by norm_num) isOpen_univ (Set.subset_univ _) continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) continuousOn_const continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp)
    isOpen_univ (Set.subset_univ _) continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) continuousOn_const continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp)
  intro h
  have hRH := key.mp h
  norm_num at hRH

open scoped ContDiff

-- The weak-residual formula of the straight moving step, with the transport input discharged.
example {f : ℝ → ℝ} {uL uR c T0 T1 X0 X1 : ℝ} {φ φt φx : ℝ → ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2))
    (hφt : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t)
    (hφx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x)
    (hsupp : Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆
      Set.Icc T0 T1 ×ˢ Set.Icc X0 X1) :
    weakResidual f (movingStep uL uR c) φt φx =
      -((f uR - f uL) - c * (uR - uL)) * ∫ t : ℝ, φ t (c * t) :=
  weakResidual_movingStep movingJumpTransport_holds hφ hφt hφx hsupp

/-- Non-vacuity and a concrete consumer: a smooth bump on the plane with value `1` at the
origin, vanishing outside `[-1, 1] × [-1, 1]`, meets the test hypotheses; for it the Burgers
step `2 | 0` has zero residual at speed `1` and residual `2 * ∫ φ (t, 0) dt` at the incorrect
speed `0`. -/
example : ∃ φ φt φx : ℝ → ℝ → ℝ,
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2) ∧
    (∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t) ∧
    (∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x) ∧
    Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆ Set.Icc (-1) 1 ×ˢ Set.Icc (-1) 1 ∧
    φ 0 0 = 1 ∧
    weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 1) φt φx = 0 ∧
    weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 0) φt φx =
      2 * ∫ t : ℝ, φ t 0 := by
  let b : ContDiffBump (0 : ℝ × ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hb : Differentiable ℝ (fun p : ℝ × ℝ => b p) :=
    (b.contDiff (n := 1)).differentiable one_ne_zero
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => b (p.1, p.2)) := b.contDiff
  have hφt : ∀ t x : ℝ,
      HasDerivAt (fun τ : ℝ => b (τ, x)) (deriv (fun τ : ℝ => b (τ, x)) t) t :=
    fun t x => ((hb.comp (differentiable_id.prodMk (differentiable_const x))) t).hasDerivAt
  have hφx : ∀ t x : ℝ,
      HasDerivAt (fun y : ℝ => b (t, y)) (deriv (fun y : ℝ => b (t, y)) x) x :=
    fun t x => ((hb.comp ((differentiable_const t).prodMk differentiable_id)) x).hasDerivAt
  have hsupp : Function.support (fun p : ℝ × ℝ => b (p.1, p.2)) ⊆
      Set.Icc (-1) 1 ×ˢ Set.Icc (-1) 1 := by
    intro p hp
    have hp' : p ∈ Function.support b := hp
    rw [b.support_eq, Metric.mem_ball, dist_zero_right, Prod.norm_def] at hp'
    have h1 : ‖p.1‖ < 1 := lt_of_le_of_lt (le_max_left _ _) hp'
    have h2 : ‖p.2‖ < 1 := lt_of_le_of_lt (le_max_right _ _) hp'
    rw [Real.norm_eq_abs, abs_lt] at h1 h2
    exact ⟨⟨h1.1.le, h1.2.le⟩, ⟨h2.1.le, h2.2.le⟩⟩
  obtain ⟨hres1, hres0⟩ :=
    burgers_step_two_zero_weakResidual movingJumpTransport_holds hφ hφt hφx hsupp
  refine ⟨fun t x => b (t, x), fun t x => deriv (fun τ : ℝ => b (τ, x)) t,
    fun t x => deriv (fun y : ℝ => b (t, y)) x, hφ, hφt, hφx, hsupp, ?_, hres1, hres0⟩
  exact b.one_of_mem_closedBall (by simp [b])

end PhyslibExtTest.FluidDynamics.ScalarShockPorts
