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

Checked consumers:

- the Burgers front with states `2 | 0` moving at speed `1` conserves mass on `[-1, 1]`;
- the same states with a stationary front do not: the incorrect speed leaves the nonzero
  interface residual `0 * (0 - 2) - (0 ^ 2 / 2 - 2 ^ 2 / 2) = 2`.
- the weak-residual formula of the straight moving step, for any admissible test;
- non-vacuity of the test hypotheses: a smooth bump on the plane with value `1` at the origin
  meets them, and for it the Burgers step `2 | 0` has zero residual at speed `1` and residual
  `2 * ∫ φ (t, 0) dt` at the incorrect speed `0`;
- an interface test built from any two bumps is admissible, so the residual formula applies to it
  with the integral of the time bump along the front;
- a concrete interface test vanishes outside `[-1, 1] × [-3, 3]`, equals `1` at the origin and has
  positive integral along the front;
- against an interface test on its own front, the Burgers step `2 | 0` moving at speed `c` has
  zero residual exactly when `c = 1`;
- the Burgers fixture for interface tests: zero residual at speed `1`, the positive residual
  `2 * ∫ β` at speed `0`;
- the weak jump equivalence for the Burgers step `2 | 0`: at speed `1` every admissible test gives
  zero residual; at speed `0` the zero test still does, but not every admissible test does.
- the Burgers front `2 | 0` conserves mass exactly at its Rankine-Hugoniot speed `1` (and not
  when stationary), through the Burgers conservation-speed equivalence;
- a decreasing jump `3 | 1` at speed `2` has production `-2 / 3 ≤ 0` and speed between the
  states, and an expansion jump `-1 | 1` at speed `0` satisfies the jump identity but has positive
  production.
-/

@[expose] public section

namespace PhyslibExtTest.FluidDynamics.ScalarShockPorts

open ScalarShock

/-- Burgers flux `u ^ 2 / 2`, states `2 | 0`, front `x = τ` (speed `1`): the mass on `[-1, 1]`
changes at the conservation rate `f 2 - f 0` at time `0`. -/
example :
    HasDerivAt (fun τ : ℝ => (∫ _x in (-1 : ℝ)..τ, (2 : ℝ)) + (∫ _x in τ..(1 : ℝ), (0 : ℝ)))
      ((2 : ℝ) ^ 2 / 2 - (0 : ℝ) ^ 2 / 2) 0 := by
  have key := conservation_iff_rankineHugoniot (f := fun u : ℝ => u ^ 2 / 2)
    (uL := fun _ _ => 2) (uR := fun _ _ => 0) (vL := fun _ _ => 0) (vR := fun _ _ => 0)
    (gL := fun _ => 0) (gR := fun _ => 0) (s := fun τ => τ) (c := 1) (a := -1) (b := 1)
    (t := 0) (UL := Set.univ) (UR := Set.univ) (hasDerivAt_id' 0)
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
    (t := 0) (UL := Set.univ) (UR := Set.univ) (hasDerivAt_const 0 0)
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

-- The weak-residual formula of the straight moving step, for an arbitrary admissible test.
example {f : ℝ → ℝ} {uL uR c T0 T1 X0 X1 : ℝ} {φ φt φx : ℝ → ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2))
    (hφt : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t)
    (hφx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x)
    (hsupp : Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆
      Set.Icc T0 T1 ×ˢ Set.Icc X0 X1) :
    weakResidual f (movingStep uL uR c) φt φx =
      -((f uR - f uL) - c * (uR - uL)) * ∫ t : ℝ, φ t (c * t) :=
  weakResidual_movingStep hφ hφt hφx hsupp

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
    burgers_step_two_zero_weakResidual hφ hφt hφx hsupp
  refine ⟨fun t x => b (t, x), fun t x => deriv (fun τ : ℝ => b (τ, x)) t,
    fun t x => deriv (fun y : ℝ => b (t, y)) x, hφ, hφt, hφx, hsupp, ?_, hres1, hres0⟩
  exact b.one_of_mem_closedBall (by simp [b])

/-- An interface test built from any two bumps is an admissible test, so the residual formula
applies to it, with the integral of the time bump along the front. -/
example {f : ℝ → ℝ} {uL uR c t₀ : ℝ} (β : ContDiffBump t₀) (θ : ContDiffBump (0 : ℝ)) :
    weakResidual f (movingStep uL uR c) (interfaceTestDt β θ c) (interfaceTestDx β θ c) =
      -((f uR - f uL) - c * (uR - uL)) * ∫ t : ℝ, β t := by
  rw [weakResidual_movingStep (contDiff_interfaceTest β θ c)
    (hasDerivAt_interfaceTest_time β θ c) (hasDerivAt_interfaceTest_space β θ c)
    (support_interfaceTest_subset β θ c)]
  congr 2
  funext t
  exact (interfaceTest_trace β θ c).1 t

/-- A concrete interface test: the bump `⟨1 / 2, 1⟩` around `0`, in time and across the front
`x = 2 * t`, vanishes outside `[-1, 1] × [-3, 3]`, equals `1` at the origin and has positive
integral along the front. -/
example :
    let β : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
    Function.support (fun p : ℝ × ℝ => interfaceTest β β 2 p.1 p.2) ⊆
        Set.Icc (-1) 1 ×ˢ Set.Icc (-3) 3 ∧
      interfaceTest β β 2 0 0 = 1 ∧ 0 < ∫ t : ℝ, interfaceTest β β 2 t (2 * t) := by
  intro β
  have hsupp := support_interfaceTest_subset β β 2
  have hβ : β.rOut = 1 := rfl
  have hX : |(2 : ℝ)| * (|(0 : ℝ)| + 1) + 1 = 3 := by norm_num
  rw [hβ, hX, zero_sub, zero_add] at hsupp
  refine ⟨hsupp, ?_, integral_interfaceTest_trace_pos β β 2⟩
  have h := (interfaceTest_trace β β 2).1 0
  rw [mul_zero] at h
  rw [h]
  exact β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)

/-- Against an interface test on its own front, the Burgers step `2 | 0` moving at speed `c` has
zero residual exactly at the Rankine-Hugoniot speed `c = 1`. -/
example {t₀ c : ℝ} (β : ContDiffBump t₀) (θ : ContDiffBump (0 : ℝ)) :
    weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 c) (interfaceTestDt β θ c)
        (interfaceTestDx β θ c) = 0 ↔ c = 1 := by
  rw [weakResidual_movingStep_eq_zero_iff_of_trace_ne_zero (contDiff_interfaceTest β θ c)
    (hasDerivAt_interfaceTest_time β θ c) (hasDerivAt_interfaceTest_space β θ c)
    (support_interfaceTest_subset β θ c) (integral_interfaceTest_trace_pos β θ c).ne']
  constructor <;> intro h <;> linarith

/-- The Burgers fixture for interface tests on the stationary front: zero residual at the
Rankine-Hugoniot speed `1`, the positive residual `2 * ∫ β` at the incorrect speed `0`. -/
example {t₀ : ℝ} (β : ContDiffBump t₀) (θ : ContDiffBump (0 : ℝ)) :
    weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 1) (interfaceTestDt β θ 0)
        (interfaceTestDx β θ 0) = 0 ∧
      weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 0) (interfaceTestDt β θ 0)
        (interfaceTestDx β θ 0) = 2 * ∫ t : ℝ, β t ∧
      0 < weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 0) (interfaceTestDt β θ 0)
        (interfaceTestDx β θ 0) :=
  burgers_step_two_zero_interfaceTest β θ

/-- The weak jump equivalence for the Burgers step `2 | 0`: at the Rankine-Hugoniot speed `1`
every admissible test gives zero residual; at the incorrect speed `0` some admissible test (the
zero test) still gives zero residual, but not every admissible test does. -/
example :
    (∀ (φ φt φx : ℝ → ℝ → ℝ) (T0 T1 X0 X1 : ℝ),
        ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2) →
        (∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t) →
        (∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x) →
        Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1 →
        weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 1) φt φx = 0) ∧
      (∃ (φ φt φx : ℝ → ℝ → ℝ) (T0 T1 X0 X1 : ℝ),
        ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2) ∧
        (∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t) ∧
        (∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x) ∧
        Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1 ∧
        weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 0) φt φx = 0) ∧
      ¬ (∀ (φ φt φx : ℝ → ℝ → ℝ) (T0 T1 X0 X1 : ℝ),
        ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2) →
        (∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t) →
        (∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x) →
        Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1 →
        weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 0) φt φx = 0) := by
  obtain ⟨φ, φt, φx, T0, T1, X0, X1, h1, h2, h3, h4, h5, hRH⟩ :=
    exists_test_weakResidual_eq_zero_not_rankineHugoniot
  exact ⟨weakResidual_movingStep_eq_zero_iff.mpr (by norm_num),
    ⟨φ, φt, φx, T0, T1, X0, X1, h1, h2, h3, h4, h5⟩,
    fun h => hRH (weakResidual_movingStep_eq_zero_iff.mp h)⟩

/-- The Burgers front `2 | 0` along `x = τ` conserves mass on `[-1, 1]` at time `0`: its speed
`1` is the Rankine-Hugoniot speed `(2 + 0) / 2`. -/
example :
    HasDerivAt (fun τ : ℝ => (∫ _x in (-1 : ℝ)..τ, (2 : ℝ)) + (∫ _x in τ..(1 : ℝ), (0 : ℝ)))
      (burgersFlux 2 - burgersFlux 0) 0 := by
  have key := burgers_conservation_iff_speed (uL := 2) (uR := 0) (a := -1) (b := 1) (t := 0)
    (s := fun τ => τ) (by norm_num) (hasDerivAt_id' 0)
    (by norm_num) (by norm_num)
  exact key.mpr (by norm_num)

/-- The same states with a stationary front do not conserve mass: speed `0` is not
`(2 + 0) / 2`. -/
example :
    ¬ HasDerivAt
      (fun _τ : ℝ => (∫ _x in (-1 : ℝ)..(0 : ℝ), (2 : ℝ)) + (∫ _x in (0 : ℝ)..(1 : ℝ), (0 : ℝ)))
      (burgersFlux 2 - burgersFlux 0) 0 := by
  have key := burgers_conservation_iff_speed (uL := 2) (uR := 0) (a := -1) (b := 1) (t := 0)
    (s := fun _ => 0) (by norm_num) (hasDerivAt_const 0 0)
    (by norm_num) (by norm_num)
  intro h
  have hc := key.mp h
  norm_num at hc

/-- A decreasing jump `3 | 1` at its Rankine-Hugoniot speed `2`: entropy production `-2 / 3`,
nonpositive, and `1 < 2 < 3`. -/
example :
    burgersEntropyProduction 2 3 1 = -2 / 3 ∧ burgersEntropyProduction 2 3 1 ≤ 0 ∧
      (1 : ℝ) < 2 ∧ (2 : ℝ) < 3 := by
  have hRH : (2 : ℝ) * (1 - 3) = burgersFlux 1 - burgersFlux 3 := by
    unfold burgersFlux
    norm_num
  have hval : burgersEntropyProduction 2 3 1 = -2 / 3 := by
    have h := burgers_entropyProduction_mean 3 1
    rw [show ((3 : ℝ) + 1) / 2 = 2 by norm_num] at h
    rw [h]
    norm_num
  exact ⟨hval, burgers_decreasingJump_admissible (by norm_num) hRH⟩

/-- An expansion jump `-1 | 1` with the stationary front satisfies the jump identity
`0 * (1 - (-1)) = f 1 - f (-1)` but has positive entropy production. -/
example : 0 < burgersEntropyProduction 0 (-1) 1 :=
  burgers_expansionJump_rejected (by norm_num) (by unfold burgersFlux; norm_num)

end PhyslibExtTest.FluidDynamics.ScalarShockPorts
