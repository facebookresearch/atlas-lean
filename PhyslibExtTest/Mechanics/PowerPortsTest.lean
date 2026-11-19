/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.PowerPorts

/-!
# Particle power-port checks

Concrete consumers of `PhyslibExt.Mechanics.PowerPorts`: mass `2`, start `0` with velocity `1`
and constant force `4` over the elapsed time `1`; the unit oscillator `m = k = A = 1` over a
quarter period; and the unit inverse-square field along a radial path that avoids the centre.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Constant-force fixture
- B. Spring example
- C. Inverse-square field

## iv. References

None.

## A. Constant-force fixture

-/

open PhyslibExt.Mechanics.PowerPorts

/-- Mass `2`, start `0` with velocity `1`, force `4 ≠ 0`, elapsed time `1 > 0`: final velocity
`3`, final position `2`, work `8` (both as the integrated power and as the change of kinetic
energy), and impulse `4`. -/
example :
    constForceVelocity (E := ℝ) 2 1 4 1 = 3 ∧ constForcePosition (E := ℝ) 2 0 1 4 1 = 2 ∧
      ∫ t in (0 : ℝ)..1, inner ℝ (4 : ℝ) (constForceVelocity (E := ℝ) 2 1 4 t) = 8 ∧
      2 * ‖constForceVelocity (E := ℝ) 2 1 4 1‖ ^ 2 / 2 -
          2 * ‖constForceVelocity (E := ℝ) 2 1 4 0‖ ^ 2 / 2 = 8 ∧
      (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 1 - (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 0
        = 4 := by
  have hm : (0 : ℝ) < 2 := by norm_num
  have hv1 : constForceVelocity (E := ℝ) 2 1 4 1 = 3 := by
    simp [constForceVelocity, smul_eq_mul]
    norm_num
  have hx1 : constForcePosition (E := ℝ) 2 0 1 4 1 = 2 := by
    simp [constForcePosition, smul_eq_mul]
    norm_num
  have hv0 : constForceVelocity (E := ℝ) 2 1 4 0 = 1 := by
    simp [constForceVelocity, smul_eq_mul]
  have hK : 2 * ‖constForceVelocity (E := ℝ) 2 1 4 1‖ ^ 2 / 2 -
      2 * ‖constForceVelocity (E := ℝ) 2 1 4 0‖ ^ 2 / 2 = 8 := by
    rw [hv1, hv0]
    norm_num [Real.norm_eq_abs]
  have hwork := (constForce_work (m := 2) hm (0 : ℝ) (1 : ℝ) (4 : ℝ) (0 : ℝ) (1 : ℝ)).1
  have hwork8 : ∫ t in (0 : ℝ)..1, inner ℝ (4 : ℝ) (constForceVelocity (E := ℝ) 2 1 4 t) = 8 :=
    hwork.trans hK
  have himp : (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 1 -
      (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 0 = 4 := by
    rw [← constForce_impulse (E := ℝ) hm (1 : ℝ) (4 : ℝ) 0 1]
    simp
  exact ⟨hv1, hx1, hwork8, hK, himp⟩

/-- Newton's law on the fixture trajectory: `2 • x'' = 4`, so the acceleration is `2`. -/
example (t : ℝ) : deriv (deriv (constForcePosition (E := ℝ) 2 0 1 4)) t = 2 := by
  have h := (constForce_actual_trajectory (E := ℝ) (by norm_num : (0 : ℝ) < 2) 0 1 4).2.2 t
  rw [smul_eq_mul] at h
  linarith

/-- Power port at the start of the fixture: the kinetic energy grows at `⟪4, 1⟫ = 4`. -/
example : HasDerivAt (fun s => 2 * ‖constForceVelocity (E := ℝ) 2 1 4 s‖ ^ 2 / 2) 4 0 := by
  have h := constForce_power_port (E := ℝ) (by norm_num : (0 : ℝ) < 2) 1 4 0
  have hp : inner ℝ (4 : ℝ) (constForceVelocity (E := ℝ) 2 1 4 0) = 4 := by
    simp [constForceVelocity]
  rwa [hp] at h

/-- Impulse over the fixture interval is the change of momentum. -/
example : ∫ _ in (0 : ℝ)..1, (4 : ℝ) =
    (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 1 - (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 0 :=
  constForce_impulse (E := ℝ) (by norm_num) 1 4 0 1

/-! ## B. Spring example -/

/-- Spring power at the start of the unit oscillator: the mass starts at rest. -/
example : HasDerivAt (fun s : ℝ => 1 * ‖-1 * 1 * Real.sin (1 * s)‖ ^ 2 / 2)
    (inner ℝ (-1 * (1 * Real.cos (1 * 0))) (-1 * 1 * Real.sin (1 * 0))) 0 :=
  spring_power_port (m := 1) (k := 1) (A := 1) (ω := 1) one_pos one_pos (by simp) 0

/-- Spring work over a quarter period of the unit oscillator: the kinetic energy rises from `0`
to `1 / 2`, and the potential `x ^ 2 / 2 + C` falls by `1 / 2` whatever the constant `C`. -/
example (C : ℝ) :
    ∫ t in (0 : ℝ)..(Real.pi / 2),
        inner ℝ (-1 * (1 * Real.cos (1 * t))) (-1 * 1 * Real.sin (1 * t)) = 1 / 2 ∧
      -((1 * (1 * Real.cos (1 * (Real.pi / 2)))) ^ 2 / 2 + C -
          ((1 * (1 * Real.cos (1 * 0))) ^ 2 / 2 + C)) = 1 / 2 := by
  have h := spring_work (m := 1) (k := 1) (A := 1) (ω := 1) one_pos one_pos (by simp)
    0 (Real.pi / 2) C
  refine ⟨?_, ?_⟩
  · rw [h.1]
    norm_num
  · norm_num

/-! ## C. Inverse-square field -/

/-- Inverse-square work along the radial path `γ t = 1 + t` on `[0, 1]`, which never meets the
centre: the potential `-1 / ‖y‖` rises from `-1` to `-1 / 2`, so the work is `-1 / 2`. -/
example : ∫ t in (0 : ℝ)..1,
    inner ℝ (-OrbitalPerturbations.inverseSquareField 1 (1 + t : ℝ)) (1 : ℝ) = -1 / 2 := by
  have hcont : ContinuousOn
      (fun t : ℝ => inner ℝ (-OrbitalPerturbations.inverseSquareField 1 (1 + t : ℝ)) (1 : ℝ))
      (Set.uIcc 0 1) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 : (1 + t : ℝ) ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hn : ‖(1 + t : ℝ)‖ ^ 3 ≠ 0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr h1)
    have hd : ContinuousAt (fun s : ℝ => ‖(1 + s : ℝ)‖ ^ 3) t := by fun_prop
    have hf : ContinuousAt (fun s : ℝ => 1 / ‖(1 + s : ℝ)‖ ^ 3) t :=
      continuousAt_const.div hd hn
    have hg : ContinuousAt (fun s : ℝ => (1 + s : ℝ)) t := by fun_prop
    simp only [OrbitalPerturbations.inverseSquareField]
    exact ((hf.smul hg).neg.inner continuousAt_const).continuousWithinAt
  rw [inverseSquare_work (γ := fun t : ℝ => 1 + t) (γ' := fun _ => 1)
    (fun t _ => by simpa using (hasDerivAt_id t).const_add 1)
    (fun t ht h => by
      rw [Set.uIcc_of_le zero_le_one] at ht
      linarith [ht.1])
    hcont.intervalIntegrable]
  norm_num

/-- On the line, the unit inverse-square field at `2` is `1 / 4`, the gradient there of
`-1 / ‖y‖`. -/
example : HasGradientAt (fun y : ℝ => -1 / ‖y‖) (1 / 4) 2 := by
  have h := hasGradientAt_inverseSquarePotential (μ := (1 : ℝ)) (x := (2 : ℝ)) two_ne_zero
  convert h using 1
  norm_num [OrbitalPerturbations.inverseSquareField]

/-- The unit inverse-square potential on the line has no limit at the centre. -/
example : ¬ ContinuousAt (fun y : ℝ => -1 / ‖y‖) 0 :=
  inverseSquarePotential_not_continuousAt_zero one_ne_zero
