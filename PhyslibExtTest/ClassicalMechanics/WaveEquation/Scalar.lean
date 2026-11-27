/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum

import PhyslibExt.ClassicalMechanics.WaveEquation.Scalar

/-!
# Scalar wave-field adapter checks

## i. Overview

Elaboration and negative-control checks for
`PhyslibExt.ClassicalMechanics.WaveEquation.Scalar`: a quadratic
Laplacian spot check and a concrete wrong-speed failure of Physlib's
wave-equation predicate for a transported sine profile. These are
checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Derivative helpers
- B. Adapter spot check
- C. Wrong-speed control

## iv. References

- `PhyslibExt.ClassicalMechanics.WaveEquation.Scalar`
-/

open Space Time
open PhyslibExt.ClassicalMechanics.WaveEquation.Scalar

/-! ## A. Derivative helpers -/

/-- Time-slice derivative of a right-moving sine profile. -/
private lemma hasDerivAt_sin_sub_mul_time (c t x : ℝ) :
    HasDerivAt (fun s => Real.sin (x - c * s))
      (Real.cos (x - c * t) * (-c)) t := by
  have hinner : HasDerivAt (fun s => x - c * s) (-c) t := by
    have h := ((hasDerivAt_id t).const_mul c).neg.const_add x
    simpa [sub_eq_add_neg] using h
  exact (Real.hasDerivAt_sin (x - c * t)).comp t hinner

/-- Time-slice derivative of a right-moving cosine profile. -/
private lemma hasDerivAt_cos_sub_mul_time (c t x : ℝ) :
    HasDerivAt (fun s => Real.cos (x - c * s))
      (-Real.sin (x - c * t) * (-c)) t := by
  have hinner : HasDerivAt (fun s => x - c * s) (-c) t := by
    have h := ((hasDerivAt_id t).const_mul c).neg.const_add x
    simpa [sub_eq_add_neg] using h
  exact (Real.hasDerivAt_cos (x - c * t)).comp t hinner

/-- Space-slice derivative of a shifted sine. -/
private lemma hasDerivAt_sin_sub_space (d x : ℝ) :
    HasDerivAt (fun y => Real.sin (y - d)) (Real.cos (x - d)) x := by
  have h := (Real.hasDerivAt_sin (x - d)).comp x ((hasDerivAt_id x).sub_const d)
  rwa [mul_one] at h

/-- Space-slice derivative of a shifted cosine. -/
private lemma hasDerivAt_cos_sub_space (d x : ℝ) :
    HasDerivAt (fun y => Real.cos (y - d)) (-Real.sin (x - d)) x := by
  have h := (Real.hasDerivAt_cos (x - d)).comp x ((hasDerivAt_id x).sub_const d)
  rwa [mul_one] at h

/-! ## B. Adapter spot check -/

/-- The Laplacian adapter on the stationary quadratic profile `y ^ 2`
gives the constant component `2`. -/
example (t : Time) (x : Space 1) :
    Δᵥ (scalarWaveField (fun _ y => y ^ 2) t) x =
      WithLp.toLp 2 (fun _ => (2 : ℝ)) :=
  laplacianVec_scalarWaveField (φ := fun _ y => y ^ 2)
    (φx := fun _ y => 2 * y) (φxx := fun _ _ => (2 : ℝ)) t x
    (fun y => by simpa using hasDerivAt_pow 2 y)
    (by simpa using (hasDerivAt_id (x 0)).const_mul (2 : ℝ))

/-! ## C. Wrong-speed control -/

/-- Wrong speed: the profile `sin (x - 2t)` does not satisfy the
Physlib wave equation at speed `1` at `t = 0`, `x = π / 2`. -/
example :
    ¬ ClassicalMechanics.WaveEquation
      (scalarWaveField (fun t x => Real.sin (x - 2 * t))) ⟨0⟩
        ⟨fun _ => Real.pi / 2⟩ 1 := by
  intro hw
  have hL : Δᵥ (scalarWaveField (fun t x => Real.sin (x - 2 * t)) ⟨0⟩)
        ⟨fun _ => Real.pi / 2⟩ =
      WithLp.toLp 2 (fun _ => -Real.sin (Real.pi / 2 - 2 * (0 : ℝ))) := by
    apply laplacianVec_scalarWaveField
      (φx := fun t x => Real.cos (x - 2 * t))
      (φxx := fun t x => -Real.sin (x - 2 * t))
    · intro y
      simpa using hasDerivAt_sin_sub_space (2 * (0 : ℝ)) y
    · simpa using hasDerivAt_cos_sub_space (2 * (0 : ℝ)) (Real.pi / 2)
  have hT : ∂ₜ (fun t => (∂ₜ
        (fun t => scalarWaveField (fun t x => Real.sin (x - 2 * t)) t
          ⟨fun _ => Real.pi / 2⟩) t)) ⟨0⟩ =
      WithLp.toLp 2
        (fun _ => (-Real.sin (Real.pi / 2 - 2 * (0 : ℝ)) * (-2)) * (-2)) := by
    apply deriv_deriv_scalarWaveField
      (φt := fun t x => Real.cos (x - 2 * t) * (-2))
      (φtt := fun t x => (-Real.sin (x - 2 * t) * (-2)) * (-2))
    · intro s
      exact hasDerivAt_sin_sub_mul_time 2 s (Real.pi / 2)
    · simpa using
        (hasDerivAt_cos_sub_mul_time 2 (0 : ℝ) (Real.pi / 2)).mul_const (-2)
  unfold ClassicalMechanics.WaveEquation at hw
  rw [hL, hT] at hw
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) hw
  simp [PiLp.sub_apply, Real.sin_pi_div_two] at h0
  norm_num at h0
