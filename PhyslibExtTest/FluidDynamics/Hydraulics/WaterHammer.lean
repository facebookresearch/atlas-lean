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

import PhyslibExt.FluidDynamics.Hydraulics.WaterHammer
import PhyslibExt.FluidDynamics.TravelingWave

/-!
# Water-hammer wave-adapter checks

## i. Overview

Elaboration, non-vacuity, and negative-control checks for
`PhyslibExt.FluidDynamics.Hydraulics.WaterHammer`: a quadratic adapter
spot check, the sine traveling profiles in both directions at unit
parameters, a wrong-speed failure, and the second-derivative premise
control. These are checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Derivative helpers
- B. Adapter spot check
- C. Traveling profiles
- D. Negative controls

## iv. References

- `PhyslibExt.FluidDynamics.Hydraulics.WaterHammer`
- `PhyslibExt.FluidDynamics.TravelingWave`
-/

open Space Time
open FluidDynamics.WaterHammer

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

/-- Time-slice derivative of a left-moving sine profile. -/
private lemma hasDerivAt_sin_add_mul_time (c t x : ℝ) :
    HasDerivAt (fun s => Real.sin (x + c * s))
      (Real.cos (x + c * t) * c) t := by
  have hinner : HasDerivAt (fun s => x + c * s) c t := by
    have h := ((hasDerivAt_id t).const_mul c).const_add x
    simpa using h
  exact (Real.hasDerivAt_sin (x + c * t)).comp t hinner

/-- Time-slice derivative of a left-moving cosine profile. -/
private lemma hasDerivAt_cos_add_mul_time (c t x : ℝ) :
    HasDerivAt (fun s => Real.cos (x + c * s))
      (-Real.sin (x + c * t) * c) t := by
  have hinner : HasDerivAt (fun s => x + c * s) c t := by
    have h := ((hasDerivAt_id t).const_mul c).const_add x
    simpa using h
  exact (Real.hasDerivAt_cos (x + c * t)).comp t hinner

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

/-- Space-slice derivative of a shifted sine, plus sign. -/
private lemma hasDerivAt_sin_add_space (d x : ℝ) :
    HasDerivAt (fun y => Real.sin (y + d)) (Real.cos (x + d)) x := by
  have h := (Real.hasDerivAt_sin (x + d)).comp x ((hasDerivAt_id x).add_const d)
  rwa [mul_one] at h

/-- Space-slice derivative of a shifted cosine, plus sign. -/
private lemma hasDerivAt_cos_add_space (d x : ℝ) :
    HasDerivAt (fun y => Real.cos (y + d)) (-Real.sin (x + d)) x := by
  have h := (Real.hasDerivAt_cos (x + d)).comp x ((hasDerivAt_id x).add_const d)
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

/-! ## C. Traveling profiles -/

/-- Right-moving sine profile at unit parameters: the transported head
satisfies the Physlib wave equation at speed `1`. -/
example : ∀ (t : Time) (x : Space 1),
    ClassicalMechanics.WaveEquation
      (scalarWaveField (FluidDynamics.TravelingWave.hR 1 Real.sin)) t x 1 := by
  refine waveEquation_head (a := 1) (g := 1) (A := 1)
    (h := FluidDynamics.TravelingWave.hR 1 Real.sin)
    (q := FluidDynamics.TravelingWave.qR 1 1 1 Real.sin)
    (ht := fun t x => -Real.cos (x - t)) (hx := fun t x => Real.cos (x - t))
    (qt := fun t x => -Real.cos (x - t)) (qx := fun t x => Real.cos (x - t))
    (hxx := fun t x => -Real.sin (x - t)) (qxt := fun t x => Real.sin (x - t))
    (qtx := fun t x => Real.sin (x - t))
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t x
    simpa [FluidDynamics.TravelingWave.hR] using hasDerivAt_sin_sub_mul_time 1 t x
  · intro t x
    simpa [FluidDynamics.TravelingWave.qR] using hasDerivAt_sin_sub_mul_time 1 t x
  · intro t x
    simpa [FluidDynamics.TravelingWave.hR] using hasDerivAt_sin_sub_space t x
  · intro t x
    simpa [FluidDynamics.TravelingWave.qR] using hasDerivAt_sin_sub_space t x
  · intro t x
    norm_num
  · intro t x
    norm_num
  · intro t x
    exact hasDerivAt_cos_sub_space t x
  · intro t x
    simpa using hasDerivAt_cos_sub_mul_time 1 t x
  · intro t x
    have h := (hasDerivAt_cos_sub_space t x).neg
    rwa [neg_neg] at h
  · intro t x
    rfl

/-- Right-moving sine profile at unit parameters: the transported
discharge also satisfies the Physlib wave equation at speed `1`. -/
example : ∀ (t : Time) (x : Space 1),
    ClassicalMechanics.WaveEquation
      (scalarWaveField (FluidDynamics.TravelingWave.qR 1 1 1 Real.sin)) t x 1 := by
  refine waveEquation_discharge (a := 1) (g := 1) (A := 1)
    (h := FluidDynamics.TravelingWave.hR 1 Real.sin)
    (q := FluidDynamics.TravelingWave.qR 1 1 1 Real.sin)
    (ht := fun t x => -Real.cos (x - t)) (hx := fun t x => Real.cos (x - t))
    (qt := fun t x => -Real.cos (x - t)) (qx := fun t x => Real.cos (x - t))
    (qxx := fun t x => -Real.sin (x - t)) (hxt := fun t x => Real.sin (x - t))
    (htx := fun t x => Real.sin (x - t))
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t x
    simpa [FluidDynamics.TravelingWave.hR] using hasDerivAt_sin_sub_mul_time 1 t x
  · intro t x
    simpa [FluidDynamics.TravelingWave.qR] using hasDerivAt_sin_sub_mul_time 1 t x
  · intro t x
    simpa [FluidDynamics.TravelingWave.hR] using hasDerivAt_sin_sub_space t x
  · intro t x
    simpa [FluidDynamics.TravelingWave.qR] using hasDerivAt_sin_sub_space t x
  · intro t x
    norm_num
  · intro t x
    norm_num
  · intro t x
    exact hasDerivAt_cos_sub_space t x
  · intro t x
    simpa using hasDerivAt_cos_sub_mul_time 1 t x
  · intro t x
    have h := (hasDerivAt_cos_sub_space t x).neg
    rwa [neg_neg] at h
  · intro t x
    rfl

/-- Left-moving sine profile at unit parameters: the transported head
satisfies the Physlib wave equation at speed `1`, with the opposite
discharge sign. -/
example : ∀ (t : Time) (x : Space 1),
    ClassicalMechanics.WaveEquation
      (scalarWaveField (FluidDynamics.TravelingWave.hL 1 Real.sin)) t x 1 := by
  refine waveEquation_head (a := 1) (g := 1) (A := 1)
    (h := FluidDynamics.TravelingWave.hL 1 Real.sin)
    (q := FluidDynamics.TravelingWave.qL 1 1 1 Real.sin)
    (ht := fun t x => Real.cos (x + t)) (hx := fun t x => Real.cos (x + t))
    (qt := fun t x => -Real.cos (x + t)) (qx := fun t x => -Real.cos (x + t))
    (hxx := fun t x => -Real.sin (x + t)) (qxt := fun t x => Real.sin (x + t))
    (qtx := fun t x => Real.sin (x + t))
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t x
    simpa [FluidDynamics.TravelingWave.hL] using hasDerivAt_sin_add_mul_time 1 t x
  · intro t x
    convert (hasDerivAt_sin_add_mul_time 1 t x).neg using 1
    · funext s
      simp [FluidDynamics.TravelingWave.qL]
    · simp
  · intro t x
    simpa [FluidDynamics.TravelingWave.hL] using hasDerivAt_sin_add_space t x
  · intro t x
    convert (hasDerivAt_sin_add_space t x).neg using 1
    · funext y
      simp [FluidDynamics.TravelingWave.qL]
  · intro t x
    norm_num
  · intro t x
    norm_num
  · intro t x
    exact hasDerivAt_cos_add_space t x
  · intro t x
    convert (hasDerivAt_cos_add_mul_time 1 t x).neg using 1
    · funext s
      simp
    · simp
  · intro t x
    convert (hasDerivAt_cos_add_space t x).neg using 1
    simp
  · intro t x
    rfl

/-! ## D. Negative controls -/

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

/-- The second-derivative premise cannot be dropped: with zero fields,
the purported supplied value `hxx ≡ 1` is not a derivative of the
zero first-derivative field. -/
example (x : ℝ) : ¬ HasDerivAt (fun _ : ℝ => (0 : ℝ)) 1 x := by
  intro hd
  have h := hd.unique (hasDerivAt_const x (0 : ℝ))
  norm_num at h
