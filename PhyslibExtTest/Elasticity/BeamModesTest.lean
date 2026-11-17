/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Elasticity.BeamModes

/-!
# Beam mode checks

Concrete consumers of `PhyslibExt.Elasticity.BeamModes`: the first
mode `k = 1` on a beam with `L = 2`, `EI = 3`, `ρA = 1`, its support
values, and its conserved energy.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. First mode on a concrete beam

## iv. References

- `PhyslibExt.Elasticity.BeamModes`
-/

/-- Support values and conserved energy of the first mode at
`L = 2`, `EI = 3`, `ρA = 1`, at arbitrary time `t`. -/
example (t : ℝ) :
    BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) 0 t = 0 ∧
      BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) 2 t = 0 ∧
        BeamModes.beamModeEnergy 3 1 2 (BeamModes.beamFreq 3 1 2 1) 1 t =
          (2 / 4) * 3 * ((1 : ℝ) * Real.pi / 2) ^ 4 :=
  ⟨BeamModes.beamMode_zero_left 1 2 _ t,
   BeamModes.beamMode_zero_right 1 (by norm_num) _ t,
   (by
     have h := BeamModes.beamModeEnergy_conserved (EI := 3) (ρA := 1)
       (L := 2) (by norm_num) (by norm_num) (by norm_num) 1 t
     simpa using h)⟩

/-- The beam equation and curvature conditions for the first mode at
`L = 2`, `EI = 3`, `ρA = 1`, at the interior point `x = 1`,
`t = 0`. -/
example : (1 : ℝ) * iteratedDeriv 2
      (fun s : ℝ => BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) 1 s) 0 +
    3 * iteratedDeriv 4
      (fun y : ℝ => BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) y 0) 1 =
    0 ∧
  iteratedDeriv 2
      (fun y : ℝ => BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) y 0) 0 =
    0 ∧
  iteratedDeriv 2
      (fun y : ℝ => BeamModes.beamMode 1 2 (BeamModes.beamFreq 3 1 2 1) y 0) 2 =
    0 :=
  ⟨BeamModes.beamMode_beamEquation (by norm_num) (by norm_num)
    (by norm_num) 1 1 0,
   (BeamModes.beamMode_curvature_zero 1 (by norm_num) _ 0).1,
   (BeamModes.beamMode_curvature_zero 1 (by norm_num) _ 0).2⟩

/-- Sine-basis tail bound: for unit coefficients, the tail modes
`2 .. 3` of the sine Hilbert basis have squared norm at most that
of the full sum `1 .. 3`. -/
example :
    ‖∑ k ∈ Finset.Ico (1 + 1) (3 + 1),
        (1 : ℝ) • MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
          ⟨k + 1, Nat.succ_pos k⟩‖ ^ 2 ≤
      ‖∑ k ∈ Finset.Icc 1 3,
        (1 : ℝ) • MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
          ⟨k + 1, Nat.succ_pos k⟩‖ ^ 2 :=
  BeamModes.sineBasis_tail_norm_sq_le (fun _ => 1) (by norm_num)
