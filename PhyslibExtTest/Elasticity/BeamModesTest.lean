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
`L = 2`, `EI = 3`, `ρA = 1`, evaluated at `t = 0`. -/
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
