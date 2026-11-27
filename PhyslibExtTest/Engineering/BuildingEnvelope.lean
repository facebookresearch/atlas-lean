/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.BuildingEnvelope
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity

/-!
# Building-envelope certificate checks

Focused checks for
`PhyslibExt.Engineering.BuildingEnvelope`: a nonzero affine
layer with face temperatures `280` and `300`, face pressures
`279` and `280`, midpoint `θ = 1 / 2`, and the saturation-pressure
specialization with zero face vapor pressures.

These are elaboration and non-vacuity checks, not new results.
-/

open Engineering.BuildingEnvelope

/-- Midpoint of the safe affine layer for the test curve
`psat(T) = T`: temperature `290`, pressure `559 / 2`. -/
example :
    0 < affineProfile 280 300 (1 / 2 : ℝ)
      ∧ affineProfile 279 280 (1 / 2 : ℝ)
        ≤ affineProfile 280 300 (1 / 2 : ℝ) :=
  affine_no_supersaturation
    (psat := fun T : ℝ => T)
    (by intro a _ b _ hab; exact hab)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The certificate values at the same midpoint are the
expected affine values. -/
example : affineProfile 280 300 (1 / 2 : ℝ) = 290
    ∧ affineProfile 279 280 (1 / 2 : ℝ) = 559 / 2 := by
  constructor <;> norm_num [affineProfile_apply]

/-- The EarthScience saturation-pressure specialization applies
to a one-layer wall with zero face vapor pressures. -/
example :
    0 < affineProfile (280 : ℝ) 300 (1 / 2 : ℝ)
      ∧ affineProfile (0 : ℝ) 0 (1 / 2 : ℝ)
        ≤ 1 * Real.exp ((1 / 1)
            * (1 / 1
              - 1 / affineProfile (280 : ℝ) 300 (1 / 2 : ℝ))) :=
  affine_no_supersaturation_layers_saturationPressure
    (n := 1) (es0 := 1) (L := 1) (Rv := 1) (T0 := 1)
    (Tface := fun i => if i = 0 then 280 else 300)
    (Pface := fun _ => 0) (i := 0) (θ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      intro i hi
      interval_cases i <;> norm_num)
    (by
      intro i hi
      interval_cases i
      simp
      positivity)
    (by norm_num) (by norm_num) (by norm_num)
