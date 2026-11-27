/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.PorePressureRatio
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Excess pore-pressure ratio checks

Concrete consumers of
`PhyslibExt.EarthScience.Geotechnical.PorePressureRatio`:
unit ratio exactly at vanishing vertical effective stress,
the ratio at the time origin, the totalized values at a
zero initial effective stress (outside the validity
domain), and independence of the shear entries.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Ratio values and entry independence

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.PorePressureRatio`
-/

open EarthScience

namespace PhyslibExtTest.EarthScience.Geotechnical.PorePressureRatio

/-- Pore-pressure series `u(t) = 2 + 8t` against total stress
`10`: initial effective stress `8`, vanishing at `t = 1`. -/
private def uLin : ℝ → ℝ := fun t => 2 + 8 * t

/-! ## A. Ratio values and entry independence -/

/-- The ratio vanishes at the time origin. -/
example : excessPorePressureRatio (!![10] : Matrix (Fin 1) (Fin 1) ℝ)
    0 uLin 0 = 0 := by
  simp [excessPorePressureRatio, uLin]

/-- At `t = 1` the pore pressure reaches the total stress:
unit ratio and zero vertical effective stress. -/
example : excessPorePressureRatio (!![10] : Matrix (Fin 1) (Fin 1) ℝ)
      0 uLin 1 = 1
    ∧ verticalEffectiveStress (!![10] : Matrix (Fin 1) (Fin 1) ℝ)
      0 uLin 1 = 0 := by
  have h0 : 0 < verticalEffectiveStress
      (!![10] : Matrix (Fin 1) (Fin 1) ℝ) 0 uLin 0 := by
    rw [verticalEffectiveStress_eq]
    norm_num [uLin]
  have hiff := excessPorePressureRatio_eq_one_iff h0 1
  have hzero : verticalEffectiveStress
      (!![10] : Matrix (Fin 1) (Fin 1) ℝ) 0 uLin 1 = 0 := by
    rw [verticalEffectiveStress_eq]
    norm_num [uLin]
  exact ⟨hiff.mpr hzero, hzero⟩

/-- Midpoint values: `σ'_v(1/2) = 4` and `r_u(1/2) = 1/2`,
through the ratio parametrization. -/
example : verticalEffectiveStress (!![10] : Matrix (Fin 1) (Fin 1) ℝ)
      0 uLin (1 / 2) = 4
    ∧ excessPorePressureRatio (!![10] : Matrix (Fin 1) (Fin 1) ℝ)
      0 uLin (1 / 2) = 1 / 2 := by
  constructor
  · rw [verticalEffectiveStress_eq]
    norm_num [uLin]
  · unfold excessPorePressureRatio
    rw [verticalEffectiveStress_eq]
    norm_num [uLin]

/-- Zero initial effective stress is outside the validity
domain: with total stress `2` and `u(0) = 2`, the initial
effective stress is `0`, so the positivity premise of the
identities cannot be met; the totalized ratio at `t = 1`
is `8 / 0 = 0` while the effective stress is `-8`, so
neither identity reads physically there. -/
example : verticalEffectiveStress (!![2] : Matrix (Fin 1) (Fin 1) ℝ)
      0 uLin 0 = 0
    ∧ ¬ 0 < verticalEffectiveStress (!![2] : Matrix (Fin 1) (Fin 1) ℝ)
      0 uLin 0
    ∧ excessPorePressureRatio (!![2] : Matrix (Fin 1) (Fin 1) ℝ)
      0 uLin 1 = 0
    ∧ verticalEffectiveStress (!![2] : Matrix (Fin 1) (Fin 1) ℝ)
      0 uLin 1 = -8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [verticalEffectiveStress_eq]
    norm_num [uLin]
  · rw [verticalEffectiveStress_eq]
    norm_num [uLin]
  · unfold excessPorePressureRatio
    rw [verticalEffectiveStress_eq]
    norm_num [uLin]
  · rw [verticalEffectiveStress_eq]
    norm_num [uLin]

/-- Shear entries do not affect the vertical effective stress. -/
example (u : ℝ → ℝ) (t : ℝ) :
    verticalEffectiveStress
        (!![10, 3; 5, 7] : Matrix (Fin 2) (Fin 2) ℝ) 0 u t
      = verticalEffectiveStress
        (!![10, -2; 9, 7] : Matrix (Fin 2) (Fin 2) ℝ) 0 u t := by
  rw [verticalEffectiveStress_eq, verticalEffectiveStress_eq]
  norm_num

#print axioms EarthScience.verticalEffectiveStress_eq
#print axioms EarthScience.verticalEffectiveStress_eq_mul_one_sub_ratio
#print axioms EarthScience.excessPorePressureRatio_eq_one_iff

end PhyslibExtTest.EarthScience.Geotechnical.PorePressureRatio
