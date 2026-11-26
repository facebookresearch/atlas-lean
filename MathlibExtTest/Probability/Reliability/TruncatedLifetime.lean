/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Reliability.TruncatedLifetime
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem atom_nonneg : 0 ≤ᵐ[Measure.dirac (2 : ℝ)] (fun x : ℝ => x) :=
  (ae_dirac_iff (measurableSet_le measurable_const measurable_id)).2 (by
    change (0 : ℝ) ≤ 2
    norm_num)

private theorem atom_survival :
    (∀ T : ℝ, 0 ≤ T → (∫ x, min x T ∂Measure.dirac (2 : ℝ)) =
      ∫ t in (0 : ℝ)..T, (Measure.dirac (2 : ℝ)).real {x | t < x}) ∧
      (∫⁻ x, ENNReal.ofReal x ∂Measure.dirac (2 : ℝ)) =
        ∫⁻ t in Set.Ioi (0 : ℝ), Measure.dirac (2 : ℝ) {x | t < x} :=
  truncatedLifetime_survival_integral (Measure.dirac (2 : ℝ)) (L := fun x : ℝ => x)
    measurable_id atom_nonneg

-- The cap is reached, even though the lifetime law is a point mass.
example : (∫ t in (0 : ℝ)..1, (Measure.dirac (2 : ℝ)).real {x | t < x}) = 1 := by
  rw [← atom_survival.1 1 (by norm_num), integral_dirac]
  norm_num

-- An atom exactly at the upper integration endpoint does not change the identity.
example : (∫ t in (0 : ℝ)..2, (Measure.dirac (2 : ℝ)).real {x | t < x}) = 2 := by
  rw [← atom_survival.1 2 (by norm_num), integral_dirac]
  simp

-- When the horizon exceeds the lifetime, the cap does not change the mean.
example : (∫ t in (0 : ℝ)..3, (Measure.dirac (2 : ℝ)).real {x | t < x}) = 2 := by
  rw [← atom_survival.1 3 (by norm_num), integral_dirac]
  norm_num

-- The result also applies at horizon zero.
example : (∫ x, min x 0 ∂Measure.dirac (2 : ℝ)) = 0 := by
  rw [atom_survival.1 0 le_rfl, intervalIntegral.integral_same]

-- The uncapped integral is over extended nonnegative values.
example : (∫⁻ t in Set.Ioi (0 : ℝ), Measure.dirac (2 : ℝ) {x | t < x}) = 2 := by
  rw [← atom_survival.2]
  rw [lintegral_dirac' _ ENNReal.measurable_ofReal]
  norm_num
