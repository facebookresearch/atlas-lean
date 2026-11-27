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

open MeasureTheory

private theorem atom_nonneg : 0 ≤ᵐ[Measure.dirac (2 : ℝ)] (fun x : ℝ => x) :=
  (ae_dirac_iff (measurableSet_le measurable_const measurable_id)).2 (by
    change (0 : ℝ) ≤ 2
    norm_num)

private theorem atom_survival (T : ℝ) (hT : 0 ≤ T) :
    (∫ x, min x T ∂Measure.dirac (2 : ℝ)) =
      ∫ t in (0 : ℝ)..T, (Measure.dirac (2 : ℝ)).real {x | t < x} :=
  integral_min_eq_intervalIntegral_meas_lt (Measure.dirac (2 : ℝ))
    measurable_id.aemeasurable atom_nonneg hT

-- The cap is reached, even though the lifetime law is a point mass.
example : (∫ t in (0 : ℝ)..1, (Measure.dirac (2 : ℝ)).real {x | t < x}) = 1 := by
  rw [← atom_survival 1 (by norm_num), integral_dirac]
  norm_num

-- An atom exactly at the upper integration endpoint does not change the identity.
example : (∫ t in (0 : ℝ)..2, (Measure.dirac (2 : ℝ)).real {x | t < x}) = 2 := by
  rw [← atom_survival 2 (by norm_num), integral_dirac]
  simp

-- When the horizon exceeds the lifetime, the cap does not change the mean.
example : (∫ t in (0 : ℝ)..3, (Measure.dirac (2 : ℝ)).real {x | t < x}) = 2 := by
  rw [← atom_survival 3 (by norm_num), integral_dirac]
  norm_num

-- The result also applies at horizon zero.
example : (∫ x, min x 0 ∂Measure.dirac (2 : ℝ)) = 0 := by
  rw [atom_survival 0 le_rfl, intervalIntegral.integral_same]

-- Total mass two: the identity concerns the integral, not a normalized expectation.
example : (∫ t in (0 : ℝ)..1,
    (Measure.dirac (2 : ℝ) + Measure.dirac 2).real {x | t < x}) = 2 := by
  have hμ : 0 ≤ᵐ[Measure.dirac (2 : ℝ) + Measure.dirac 2] (fun x : ℝ => x) :=
    ae_add_measure_iff.2 ⟨atom_nonneg, atom_nonneg⟩
  rw [← integral_min_eq_intervalIntegral_meas_lt _ (L := fun x : ℝ => x)
    measurable_id.aemeasurable hμ (by norm_num : (0 : ℝ) ≤ 1),
    integral_add_measure (integrable_dirac eNorm_lt_top) (integrable_dirac eNorm_lt_top),
    integral_dirac]
  norm_num
