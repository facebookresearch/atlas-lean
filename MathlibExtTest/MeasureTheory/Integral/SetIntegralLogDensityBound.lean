/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Integral.SetIntegralLogDensityBound
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open MathlibExt.MeasureTheory.SetIntegralLogDensityBoundWanted
open scoped ENNReal

private noncomputable def twoAtoms : Measure ℝ :=
  (2 : ℝ≥0∞) • Measure.dirac 0 + Measure.dirac 1

-- The set has mass two, strictly smaller than the full mass three. The bound is negative.
example : (∫ _ in ({0} : Set ℝ), Real.log (1 / 3) ∂twoAtoms) ≤ 2 * Real.log (1 / 2) := by
  have hm : twoAtoms univ = 3 := by norm_num [twoAtoms]
  have hE : twoAtoms ({0} : Set ℝ) = 2 := by norm_num [twoAtoms]
  let : IsFiniteMeasure twoAtoms := ⟨by rw [hm]; simp⟩
  let : IsFiniteMeasure (twoAtoms.restrict ({0} : Set ℝ)) := inferInstance
  have hnorm : (∫ _ : ℝ, (1 / 3 : ℝ) ∂twoAtoms) = 1 := by
    rw [integral_const, Measure.real_def, hm]
    norm_num [smul_eq_mul]
  have h := setIntegral_log_le_measure_mul_log_inv_measure twoAtoms (fun _ => (1 / 3 : ℝ))
    (fun _ => by norm_num) (integrable_const _) hnorm {0} (measurableSet_singleton 0)
    (by rw [hE]; norm_num) (by rw [hE]; simp) (integrable_const _)
  simpa only [hE, ENNReal.toReal_ofNat] using h
