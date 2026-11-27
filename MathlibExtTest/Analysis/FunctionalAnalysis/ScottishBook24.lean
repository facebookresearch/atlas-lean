/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook24

/-!
# Tests for Mazur's Problem 24

The theorem applies to a nonzero functional on the real plane and to the zero functional.
-/

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook24Wanted

example : Continuous (fun p : ℝ × ℝ ↦ p.1 - 2 * p.2) := by
  apply additiveFunctionalMeasurableOnCurvesContinuous
  · intro p q
    change (p.1 + q.1) - 2 * (p.2 + q.2) = (p.1 - 2 * p.2) + (q.1 - 2 * q.2)
    ring
  · intro x
    exact (continuous_fst.sub (continuous_const.mul continuous_snd)).measurable.comp
      x.continuous.measurable

example : Continuous (fun _ : Fin 0 → ℝ ↦ (0 : ℝ)) :=
  additiveFunctionalMeasurableOnCurvesContinuous (Fin 0 → ℝ) (fun _ ↦ 0) (by intros; simp)
    (fun _ ↦ measurable_const)
