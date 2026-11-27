/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Measure.SingularMeasureMaximalFunction
import Mathlib.MeasureTheory.Measure.Dirac.Basic

open MeasureTheory Metric Set
open MathlibExt.MeasureTheory.SingularMeasureMaximalFunctionWanted
open scoped ENNReal

-- The conclusion forces divergence at the actual atom, not just a statement about volume.
example :
    (⨆ (r : ℝ) (_ : 0 < r), (Measure.dirac (0 : EuclideanSpace ℝ (Fin 1))) (ball 0 r) /
      volume (ball (0 : EuclideanSpace ℝ (Fin 1)) r)) = ⊤ := by
  let E := EuclideanSpace ℝ (Fin 1)
  let μ := Measure.dirac (0 : E)
  let M (x : E) := ⨆ (r : ℝ) (_ : 0 < r), μ (ball x r) / volume (ball x r)
  have hsing : μ.MutuallySingular (volume : Measure E) :=
    mutuallySingular_dirac (0 : E) volume
  have hzero := measure_setOf_maximalFunction_lt_top_eq_zero_of_mutuallySingular μ hsing M
    (fun _ => rfl)
  change M 0 = ⊤
  by_contra hnot
  have hx : (0 : E) ∈ {x : E | M x < ⊤} := lt_top_iff_ne_top.2 hnot
  change Measure.dirac (0 : E) {x : E | M x < ⊤} = 0 at hzero
  rw [Measure.dirac_apply_of_mem hx] at hzero
  exact one_ne_zero hzero
