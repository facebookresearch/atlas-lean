/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Measure.GraphMeasurableNull

open MeasureTheory
open MathlibExt.MeasureTheory.GraphMeasurableNullWanted

-- The d = 0 case is a singleton in the one-dimensional space, not an empty graph.
example : volume ({z : Fin 1 → ℝ | z (Fin.last 0) = 2} : Set (Fin 1 → ℝ)) = 0 :=
  (measurableSet_and_volume_eq_zero_graph (fun _ : Fin 0 → ℝ => 2) _ rfl measurable_const).2

-- A nonconstant graph: last coordinate equals first coordinate in ℝ².
example :
    MeasurableSet {z : Fin 2 → ℝ | z (Fin.last 1) = z (Fin.castSucc (0 : Fin 1))} ∧
      volume {z : Fin 2 → ℝ | z (Fin.last 1) = z (Fin.castSucc (0 : Fin 1))} = 0 :=
  measurableSet_and_volume_eq_zero_graph (fun x : Fin 1 → ℝ => x 0) _ rfl (measurable_pi_apply 0)
