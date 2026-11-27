/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Measure.ScottishBook169

open MeasureTheory
open MathlibExt.MeasureTheory.ScottishBook169Wanted

-- Hausdorff measure has the stated congruence invariance and agrees with itself on Borel sets,
-- but it cannot be countably additive on arbitrary subsets of the plane.
example : ¬ IsCountablyAdditive (fun S : Set (EuclideanSpace ℝ (Fin 2)) => μH[1] S) := by
  intro hadd
  apply no_countably_additive_congruence_measure
  refine ⟨_, ?_, hadd, fun _ _ => rfl⟩
  rintro S T ⟨e, rfl⟩
  exact (e.hausdorffMeasure_image 1 S).symm
