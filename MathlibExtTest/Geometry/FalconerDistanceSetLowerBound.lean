/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Geometry.FalconerDistanceSetLowerBound

open MeasureTheory FalconerDistanceSet FalconerDistanceSetWanted
open scoped ENNReal

example : (1 : ℝ≥0∞) ≤ planarDistanceThreshold := lowerBound_Falconer1985_holds

-- Every strictly subcritical exponent admits a compact counterexample.
example {s : ℝ≥0∞} (hs : s < 1) :
    ∃ E : Set (EuclideanSpace ℝ (Fin 2)), IsCompact E ∧ s < dimH E ∧
      volume (distanceSet E) = 0 := by
  by_contra! h
  have hp : planarThresholdProperty s := fun E hc hd ↦ pos_iff_ne_zero.mpr (h E hc hd)
  have hle := planarDistanceThreshold_le_of_property (hs.le.trans (by norm_num)) hp
  exact hs.not_ge (le_trans lowerBound_Falconer1985_holds hle)
