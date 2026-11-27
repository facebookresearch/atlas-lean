/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GraphicalModels.BalkePearlBoundsWidth

/-!
# Balke–Pearl interval width under perfect compliance
-/

open Cslib.MachineLearning.GraphicalModels.BalkePearl
open WantedExt.Probability.Statistics.BalkePearlBoundsWanted

-- Under perfect compliance, the four cells with D ≠ Z vanish, so the interval has width zero.
example (q : TypeLaw) (hfalse : ∀ y, q.obs y true false = 0)
    (htrue : ∀ y, q.obs y false true = 0) :
    upperBound q.obs - lowerBound q.obs = 0 := by
  apply le_antisymm
  · simpa [hfalse, htrue] using width_le_noncompliance q
  · exact sub_nonneg.mpr ((lowerBound_le_ace q).trans (ace_le_upperBound q))
