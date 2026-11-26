/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentSubConvergentOrder

namespace MathlibExtTest.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentSubConvergentOrder

open MetaMathlibExt

variable {K : Type*} [Field K] (α : LaurentSeries K) (hα : LaurentIsIrrational α)

-- The zeroth convergent already improves the approximation when `|α| ≥ 1`.
example (h0 : α.order ≤ 0) :
    α.order < (α - laurentConvNum α 1 / laurentConvDen α 1).order :=
  (laurent_sub_convergent_order α hα).1 h0 0

-- When `|α| < 1`, later convergents are strictly closer than the zeroth one.
example (hpos : 0 < α.order) (n : ℕ) (hn : 1 ≤ n) :
    (α - laurentConvNum α 1 / laurentConvDen α 1).order <
      (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order := by
  have h := (laurent_sub_convergent_order α hα).2 hpos
  rw [h.1]
  exact h.2 n hn

end MathlibExtTest.NumberTheory.LaurentSeriesBoundedPartialQuotientsLaurentSubConvergentOrder
