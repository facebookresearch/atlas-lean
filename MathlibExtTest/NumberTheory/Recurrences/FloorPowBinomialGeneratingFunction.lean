/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FloorPowBinomialSum
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

open Finset

-- For ℓ = 3 the numerator is 1 - X + X^2, even when the weight t is nonzero.
example (t : ℤ) :
    PowerSeries.mk (fun n => ∑ i ∈ range (n + 1), (n.choose i : ℤ) * t ^ (i / 3)) *
        ((1 - PowerSeries.X) ^ 3 - PowerSeries.C t * PowerSeries.X ^ 3) =
      1 - PowerSeries.X + PowerSeries.X ^ 2 := by
  rw [floorPowBinomialSum_generatingFunction t (ℓ := 3) (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose, sub_eq_add_neg]

end MetaMathlibExt
