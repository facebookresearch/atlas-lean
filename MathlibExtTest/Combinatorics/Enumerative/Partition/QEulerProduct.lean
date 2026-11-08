/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

example : qEulerProduct 1 = pentagonalSeries ℤ := qEulerProduct_one

example (k : ℕ) : qEulerProduct k = ∏' m : ℕ, (1 - X ^ (k * (m + 1)) : ℤ⟦X⟧) := rfl

example : PowerSeries.constantCoeff (qEulerProduct 3) = 1 :=
  constantCoeff_qEulerProduct (by norm_num)

end MetaMathlibExt
