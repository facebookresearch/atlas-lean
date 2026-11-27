/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.CommonRectangle

/-!
# Tests for `Sheffield.CommonRectangle`

Module under test: `Sheffield.CommonRectangle` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `commonRectLeftShift` and `commonRectTopShift` evaluate on `M = 3`: `(-3, 0)` and `(0, 3)`.
* The left and right shifts cancel, and so do the bottom and top shifts.
* `PeriodicPlaneEmbedding.exists_commonSquare_fourBoundaryPlacements` elaborates (check-only;
  no concrete plane embedding is available).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace CommonRectangle

open _root_.StatMech.FK.PeriodicPlanar

-- Explicit values for `M = 3`.
example : commonRectLeftShift (fun _ => 3) 0 = ![-3, 0] ∧
    commonRectTopShift (fun _ => 3) 0 = ![0, 3] := by
  constructor <;> funext i <;> fin_cases i <;> simp [commonRectLeftShift, commonRectTopShift]

-- Opposite shifts cancel.
example (M : ℕ → ℕ) (N : ℕ) : commonRectLeftShift M N + commonRectRightShift M N = 0 ∧
    commonRectBottomShift M N + commonRectTopShift M N = 0 := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [commonRectLeftShift, commonRectRightShift, commonRectBottomShift, commonRectTopShift]

-- `PeriodicPlaneEmbedding.exists_commonSquare_fourBoundaryPlacements` elaborates.
example := @PeriodicPlaneEmbedding.exists_commonSquare_fourBoundaryPlacements

end CommonRectangle
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
