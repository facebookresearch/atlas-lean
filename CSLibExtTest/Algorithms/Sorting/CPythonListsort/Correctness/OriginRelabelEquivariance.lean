/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.OriginRelabelEquivariance

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Kernel-checkable nonidentity regression -/

private def originRelabelRegressionOccurrence : Occurrence Nat :=
  { value := 17, origin := 0 }

/-- The relabeling is observably nonidentity inside the mirrored extent, and
applying it twice restores the original occurrence.  This is a kernel-reduced
regression proved by `decide`. -/
private theorem mirrorOccurrence_nonidentity_regression :
    mirrorOccurrence 4 originRelabelRegressionOccurrence =
        ({ value := 17, origin := 3 } : Occurrence Nat) ∧
      mirrorOccurrence 4
          (mirrorOccurrence 4 originRelabelRegressionOccurrence) =
        originRelabelRegressionOccurrence := by
  decide

end CPythonListsort
