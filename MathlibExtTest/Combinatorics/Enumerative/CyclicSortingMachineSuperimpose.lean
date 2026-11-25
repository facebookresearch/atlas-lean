/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CyclicSortingMachineSuperimpose

open MetaMathlibExt

-- For `n = 10` and odd `m = 5`, one pass moves `6` from the second run to the first.
example : cyclicSortingMachine [3, 2, 1] [6, 7, 1, 8, 2, 3, 9, 4, 5, 10] =
    [7, 1, 2, 8, 3, 4, 9, 5, 6, 10] :=
  cyclicSortingMachine_321_superimpose (n := 10) (m := 5) (by decide) (by decide) (by decide)

-- For `n = 7` the largest allowed `m` is the even value `4`.
example : cyclicSortingMachine [3, 2, 1] [5, 1, 2, 6, 3, 4, 7] = [1, 2, 3, 6, 4, 5, 7] :=
  cyclicSortingMachine_321_superimpose (n := 7) (m := 4) (by decide) (by decide) (by decide)

-- At `m = 5 = ⌊(2 · 7 + 1) / 3⌋` the conclusion fails, so the bound on `m` is sharp.
example : cyclicSortingMachine [3, 2, 1] (superimpose (List.range' 1 5) (List.range' 6 2)) ≠
    superimpose (List.range' 1 6) (List.range' 7 1) := by
  decide

-- The theorem assumes `4 ≤ n`, but its conclusion also holds for `n = 3` and `m = 1`.
example : cyclicSortingMachine [3, 2, 1] (superimpose (List.range' 1 1) (List.range' 2 2)) =
    superimpose (List.range' 1 2) (List.range' 3 1) := by
  decide
