/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CyclicSortingMachine123Iterates

open MetaMathlibExt

-- At the lower endpoint the machine sorts `231` in one pass, while `ξ₃` is not the identity.
example : cyclicSortingMachine [1, 2, 3] [2, 3, 1] = [1, 2, 3] ∧
    xiPermutation 3 ≠ [1, 2, 3] := by
  obtain ⟨hs, ht⟩ := cyclicSortingMachine_123_iterate_sorts (n := 3) (by decide)
  exact ⟨hs [2, 3, 1] (by decide), ht⟩

-- The sharpness witness fails one pass early at the first even and odd inductive steps.
example : cyclicSortingMachine [1, 2, 3] (xiPermutation 4) ≠ [1, 2, 3, 4] ∧
    (cyclicSortingMachine [1, 2, 3])^[2] (xiPermutation 5) ≠ [1, 2, 3, 4, 5] :=
  ⟨(cyclicSortingMachine_123_iterate_sorts (n := 4) (by decide)).2,
    (cyclicSortingMachine_123_iterate_sorts (n := 5) (by decide)).2⟩

-- Compute the first pass on each witness independently.
example : cyclicSortingMachine [1, 2, 3] (xiPermutation 4) = [3, 1, 2, 4] ∧
    cyclicSortingMachine [1, 2, 3] (xiPermutation 5) = [1, 4, 2, 3, 5] := by
  decide
