/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InfiniteWord.GutkovskiyModTwo

open MetaMathlibExt

-- The second iterate has length 6, so the unboundedness part gives such an
-- iterate for the bound 6.
example : ∃ n : ℕ,
    6 ≤ (morphIterate (fun b : ℕ ↦ if b = 0 then [0, 1] else [0, 0, 1, 0]) n [0]).length :=
  isOmegaLimit_gutkovskiy_mod_two.1 6

-- The agreement part of the limit, at position 4 of the second iterate,
-- recovers the parity of `gutkovskiy 4`.
example : gutkovskiy 4 % 2 = 1 := by
  have h := isOmegaLimit_gutkovskiy_mod_two.2 2 4 (by decide)
  change (1 : ℕ) = gutkovskiy 4 % 2 at h
  exact h.symm

-- The agreement part of the limit, at position 5 of the third iterate,
-- recovers the parity of `gutkovskiy 5`.
example : gutkovskiy 5 % 2 = 0 := by
  have h := isOmegaLimit_gutkovskiy_mod_two.2 3 5 (by decide)
  change (0 : ℕ) = gutkovskiy 5 % 2 at h
  exact h.symm
