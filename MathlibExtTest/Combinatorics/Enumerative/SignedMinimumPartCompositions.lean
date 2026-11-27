/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedMinimumPartCompositions

namespace MetaMathlibExt

-- Check the original type and named arguments through the production import.
example (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    compositionOddMinusEven (n + k - 1) (fun c => ∀ a ∈ c.blocks, k ≤ a)
      = ∑ j ∈ Finset.range ((n - 1) / k + 1),
          (-1 : ℤ) ^ j * ((n - 1 - j * (k - 1)).choose j : ℤ) :=
  compositionOddMinusEven_parts_ge (k := k) (n := n) hk hn

-- At n = 1, only the single part k is possible.
example (k : ℕ) (hk : 1 ≤ k) :
    compositionOddMinusEven (1 + k - 1) (fun c => ∀ a ∈ c.blocks, k ≤ a) = 1 := by
  simpa using compositionOddMinusEven_parts_ge k 1 hk (by decide)

-- At the first cutoff the two-part composition [3, 3] cancels the one-part composition [6].
example : compositionOddMinusEven 6 (fun c => ∀ a ∈ c.blocks, 3 ≤ a) = 0 := by
  rw [show 6 = 4 + 3 - 1 by decide, compositionOddMinusEven_parts_ge 3 4 (by decide) (by decide)]
  decide

-- For total nine, one one-part and one three-part composition contribute +1 each,
-- and four two-part compositions contribute -1 each.
example : compositionOddMinusEven 9 (fun c => ∀ a ∈ c.blocks, 3 ≤ a) = -2 := by
  rw [show 9 = 7 + 3 - 1 by decide, compositionOddMinusEven_parts_ge 3 7 (by decide) (by decide)]
  decide

-- At k = 1, all positive parts are allowed.
example : compositionOddMinusEven 4 (fun c => ∀ a ∈ c.blocks, 1 ≤ a) = 0 := by
  rw [show 4 = 4 + 1 - 1 by decide, compositionOddMinusEven_parts_ge 1 4 (by decide) (by decide)]
  decide

end MetaMathlibExt
