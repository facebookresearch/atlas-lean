/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedResidueClassCompositions

namespace MetaMathlibExt

-- Check the original type and named arguments through the production import.
example (n r s : ℕ) (hn : 1 ≤ n) (hsr : s < r) :
    compositionOddMinusEven (n + (r - s) - 1)
        (fun c => ∀ a ∈ c.blocks, r - s ≤ a ∧ a % r = (r - s + s) % r)
      = if n = s + 1 then 1 else 0 :=
  compositionOddMinusEven_parts_ge_modEq_sub (n := n) (r := r) (s := s) hn hsr

-- A total not divisible by three admits no composition with the required parts.
example : compositionOddMinusEven 2 (fun c => ∀ a ∈ c.blocks, 1 ≤ a ∧ a % 3 = 0) = 0 :=
  compositionOddMinusEven_parts_ge_modEq_sub 2 3 2 (by decide) (by decide)

-- The total three admits just the one-part composition [3].
example : compositionOddMinusEven 3 (fun c => ∀ a ∈ c.blocks, 1 ≤ a ∧ a % 3 = 0) = 1 :=
  compositionOddMinusEven_parts_ge_modEq_sub 3 3 2 (by decide) (by decide)

-- The odd compositions [6] and [2, 2, 2] cancel the even ones [2, 4] and [4, 2].
example : compositionOddMinusEven 6 (fun c => ∀ a ∈ c.blocks, 1 ≤ a ∧ a % 2 = 0) = 0 :=
  compositionOddMinusEven_parts_ge_modEq_sub 6 2 1 (by decide) (by decide)

end MetaMathlibExt
