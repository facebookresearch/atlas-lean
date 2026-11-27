/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedResiduePartCompositions

namespace MetaMathlibExt

-- Check the original type and named arguments through the production import.
example (k n r s : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (hsr : s < r) :
    compositionOddMinusEven (n + k - 1)
        (fun c => ∀ a ∈ c.blocks, k ≤ a ∧ a % r = (k + s) % r)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if r * i + j * (k + s) + s + 1 = n then (-1 : ℤ) ^ j * ((i + j).choose i : ℤ)
          else 0 :=
  compositionOddMinusEven_parts_ge_modEq (k := k) (n := n) (r := r) (s := s) hk hn hsr

-- For total four, the congruent parts `[2, 2]` are excluded by the lower bound `k = 3`.
example : compositionOddMinusEven (2 + 3 - 1)
    (fun c => ∀ a ∈ c.blocks, 3 ≤ a ∧ a % 3 = (3 + 2) % 3) = 0 := by
  rw [compositionOddMinusEven_parts_ge_modEq 3 2 3 2 (by decide) (by decide) (by decide)]
  decide

-- At `n = s + 1`, just the single part `k + s` is possible.
example : compositionOddMinusEven (2 + 3 - 1)
    (fun c => ∀ a ∈ c.blocks, 3 ≤ a ∧ a % 2 = (3 + 1) % 2) = 1 := by
  rw [compositionOddMinusEven_parts_ge_modEq 3 2 2 1 (by decide) (by decide) (by decide)]
  decide

-- For total ten, `[10]` contributes +1 and `[4, 6]`, `[6, 4]` each contribute −1.
example : compositionOddMinusEven (8 + 3 - 1)
    (fun c => ∀ a ∈ c.blocks, 3 ≤ a ∧ a % 2 = (3 + 1) % 2) = -1 := by
  rw [compositionOddMinusEven_parts_ge_modEq 3 8 2 1 (by decide) (by decide) (by decide)]
  decide

-- Modulus one with zero offset places no further restriction on the parts.
example : compositionOddMinusEven (3 + 2 - 1)
    (fun c => ∀ a ∈ c.blocks, 2 ≤ a ∧ a % 1 = (2 + 0) % 1) = 0 := by
  rw [compositionOddMinusEven_parts_ge_modEq 2 3 1 0 (by decide) (by decide) (by decide)]
  decide

end MetaMathlibExt
