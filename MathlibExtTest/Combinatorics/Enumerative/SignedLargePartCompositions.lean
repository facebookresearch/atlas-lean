/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedLargePartCompositions

namespace MetaMathlibExt

-- Check the original type and named argument through the production import.
example (n : ℕ) :
    (∀ j : ℕ, n = 3 * j + 1 ∨ n = 3 * j + 2 →
        compositionOddMinusEven (n + 1) (fun c => ∀ a ∈ c.blocks, 1 < a) = (-1) ^ j) ∧
      ((∀ j : ℕ, n ≠ 3 * j + 1 ∧ n ≠ 3 * j + 2) →
        compositionOddMinusEven (n + 1) (fun c => ∀ a ∈ c.blocks, 1 < a) = 0) :=
  compositionOddMinusEven_parts_gt_one (n := n)

-- At n = 0 no admissible composition exists; at n = 3 the two signs cancel.
example : compositionOddMinusEven 1 (fun c => ∀ a ∈ c.blocks, 1 < a) = 0 :=
  (compositionOddMinusEven_parts_gt_one (n := 0)).2 (by omega)

example : compositionOddMinusEven 4 (fun c => ∀ a ∈ c.blocks, 1 < a) = 0 :=
  (compositionOddMinusEven_parts_gt_one (n := 3)).2 (by omega)

-- Both nonzero residue classes have negative sign at j = 1 and positive sign at j = 2.
example : compositionOddMinusEven 5 (fun c => ∀ a ∈ c.blocks, 1 < a) = -1 := by
  simpa using (compositionOddMinusEven_parts_gt_one (n := 4)).1 1 (Or.inl rfl)

example : compositionOddMinusEven 6 (fun c => ∀ a ∈ c.blocks, 1 < a) = -1 := by
  simpa using (compositionOddMinusEven_parts_gt_one (n := 5)).1 1 (Or.inr rfl)

example : compositionOddMinusEven 8 (fun c => ∀ a ∈ c.blocks, 1 < a) = 1 := by
  simpa using (compositionOddMinusEven_parts_gt_one (n := 7)).1 2 (Or.inl rfl)

example : compositionOddMinusEven 9 (fun c => ∀ a ∈ c.blocks, 1 < a) = 1 := by
  simpa using (compositionOddMinusEven_parts_gt_one (n := 8)).1 2 (Or.inr rfl)

end MetaMathlibExt
