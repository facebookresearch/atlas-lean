/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HelouTerjanianBlockProduct

/-!
# Tests for the Helou–Terjanian block products
-/

open MetaMathlibExt.HelouTerjanian

-- The block between six and nine contains precisely seven and eight.
example : blockProd 3 2 = 56 := by
  rw [blockProd_eq_prod]
  decide

-- For `p = 3`, `a = 1`, and `k = 2`, both sides of the identity independently evaluate to 3360.
example : (9 : ℕ).choose 6 * (∏ j ∈ Finset.range 2, blockProd 3 j) = 3360 ∧
    (3 : ℕ).choose 2 * (∏ j ∈ Finset.range 2, blockProd 3 (1 + j)) = 3360 := by
  simp only [blockProd_eq_prod]
  decide

example : (9 : ℕ).choose 6 * (∏ j ∈ Finset.range 2, blockProd 3 j) =
    (3 : ℕ).choose 2 * (∏ j ∈ Finset.range 2, blockProd 3 (1 + j)) :=
  choose_mul_prod_blockProd 3 1 2 Nat.prime_three (by decide)
