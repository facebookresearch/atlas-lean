/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import MathlibExt.Combinatorics.Additive.ConsecutiveWeightedZeroSumProd
import MathlibExt.Combinatorics.Additive.ConsecutiveZeroSum

open MetaMathlibExt

-- Sharp with nonempty blocks and separators, using the same integer weight `1` throughout.
example : 2 * 2 ≤ 4 := by
  have h := consecutive_prod_ge (A := ({1} : Set ℤ))
    (hM := consecutive_constant_eq_card (ZMod 2)) (hN := consecutive_constant_eq_card (ZMod 2))
    (h := consecutive_constant_eq_card (ZMod 2 × ZMod 2))
  simp only [Fintype.card_prod, ZMod.card] at h
  exact h

-- No first-coordinate letters when the first constant is `1`.
example : 1 * 2 ≤ 2 := by
  have h := consecutive_prod_ge (A := ({1} : Set ℤ))
    (hM := consecutive_constant_eq_card (ZMod 1)) (hN := consecutive_constant_eq_card (ZMod 2))
    (h := consecutive_constant_eq_card (ZMod 1 × ZMod 2))
  simp only [Fintype.card_prod, ZMod.card] at h
  exact h

-- No separators when the second constant is `1`.
example : 2 * 1 ≤ 2 := by
  have h := consecutive_prod_ge (A := ({1} : Set ℤ))
    (hM := consecutive_constant_eq_card (ZMod 2)) (hN := consecutive_constant_eq_card (ZMod 1))
    (h := consecutive_constant_eq_card (ZMod 2 × ZMod 1))
  simp only [Fintype.card_prod, ZMod.card] at h
  exact h
