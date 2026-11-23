/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.AtLeastDistinctSumset
import Mathlib.Data.ZMod.Defs

open MetaMathlibExt
open scoped Pointwise

-- Boundary: the only sum of zero terms is the empty sum `0`.
example : atLeastDistinctSumset 0 0 ({1, 2} : Finset ℤ) = {0} := by decide

-- Boundary: asking for more distinct terms than `A` has elements gives the empty set.
example : atLeastDistinctSumset 3 3 ({1, 2} : Finset ℤ) = ∅ := by decide

-- Repetitions are allowed but at least two distinct terms must occur: `0 + 0 + 1` and
-- `0 + 1 + 1` count, `0 + 0 + 0` and `1 + 1 + 1` do not.
example : atLeastDistinctSumset 3 2 ({0, 1} : Finset ℤ) = {1, 2} := by decide

-- The same computation in `ZMod 3`: `0` is not a sum, since `0 + 0 + 0` and `1 + 1 + 1` use a
-- single term.
example : atLeastDistinctSumset 3 2 ({0, 1} : Finset (ZMod 3)) = {1, 2} := by decide

-- For `r = h` only sums of distinct elements remain: `2^(≥ 2) {1, 2, 3} = 2^∧ {1, 2, 3}`.
example : atLeastDistinctSumset 2 2 ({1, 2, 3} : Finset ℤ) = restrictedSumset 2 {1, 2, 3} := by
  decide

-- The decomposition on a concrete set: `3^(≥ 2) {0, 1, 2} = 1 • {0, 1, 2} + 2^∧ {0, 1, 2}`.
example : atLeastDistinctSumset 3 2 ({0, 1, 2} : Finset ℤ) = {1, 2, 3, 4, 5} := by
  rw [atLeastDistinctSumset_eq_nsmul_add_restrictedSumset _ (by decide) 2 3 (by decide)
    (by decide) (by decide)]
  decide

-- The hypothesis `r ≤ h` is needed: for `h = 1 < r = 2` natural subtraction gives
-- `(1 - 2) • A = {0}`, so the right side is `2^∧ {0, 1} = {1}`, while a single term never
-- has two distinct terms.
example : atLeastDistinctSumset 1 2 ({0, 1} : Finset ℤ) = ∅ := by decide
example : (1 - 2) • ({0, 1} : Finset ℤ) + restrictedSumset 2 {0, 1} = {1} := by decide

-- Specialization `r = h`: in any abelian group, `h^(≥ h) A = h^∧ A`.
example {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) (hA : A.Nonempty) (h : ℕ)
    (h1 : 1 ≤ h) (hk : h ≤ A.card) :
    atLeastDistinctSumset h h A = restrictedSumset h A := by
  rw [atLeastDistinctSumset_eq_nsmul_add_restrictedSumset A hA h h h1 hk le_rfl, Nat.sub_self,
    zero_nsmul, zero_add]

-- Specialization `r = 1`: in any abelian group, `h^(≥ 1) A = hA` for `h ≥ 1`.
example {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) (hA : A.Nonempty) (h : ℕ)
    (h1 : 1 ≤ h) :
    atLeastDistinctSumset h 1 A = h • A := by
  have hone : restrictedSumset 1 A = A := by
    ext x
    simp [restrictedSumset, Finset.card_eq_one]
  rw [atLeastDistinctSumset_eq_nsmul_add_restrictedSumset A hA 1 h le_rfl
    (Finset.one_le_card.2 hA) h1, hone, ← succ_nsmul, Nat.sub_add_cancel h1]
