/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TwoGroupAbelianRankOrderBoundKourovka19Problem75
import Mathlib.GroupTheory.Rank

/-! # Tests for Sambale's order bound -/

namespace MathlibExtTest.GroupTheory.TwoGroupAbelianRankOrderBoundKourovka19Problem75

open MathlibExt.GroupTheory.TwoGroupAbelianRankOrderBoundKourovka19Problem75Wanted

-- Recover the counterexample in terms of the intrinsic group rank of each abelian subgroup.
-- The exponent-one case cannot witness a strict failure of the bound.
example : ∃ (P : Type) (_ : Group P) (_ : Finite P) (e r : ℕ),
    IsPGroup 2 P ∧ 0 < e ∧ Monoid.exponent P = 2 ^ e ∧
    (∀ A : Subgroup P, IsMulCommutative A → Group.rank A ≤ r) ∧
    2 ^ (r * (e + 1)) < Nat.card P := by
  classical
  by_contra h
  apply twoGroupOrderBoundByAbelianRank_refuted
  intro P _ _ hp e r he hgen
  by_contra! hlt
  apply h
  refine ⟨P, inferInstance, inferInstance, e, r, hp, ?_, he, ?_, hlt⟩
  · by_contra! hzero
    have : Subsingleton P := Monoid.exp_eq_one_iff.mp
      (by simpa [Nat.eq_zero_of_le_zero hzero] using he)
    rw [Nat.card_unique] at hlt
    exact (Nat.one_le_pow _ _ (by decide)).not_gt hlt
  · intro A hA
    obtain ⟨s, hs, hclosure⟩ := hgen A fun x hx y hy ↦
      congrArg Subtype.val (isMulCommutative_iff.mp hA ⟨x, hx⟩ ⟨y, hy⟩)
    calc
      Group.rank A = Group.rank (Subgroup.closure (s : Set P)) := Subgroup.rank_congr hclosure.symm
      _ ≤ s.card := Subgroup.rank_closure_finset_le_card s
      _ ≤ r := hs

end MathlibExtTest.GroupTheory.TwoGroupAbelianRankOrderBoundKourovka19Problem75
