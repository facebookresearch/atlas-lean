/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.MaximalSubgroupsSpecial

open MathlibExt.GroupTheory.MaximalSubgroupsSpecialKourovka16Problem13Wanted

-- At p = 2, a size bound already excludes the example with a trivial maximal subgroup.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup 2 G ∧ 4 < Nat.card G ∧
    ∀ H : Subgroup G, IsCoatom H → ¬ IsMulCommutative H := by
  obtain ⟨G, inst, fin, hP, hsize, hmax⟩ :=
    largePGroupsWithSpecialMaximalSubgroups_holds 2 Nat.prime_two 4
  refine ⟨G, inst, fin, hP, hsize, ?_⟩
  intro H hH hc
  have hcenter := (hmax H hH).1
  rw [Subgroup.center_eq_top_iff.mpr hc, (commutator_eq_bot_iff H).mpr hc] at hcenter
  have hcard := (Subgroup.eq_bot_iff_card (H := (⊤ : Subgroup H))).mp hcenter
  rw [Subgroup.card_top] at hcard
  have := hP.isNilpotent
  have horder := H.index_mul_card
  rw [hP.isCoatom_iff_index_eq_prime.mp hH, hcard] at horder
  omega

-- A nontrivial elementary abelian group fails the center/commutator equality.
example : ¬ IsSpecialGroup (Multiplicative (ZMod 2)) := by
  intro h
  have heq := h.1
  rw [Subgroup.center_eq_top, commutator_eq_bot] at heq
  exact top_ne_bot heq
