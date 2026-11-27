/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.MinimalNonNilpotentPermutableCoreKourovka17Problem56
import Mathlib.GroupTheory.SpecificGroups.Dihedral

open MathlibExt.GroupTheory.MinimalNonNilpotentPermutableCoreKourovka17Problem56Wanted

-- Even when a subgroup has no proper subgroups, it still has to be non-nilpotent.
example {G : Type*} [Group G] : ¬ IsMinimalNonNilpotent (⊥ : Subgroup G) :=
  fun h => h.1 inferInstance

-- The dihedral group of order ten is minimal non-nilpotent. Its proper subgroups
-- have order one, two or five.
example : IsMinimalNonNilpotent (⊤ : Subgroup (DihedralGroup 5)) := by
  constructor
  · intro h
    have := Group.nilpotent_of_mulEquiv (Subgroup.topEquiv (G := DihedralGroup 5))
    have hc : Commute (DihedralGroup.sr 0 : DihedralGroup 5) (DihedralGroup.r 1) :=
      Group.IsNilpotent.commute_of_orderOf_coprime (by
        rw [DihedralGroup.orderOf_sr, DihedralGroup.orderOf_r_one]
        decide)
    exact (by decide : DihedralGroup.sr 0 * DihedralGroup.r 1 ≠
      DihedralGroup.r 1 * (DihedralGroup.sr 0 : DihedralGroup 5)) hc.eq
  · intro K hK
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hd : Nat.card K ∈ Nat.divisors 10 := Nat.mem_divisors.mpr
      ⟨by simpa only [DihedralGroup.nat_card] using K.card_subgroup_dvd_card, by decide⟩
    have hl : Nat.card K < 10 := by
      simpa only [Subgroup.card_top, DihedralGroup.nat_card] using Subgroup.card_lt_of_lt hK
    rw [show Nat.divisors 10 = {1, 2, 5, 10} by decide] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h | h
    · exact (IsPGroup.of_card (p := 2) (n := 0) h).isNilpotent
    · exact (IsPGroup.of_card (p := 2) (n := 1) h).isNilpotent
    · exact (IsPGroup.of_card (p := 5) (n := 1) h).isNilpotent
    · exact (hl.ne h).elim
