/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Derived-subgroup recognition from a proved index bound and an explicit abelian kernel. -/
module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Abelianization.Defs

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement

/-- A subgroup of index at most two in a finite group contains the actual derived subgroup. -/
theorem y322SmallIndex_commutator_le {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hindex : H.index ≤ 2) : commutator G ≤ H := by
  have hpos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcases : H.index = 1 ∨ H.index = 2 := by omega
  rcases hcases with h | h
  · rw [Subgroup.index_eq_one.mp h]
    exact le_top
  · let := H.normal_of_index_eq_two h
    have hc : Nat.card (G ⧸ H) = 2 := by
      rw [← H.index_eq_card]
      exact h
    let := isCyclic_of_prime_card hc
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

/-- An actual abelian-kernel description and index bound identify the independent derived group. -/
theorem y322SmallIndex_derived_eq {G A : Type*} [Group G] [Finite G] [CommGroup A]
    (H : Subgroup G) (sign : G →* A) (hindex : H.index ≤ 2)
    (hkernel : (sign.comp H.subtype).ker = commutator H) :
    commutator G = (commutator H).map H.subtype := by
  apply le_antisymm
  · intro x hx
    have hH := y322SmallIndex_commutator_le H hindex hx
    have hs := Abelianization.commutator_subset_ker sign hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hH⟩, ?_, rfl⟩
    rw [← hkernel]
    exact hs
  · rw [Subgroup.map_subtype_commutator, commutator_def]
    exact Subgroup.commutator_mono le_top le_top

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
