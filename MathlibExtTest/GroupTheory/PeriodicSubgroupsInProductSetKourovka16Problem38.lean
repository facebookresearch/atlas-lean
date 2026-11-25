/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PeriodicSubgroupsInProductSetKourovka16Problem38
import Mathlib.GroupTheory.SpecificGroups.Dihedral

open DihedralGroup Pointwise
open MathlibExt.GroupTheory.PeriodicSubgroupsInProductSetKourovka16Problem38Wanted

namespace MathlibExt.GroupTheory.PeriodicSubgroupsInProductSetKourovka16Problem38Wanted.Tests

/-- Rotations form the abelian kernel of the reflection parity map. -/
private theorem dihedral_solvable : Group.IsSolvable (DihedralGroup 0) := by
  let rotations : Multiplicative ℤ →* DihedralGroup 0 :=
    { toFun := fun i => r i.toAdd
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let parity : DihedralGroup 0 →* Multiplicative (ZMod 2) :=
    { toFun := fun | r _ => 1 | sr _ => Multiplicative.ofAdd 1
      map_one' := rfl
      map_mul' := by
        rintro (i | i) (j | j) <;> first | rfl | exact (by decide : (0 : ZMod 2) = 1 + 1) }
  apply Group.isSolvable_of_ker_le_range rotations parity
  rintro (i | i) hi
  · exact ⟨Multiplicative.ofAdd i, rfl⟩
  · exact absurd hi (by decide : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1)

-- The product contains the basic rotation, but cannot contain the subgroup it generates.
example :
    let A := Subgroup.zpowers (sr (0 : ZMod 0))
    let B := Subgroup.zpowers (sr (1 : ZMod 0))
    let t := r (1 : ZMod 0)
    let AB : Set (DihedralGroup 0) := (A : Set _) * (B : Set _)
    t ∈ AB ∧ ¬ (Subgroup.zpowers t : Set (DihedralGroup 0)) ⊆ AB := by
  dsimp only
  constructor
  · exact ⟨_, Subgroup.mem_zpowers _, _, Subgroup.mem_zpowers _, by simp⟩
  · intro h
    have periodic (i : ZMod 0) : IsOfFinOrder (sr i) := by
      rw [← orderOf_pos_iff, orderOf_sr]
      decide
    have ht := subgroupInPeriodicProductIsPeriodic_holds _ dihedral_solvable _ _
      (fun _ hx => (periodic 0).of_mem_zpowers hx) (fun _ hx => (periodic 1).of_mem_zpowers hx)
      _ h _ (Subgroup.mem_zpowers _)
    simp [← orderOf_pos_iff] at ht

end MathlibExt.GroupTheory.PeriodicSubgroupsInProductSetKourovka16Problem38Wanted.Tests
