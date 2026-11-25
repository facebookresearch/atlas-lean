/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FiniteAbelian.SubgroupCount

open MetaMathlibExt

variable (G : Type*) [AddCommGroup G] [Finite G]

-- Every subgroup contains zero, so the index-zero family is empty as well.
example : {H : AddSubgroup G | H.index = 0}.ncard = 0 := by
  rw [← ncard_addSubgroup_card_eq_ncard_index_eq]
  simp [Nat.card_pos.ne']

-- The whole group is the unique subgroup of full order.
example : {H : AddSubgroup G | H.index = Nat.card G}.ncard = 1 := by
  rw [← ncard_addSubgroup_card_eq_ncard_index_eq]
  simp [AddSubgroup.card_eq_iff_eq_top]

-- In ℤ/4 × ℤ/2, one index-two subgroup has rank two and two have rank one.
example :
    {H : AddSubgroup ((Fin 1 → ZMod 4) × (Fin 1 → ZMod 2)) |
        H.index = 2 ∧ AddGroup.rank H = 2}.ncard = 1 ∧
      {H : AddSubgroup ((Fin 1 → ZMod 4) × (Fin 1 → ZMod 2)) |
        H.index = 2 ∧ AddGroup.rank H = 1}.ncard = 2 :=
  ncard_index_two_addSubgroup_rank 1 1 (by decide) (fun _ => 2) (fun _ => by decide)

-- When the higher-exponent factor is empty, all three index-two subgroups have rank one.
example :
    {H : AddSubgroup ((Fin 0 → ZMod 4) × (Fin 2 → ZMod 2)) |
        H.index = 2 ∧ AddGroup.rank H = 2}.ncard = 0 ∧
      {H : AddSubgroup ((Fin 0 → ZMod 4) × (Fin 2 → ZMod 2)) |
        H.index = 2 ∧ AddGroup.rank H = 1}.ncard = 3 :=
  ncard_index_two_addSubgroup_rank 0 2 (by decide) (fun _ => 2) (fun _ => by decide)
