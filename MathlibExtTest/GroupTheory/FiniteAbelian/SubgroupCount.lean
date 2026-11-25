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
