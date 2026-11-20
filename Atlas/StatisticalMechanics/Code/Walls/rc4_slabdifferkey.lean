/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Code.Walls.rc2_slabimgeqinter

open Finset

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*}















theorem rc4_slab_differ_key {k : ConfigSpace α × ConfigSpace α} {ω : ConfigSpace α}
    (hk : ω ∈ rc2_slab k) (a : α) (hne : k.1 a ≠ k.2 a) :
    k.1 a = true ∧ k.2 a = false := by
  rw [rc2_mem_slab] at hk
  
  have hor := congrFun (congrArg Prod.fst hk) a
  
  have hand := congrFun (congrArg Prod.snd hk) a
  simp only [orbitKey, poc_keyFlip, poc_flip,
    show (decide (k.1 a ≠ k.2 a)) = true by simp [hne], if_true] at hor hand
  
  cases hw : ω a <;> simp_all















theorem rc4_keyFlip_eq_not_on_differ (k : ConfigSpace α × ConfigSpace α)
    (ω : ConfigSpace α) (a : α) (hne : k.1 a ≠ k.2 a) :
    poc_keyFlip k ω a = !ω a := by
  simp only [poc_keyFlip, poc_flip, show (decide (k.1 a ≠ k.2 a)) = true by simp [hne], if_true]






theorem rc4_keyFlip_eq_id_off_differ (k : ConfigSpace α × ConfigSpace α)
    (ω : ConfigSpace α) (a : α) (heq : k.1 a = k.2 a) :
    poc_keyFlip k ω a = ω a := by
  simp only [poc_keyFlip, poc_flip, show (decide (k.1 a ≠ k.2 a)) = false by simp [heq],
    Bool.false_eq_true, if_false]





theorem rc4_keyFlip_apply (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α)
    (a : α) [Decidable (k.1 a ≠ k.2 a)] :
    poc_keyFlip k ω a = if k.1 a ≠ k.2 a then !ω a else ω a := by
  by_cases hne : k.1 a ≠ k.2 a
  · rw [rc4_keyFlip_eq_not_on_differ k ω a hne, if_pos hne]
  · rw [rc4_keyFlip_eq_id_off_differ k ω a (not_not.mp hne), if_neg hne]










theorem rc4_topKey_differ (a : α) :
    (poc_topKey : ConfigSpace α × ConfigSpace α).1 a ≠
      (poc_topKey : ConfigSpace α × ConfigSpace α).2 a := by
  simp only [poc_topKey]; decide




theorem rc4_slab_differ_key_top {ω : ConfigSpace α}
    (hk : ω ∈ rc2_slab (poc_topKey : ConfigSpace α × ConfigSpace α)) (a : α) :
    (poc_topKey : ConfigSpace α × ConfigSpace α).1 a = true ∧
      (poc_topKey : ConfigSpace α × ConfigSpace α).2 a = false :=
  rc4_slab_differ_key hk a (rc4_topKey_differ a)





theorem rc4_keyFlip_top_eq_not (ω : ConfigSpace α) (a : α) :
    poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω a = !ω a :=
  rc4_keyFlip_eq_not_on_differ poc_topKey ω a (rc4_topKey_differ a)

end StatMech.Walls
