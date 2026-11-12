/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Code.Walls.rmr_reflectinvolution
import Code.Walls.rc3_core

open Finset
open scoped StatMech

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*}










def rc4_differ (k : ConfigSpace α × ConfigSpace α) : Type _ := {a : α // k.1 a ≠ k.2 a}

instance instDecidableEqDiffer (k : ConfigSpace α × ConfigSpace α) [DecidableEq α] :
    DecidableEq (rc4_differ k) :=
  inferInstanceAs (DecidableEq {a : α // k.1 a ≠ k.2 a})

instance instFintypeDiffer (k : ConfigSpace α × ConfigSpace α) [Fintype α] [DecidableEq α] :
    Fintype (rc4_differ k) :=
  inferInstanceAs (Fintype {a : α // k.1 a ≠ k.2 a})





def rc4_restrict (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    ConfigSpace (rc4_differ k) := fun b => ω b.val

@[simp] theorem rc4_restrict_apply (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α)
    (b : rc4_differ k) : rc4_restrict k ω b = ω b.val := rfl










theorem rc4_keyFlip_eq_on_differ (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α)
    (a : α) (ha : k.1 a ≠ k.2 a) : poc_keyFlip k ω a = !(ω a) := by
  simp only [poc_keyFlip, poc_flip,
    show decide (k.1 a ≠ k.2 a) = true from by simp [ha], if_true]




theorem rc4_keyFlip_eq_off_differ (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α)
    (a : α) (ha : k.1 a = k.2 a) : poc_keyFlip k ω a = ω a := by
  simp only [poc_keyFlip, poc_flip,
    show decide (k.1 a ≠ k.2 a) = false from by simp [ha], Bool.false_eq_true, if_false]

















theorem rc4_restrict_keyFlip (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    rc4_restrict k (poc_keyFlip k ω) = rmr_compl (rc4_restrict k ω) := by
  funext b
  obtain ⟨a, ha⟩ := b
  rw [rc4_restrict_apply, rc4_keyFlip_eq_on_differ k ω a ha, rmr_compl_apply, rc4_restrict_apply]



theorem rc4_restrict_keyFlip_apply (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α)
    (b : rc4_differ k) :
    rc4_restrict k (poc_keyFlip k ω) b = !(rc4_restrict k ω b) := by
  rw [rc4_restrict_keyFlip, rmr_compl_apply]











theorem rc4_restrict_keyFlip_keyFlip (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    rc4_restrict k (poc_keyFlip k (poc_keyFlip k ω)) = rc4_restrict k ω := by
  rw [rc4_restrict_keyFlip, rc4_restrict_keyFlip, rmr_compl_involutive]















theorem rc4_keyReflect_mem_via_compl (k : ConfigSpace α × ConfigSpace α)
    {B : Set (ConfigSpace α)} {P : ConfigSpace (rc4_differ k) → Prop}
    (hP : ∀ ω, poc_keyFlip k ω ∈ B ↔ P (rc4_restrict k (poc_keyFlip k ω)))
    (ω : ConfigSpace α) :
    poc_keyFlip k ω ∈ B ↔ P (rmr_compl (rc4_restrict k ω)) := by
  rw [hP ω, rc4_restrict_keyFlip]











theorem rc4_slab_frozen {k : ConfigSpace α × ConfigSpace α} {ω : ConfigSpace α}
    (hk : ω ∈ rc2_slab k) (a : α) (hne : k.1 a = k.2 a) :
    ω a = k.1 a :=
  rc3_core_slab_frozen hk a hne




theorem rc4_slab_differ_key {k : ConfigSpace α × ConfigSpace α} {ω : ConfigSpace α}
    (hk : ω ∈ rc2_slab k) (a : α) (hne : k.1 a ≠ k.2 a) :
    k.1 a = true ∧ k.2 a = false :=
  rc3_core_slab_differ_key hk a hne











theorem rc4_topKey_differ (a : α) :
    (poc_topKey : ConfigSpace α × ConfigSpace α).1 a
      ≠ (poc_topKey : ConfigSpace α × ConfigSpace α).2 a := by
  simp [poc_topKey]






theorem rc4_keyFlip_top_eq_compl (ω : ConfigSpace α) :
    poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω = rmr_compl ω :=
  (rmr_compl_eq_keyFlip_top ω).symm

end StatMech.Walls
