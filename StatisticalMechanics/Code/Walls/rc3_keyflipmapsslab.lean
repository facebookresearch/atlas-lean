/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































import Code.Walls.rc2_core

open Finset
open scoped StatMech

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








omit [Fintype α] [DecidableEq α] in



theorem rc3_kfms_keyFlip_involutive (k : ConfigSpace α × ConfigSpace α) :
    Function.Involutive (poc_keyFlip k) :=
  fun ω => rc2_keyFlip_involutive_on_slab k ω

omit [Fintype α] [DecidableEq α] in


theorem rc3_kfms_orbitKey_symm (a b : ConfigSpace α) : orbitKey (a, b) = orbitKey (b, a) :=
  rc2_orbitKey_symm a b









omit [Fintype α] [DecidableEq α] in






theorem rc3_keyFlip_maps_slab (k : ConfigSpace α × ConfigSpace α) {ω : ConfigSpace α}
    (hω : ω ∈ rc2_slab k) : poc_keyFlip k ω ∈ rc2_slab k := by
  rw [rc2_mem_slab] at hω ⊢
  rw [rc3_kfms_keyFlip_involutive k ω, rc3_kfms_orbitKey_symm]
  exact hω







omit [Fintype α] [DecidableEq α] in

theorem rc3_keyFlip_mapsTo_slab (k : ConfigSpace α × ConfigSpace α) :
    Set.MapsTo (poc_keyFlip k) (rc2_slab k) (rc2_slab k) :=
  fun _ hω => rc3_keyFlip_maps_slab k hω

omit [Fintype α] [DecidableEq α] in

theorem rc3_keyFlip_invOn_slab (k : ConfigSpace α × ConfigSpace α) :
    Set.InvOn (poc_keyFlip k) (poc_keyFlip k) (rc2_slab k) (rc2_slab k) :=
  ⟨fun ω _ => rc3_kfms_keyFlip_involutive k ω, fun ω _ => rc3_kfms_keyFlip_involutive k ω⟩

omit [Fintype α] [DecidableEq α] in

theorem rc3_keyFlip_injOn_slab (k : ConfigSpace α × ConfigSpace α) :
    Set.InjOn (poc_keyFlip k) (rc2_slab k) :=
  (rc3_keyFlip_invOn_slab k).1.injOn

omit [Fintype α] [DecidableEq α] in





theorem rc3_keyFlip_bijOn_slab (k : ConfigSpace α × ConfigSpace α) :
    Set.BijOn (poc_keyFlip k) (rc2_slab k) (rc2_slab k) :=
  (rc3_keyFlip_invOn_slab k).bijOn (rc3_keyFlip_mapsTo_slab k) (rc3_keyFlip_mapsTo_slab k)







omit [Fintype α] [DecidableEq α] in



theorem rc3_mem_slab_top (ω : ConfigSpace α) :
    ω ∈ rc2_slab (poc_topKey : ConfigSpace α × ConfigSpace α) := by
  rw [rc2_mem_slab]
  exact poc_orbitKey_top ω

end StatMech.Walls
