/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Code.Walls.rc3_core
import Code.Inequalities.PerOrbitCardClose
import Code.Walls.rc2_slabimgeqinter

open Finset
open scoped StatMech

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*}









def pocDiffer (k : ConfigSpace α × ConfigSpace α) : Set α := {a | k.1 a ≠ k.2 a}

@[simp] theorem mem_pocDiffer (k : ConfigSpace α × ConfigSpace α) (a : α) :
    a ∈ pocDiffer k ↔ k.1 a ≠ k.2 a := Iff.rfl


abbrev DifferSub (k : ConfigSpace α × ConfigSpace α) := {a : α // k.1 a ≠ k.2 a}










def pocRestrict (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    ConfigSpace (DifferSub k) := fun s => ω s.1

@[simp] theorem pocRestrict_apply (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α)
    (s : DifferSub k) : pocRestrict k ω s = ω s.1 := rfl





noncomputable def pocUnrestrict (k : ConfigSpace α × ConfigSpace α)
    (σ : ConfigSpace (DifferSub k)) : ConfigSpace α := by
  classical
  exact fun a => if h : k.1 a ≠ k.2 a then σ ⟨a, h⟩ else k.1 a


theorem pocUnrestrict_apply_differ (k : ConfigSpace α × ConfigSpace α)
    (σ : ConfigSpace (DifferSub k)) {a : α} (h : k.1 a ≠ k.2 a) :
    pocUnrestrict k σ a = σ ⟨a, h⟩ := by
  simp only [pocUnrestrict, dif_pos h]


theorem pocUnrestrict_apply_nondiffer (k : ConfigSpace α × ConfigSpace α)
    (σ : ConfigSpace (DifferSub k)) {a : α} (h : k.1 a = k.2 a) :
    pocUnrestrict k σ a = k.1 a := by
  simp only [pocUnrestrict, dif_neg (by simp [h] : ¬ k.1 a ≠ k.2 a)]



@[simp] theorem pocRestrict_pocUnrestrict (k : ConfigSpace α × ConfigSpace α)
    (σ : ConfigSpace (DifferSub k)) : pocRestrict k (pocUnrestrict k σ) = σ := by
  funext s
  simp only [pocRestrict_apply]
  exact pocUnrestrict_apply_differ k σ s.2










noncomputable def pocFrozenRestrict (k : ConfigSpace α × ConfigSpace α)
    (A : Set (ConfigSpace α)) : Set (ConfigSpace (DifferSub k)) := pocUnrestrict k ⁻¹' A

@[simp] theorem mem_pocFrozenRestrict (k : ConfigSpace α × ConfigSpace α)
    (A : Set (ConfigSpace α)) (σ : ConfigSpace (DifferSub k)) :
    σ ∈ pocFrozenRestrict k A ↔ pocUnrestrict k σ ∈ A := Iff.rfl



def pocRestrictWitness (k : ConfigSpace α × ConfigSpace α) (K : Set α) :
    Set (DifferSub k) := {s | s.1 ∈ K}

@[simp] theorem mem_pocRestrictWitness (k : ConfigSpace α × ConfigSpace α) (K : Set α)
    (s : DifferSub k) : s ∈ pocRestrictWitness k K ↔ s.1 ∈ K := Iff.rfl

















theorem rc4_agreeOn_unrestrict_of_restrict {k : ConfigSpace α × ConfigSpace α}
    {K : Set α} {ω : ConfigSpace α} {σ' : ConfigSpace (DifferSub k)}
    (hfroz : ∀ a, k.1 a = k.2 a → ω a = k.1 a)
    (hagree : agreeOn (pocRestrictWitness k K) (pocRestrict k ω) σ') :
    agreeOn K ω (pocUnrestrict k σ') := by
  intro a haK
  by_cases h : k.1 a ≠ k.2 a
  · 
    rw [pocUnrestrict_apply_differ k σ' h]
    exact hagree ⟨a, h⟩ haK
  · 
    rw [not_ne_iff] at h
    rw [pocUnrestrict_apply_nondiffer k σ' h, hfroz a h]


















theorem rc4_occurs_restrict_witness_frozen {k : ConfigSpace α × ConfigSpace α}
    {A : Set (ConfigSpace α)} {K : Set α} {ω : ConfigSpace α}
    (hfroz : ∀ a, k.1 a = k.2 a → ω a = k.1 a)
    (hocc : OccursOn A K ω) :
    OccursOn (pocFrozenRestrict k A) (pocRestrictWitness k K) (pocRestrict k ω) := by
  intro σ' hagree
  rw [mem_pocFrozenRestrict]
  exact hocc _ (rc4_agreeOn_unrestrict_of_restrict hfroz hagree)





theorem rc4_occurs_restrict_witness {k : ConfigSpace α × ConfigSpace α}
    {A : Set (ConfigSpace α)} {K : Set α} {ω : ConfigSpace α}
    (hslab : ω ∈ rc2_slab k) (hocc : OccursOn A K ω) :
    OccursOn (pocFrozenRestrict k A) (pocRestrictWitness k K) (pocRestrict k ω) :=
  rc4_occurs_restrict_witness_frozen (fun a ha => rc3_core_slab_frozen hslab a ha) hocc










theorem topKey_differ (a : α) : (poc_topKey : ConfigSpace α × ConfigSpace α).1 a ≠ poc_topKey.2 a :=
  by simp [poc_topKey]




theorem pocUnrestrict_pocRestrict_top (ω : ConfigSpace α) :
    pocUnrestrict (poc_topKey : ConfigSpace α × ConfigSpace α) (pocRestrict poc_topKey ω) = ω := by
  funext a
  rw [pocUnrestrict_apply_differ _ _ (topKey_differ a)]
  rfl





theorem rc4_occurs_restrict_witness_top {A : Set (ConfigSpace α)} {K : Set α} {ω : ConfigSpace α}
    (hocc : OccursOn A K ω) :
    OccursOn (pocFrozenRestrict (poc_topKey : ConfigSpace α × ConfigSpace α) A)
      (pocRestrictWitness poc_topKey K) (pocRestrict poc_topKey ω) :=
  rc4_occurs_restrict_witness_frozen
    (fun a ha => absurd ha (topKey_differ a)) hocc

end StatMech.Walls
