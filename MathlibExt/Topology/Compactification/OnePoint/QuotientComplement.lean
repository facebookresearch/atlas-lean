/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# One-point compactifications from quotient complements

A quotient of a compact Hausdorff space is a one-point compactification when
the collapsed fibre is closed and the source and target complements are
compatibly homeomorphic to the same space.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set
open scoped OnePoint

universe u v w

namespace OnePoint

/-- A compatible pair of complement homeomorphisms extends across a quotient
point to a homeomorphism from a one-point compactification. -/
noncomputable def homeomorphOfQuotientComplement
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactSpace X] [T2Space X]
    (A : Set X) (q : X → Z) (z : Z) (hA : IsClosed A)
    (hq : Topology.IsQuotientMap q) (hfiber : q ⁻¹' {z} = A)
    (sourceComplement : Y ≃ₜ (Aᶜ : Set X))
    (targetComplement : Y ≃ₜ ({z}ᶜ : Set Z))
    (hcomm : ∀ y, q (sourceComplement y).1 = (targetComplement y).1) :
    OnePoint Y ≃ₜ Z := by
  let g : OnePoint Y → Z := fun p ↦ p.elim z (fun y ↦ (targetComplement y).1)
  have hg_injective : Function.Injective g := by
    intro a b hab
    induction a using OnePoint.rec with
    | infty =>
        induction b using OnePoint.rec with
        | infty => rfl
        | coe b =>
            exfalso
            exact (targetComplement b).2 hab.symm
    | coe a =>
        induction b using OnePoint.rec with
        | infty =>
            exfalso
            exact (targetComplement a).2 hab
        | coe b =>
            apply congrArg OnePoint.some
            apply targetComplement.injective
            exact Subtype.ext hab
  have hg_surjective : Function.Surjective g := by
    intro x
    by_cases hx : x = z
    · exact ⟨∞, by simp [g, hx]⟩
    · let y := targetComplement.symm ⟨x, hx⟩
      refine ⟨(y : OnePoint Y), ?_⟩
      change (targetComplement y).1 = x
      simp [y]
  let e : OnePoint Y ≃ Z := Equiv.ofBijective g ⟨hg_injective, hg_surjective⟩
  apply e.toHomeomorph
  intro U
  let S : Set Y := {y | (targetComplement y).1 ∈ U}
  have hcoe_preimage :
      (fun y : Y ↦ (y : OnePoint Y)) ⁻¹' (g ⁻¹' U) = S :=
    rfl
  have hpreimage_of_notMem (hzU : z ∉ U) :
      q ⁻¹' U = Subtype.val '' (sourceComplement '' S) := by
    ext x
    constructor
    · intro hxU
      have hxne : q x ≠ z := fun hxz ↦ hzU (hxz ▸ hxU)
      have hxA : x ∈ Aᶜ := by
        intro hx
        apply hxne
        have : x ∈ q ⁻¹' {z} := hfiber.symm ▸ hx
        exact this
      obtain ⟨y, hy⟩ := sourceComplement.surjective ⟨x, hxA⟩
      have hyval : (sourceComplement y).1 = x := congrArg Subtype.val hy
      have hyS : y ∈ S := by
        change (targetComplement y).1 ∈ U
        rw [← hcomm y, hyval]
        exact hxU
      exact ⟨sourceComplement y, ⟨y, hyS, rfl⟩, hyval⟩
    · rintro ⟨_, ⟨y, hyS, rfl⟩, rfl⟩
      change q (sourceComplement y).1 ∈ U
      rw [hcomm y]
      exact hyS
  have hpreimage_compl_of_mem (hzU : z ∈ U) :
      (q ⁻¹' U)ᶜ = Subtype.val '' (sourceComplement '' Sᶜ) := by
    ext x
    constructor
    · intro hxU
      have hxne : q x ≠ z := by
        intro hxz
        apply hxU
        change q x ∈ U
        rw [hxz]
        exact hzU
      have hxA : x ∈ Aᶜ := by
        intro hx
        apply hxne
        have : x ∈ q ⁻¹' {z} := hfiber.symm ▸ hx
        exact this
      obtain ⟨y, hy⟩ := sourceComplement.surjective ⟨x, hxA⟩
      have hyval : (sourceComplement y).1 = x := congrArg Subtype.val hy
      have hyS : y ∈ Sᶜ := by
        intro hyS
        apply hxU
        change q x ∈ U
        rw [← hyval, hcomm y]
        exact hyS
      exact ⟨sourceComplement y, ⟨y, hyS, rfl⟩, hyval⟩
    · rintro ⟨_, ⟨y, hyS, rfl⟩, rfl⟩
      intro hyU
      apply hyS
      change (targetComplement y).1 ∈ U
      rw [← hcomm y]
      exact hyU
  change IsOpen (g ⁻¹' U) ↔ IsOpen U
  constructor
  · intro hU
    apply hq.isCoinducing.isOpen_preimage.mp
    by_cases hzU : z ∈ U
    · have hinfty : (∞ : OnePoint Y) ∈ g ⁻¹' U := by
        exact hzU
      have hcompact : IsCompact Sᶜ := by
        have h := (OnePoint.isOpen_iff_of_mem hinfty).1 hU
        rw [hcoe_preimage] at h
        exact h.2
      rw [← isClosed_compl_iff, hpreimage_compl_of_mem hzU]
      exact ((hcompact.image sourceComplement.continuous).image
        continuous_subtype_val).isClosed
    · have hinfty : (∞ : OnePoint Y) ∉ g ⁻¹' U := by
        exact hzU
      have hS : IsOpen S := by
        have h := (OnePoint.isOpen_iff_of_notMem hinfty).1 hU
        rw [hcoe_preimage] at h
        exact h
      rw [hpreimage_of_notMem hzU]
      exact hA.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap _
        (sourceComplement.isOpenMap _ hS)
  · intro hU
    have hS : IsOpen S := by
      exact hU.preimage (continuous_subtype_val.comp targetComplement.continuous)
    by_cases hzU : z ∈ U
    · have hinfty : (∞ : OnePoint Y) ∈ g ⁻¹' U := by
        exact hzU
      apply (OnePoint.isOpen_iff_of_mem hinfty).2
      have hcompactX : IsCompact ((q ⁻¹' U)ᶜ) :=
        (hU.preimage hq.continuous).isClosed_compl.isCompact
      have hcompactVal :
          IsCompact (Subtype.val '' (sourceComplement '' Sᶜ)) := by
        rw [← hpreimage_compl_of_mem hzU]
        exact hcompactX
      have hcompactSubtype : IsCompact (sourceComplement '' Sᶜ) :=
        Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr hcompactVal
      have hcompact : IsCompact Sᶜ :=
        sourceComplement.isEmbedding.isCompact_iff.mpr hcompactSubtype
      rw [hcoe_preimage]
      exact ⟨hS.isClosed_compl, hcompact⟩
    · have hinfty : (∞ : OnePoint Y) ∉ g ⁻¹' U := by
        exact hzU
      apply (OnePoint.isOpen_iff_of_notMem hinfty).2
      rw [hcoe_preimage]
      exact hS

@[simp]
theorem homeomorphOfQuotientComplement_apply_infty
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactSpace X] [T2Space X]
    (A : Set X) (q : X → Z) (z : Z) (hA : IsClosed A)
    (hq : Topology.IsQuotientMap q) (hfiber : q ⁻¹' {z} = A)
    (sourceComplement : Y ≃ₜ (Aᶜ : Set X))
    (targetComplement : Y ≃ₜ ({z}ᶜ : Set Z))
    (hcomm : ∀ y, q (sourceComplement y).1 = (targetComplement y).1) :
    homeomorphOfQuotientComplement A q z hA hq hfiber sourceComplement
      targetComplement hcomm ∞ = z :=
  rfl

@[simp]
theorem homeomorphOfQuotientComplement_apply_coe
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactSpace X] [T2Space X]
    (A : Set X) (q : X → Z) (z : Z) (hA : IsClosed A)
    (hq : Topology.IsQuotientMap q) (hfiber : q ⁻¹' {z} = A)
    (sourceComplement : Y ≃ₜ (Aᶜ : Set X))
    (targetComplement : Y ≃ₜ ({z}ᶜ : Set Z))
    (hcomm : ∀ y, q (sourceComplement y).1 = (targetComplement y).1)
    (y : Y) :
    homeomorphOfQuotientComplement A q z hA hq hfiber sourceComplement
      targetComplement hcomm y = (targetComplement y).1 :=
  rfl

end OnePoint
