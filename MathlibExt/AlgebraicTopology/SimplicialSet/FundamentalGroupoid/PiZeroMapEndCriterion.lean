/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# A π₀ and automorphism-group criterion for fundamental groupoids

A simplicial map induces an equivalence on fundamental groupoids if it is
bijective on connected components and bijective on the automorphism group of
every represented source vertex. The proof promotes this based information to
fullness and faithfulness on arbitrary objects and hom-sets.

This is a combinatorial groupoid criterion. It makes no realization, unit,
weak-equivalence, Kan-complex, or model-category claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet

private def fundamentalGroupoidToPiZero {X : SSet.{u}}
    (a : SSet.FundamentalGroupoid X) : SSet.π₀ X :=
  SSet.π₀.mk a.pt

@[simp]
private lemma fundamentalGroupoidToPiZero_mk {X : SSet.{u}}
    (x : X _⦋0⦌) :
    fundamentalGroupoidToPiZero (SSet.FundamentalGroupoid.mk x) =
      SSet.π₀.mk x :=
  rfl

private lemma fundamentalGroupoidToPiZero_eq_of_hom {X : SSet.{u}}
    {a b : SSet.FundamentalGroupoid X} (φ : a ⟶ b) :
    fundamentalGroupoidToPiZero a = fundamentalGroupoidToPiZero b := by
  induction φ using SSet.FundamentalGroupoid.hom_rec with
  | homMk e => exact SSet.π₀.sound e
  | inv f hf => exact hf.symm
  | comp f g hf hg => exact hf.trans hg

private lemma fundamentalGroupoidToPiZero_eq_iff_nonempty_iso
    {X : SSet.{u}} (a b : SSet.FundamentalGroupoid X) :
    fundamentalGroupoidToPiZero a = fundamentalGroupoidToPiZero b ↔
      Nonempty (a ≅ b) := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := SSet.FundamentalGroupoid.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.FundamentalGroupoid.mk_surjective b
    rw [fundamentalGroupoidToPiZero_mk,
      fundamentalGroupoidToPiZero_mk, SSet.π₀.mk_eq_mk_iff] at h
    induction h with
    | rel x y h =>
        obtain ⟨e⟩ := h
        exact ⟨asIso (SSet.FundamentalGroupoid.homMk e)⟩
    | refl => exact ⟨Iso.refl _⟩
    | symm _ _ _ ih => exact ⟨ih.some.symm⟩
    | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some.trans ih₂.some⟩
  · rintro ⟨e⟩
    exact fundamentalGroupoidToPiZero_eq_of_hom e.hom

private lemma mapPiZero_surjective_iff_essSurj
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    Function.Surjective (SSet.mapπ₀ f) ↔
      (SSet.mapFundamentalGroupoid f).EssSurj := by
  constructor
  · intro hf
    constructor
    intro b
    obtain ⟨a, ha⟩ := hf (SSet.π₀.mk b.pt)
    obtain ⟨x, rfl⟩ := a.mk_surjective
    refine ⟨SSet.FundamentalGroupoid.mk x,
      (fundamentalGroupoidToPiZero_eq_iff_nonempty_iso _ _).mp ?_⟩
    change SSet.π₀.mk (f.app _ x) = SSet.π₀.mk b.pt
    exact ha
  · intro hf b
    obtain ⟨y, rfl⟩ := b.mk_surjective
    obtain ⟨a, ⟨e⟩⟩ :=
      hf.mem_essImage (SSet.FundamentalGroupoid.mk y)
    obtain ⟨x, rfl⟩ := SSet.FundamentalGroupoid.mk_surjective a
    refine ⟨SSet.π₀.mk x, ?_⟩
    have hcomp := (fundamentalGroupoidToPiZero_eq_iff_nonempty_iso
      ((SSet.mapFundamentalGroupoid f).obj
        (SSet.FundamentalGroupoid.mk x))
      (SSet.FundamentalGroupoid.mk y)).mpr ⟨e⟩
    change SSet.π₀.mk (f.app _ x) = SSet.π₀.mk y at hcomp
    simpa only [SSet.mapπ₀_mk] using hcomp

private lemma mapPiZero_injective_reflects_iso
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : Function.Injective (SSet.mapπ₀ f))
    (a b : SSet.FundamentalGroupoid X)
    (h : Nonempty ((SSet.mapFundamentalGroupoid f).obj a ≅
      (SSet.mapFundamentalGroupoid f).obj b)) :
    Nonempty (a ≅ b) := by
  apply (fundamentalGroupoidToPiZero_eq_iff_nonempty_iso _ _).mp
  obtain ⟨x, rfl⟩ := SSet.FundamentalGroupoid.mk_surjective a
  obtain ⟨y, rfl⟩ := SSet.FundamentalGroupoid.mk_surjective b
  apply hf
  change SSet.mapπ₀ f (SSet.π₀.mk x) =
    SSet.mapπ₀ f (SSet.π₀.mk y)
  have hcomp := (fundamentalGroupoidToPiZero_eq_iff_nonempty_iso
    ((SSet.mapFundamentalGroupoid f).obj
      (SSet.FundamentalGroupoid.mk x))
    ((SSet.mapFundamentalGroupoid f).obj
      (SSet.FundamentalGroupoid.mk y))).mpr h
  change SSet.π₀.mk (f.app _ x) = SSet.π₀.mk (f.app _ y) at hcomp
  simpa only [SSet.mapπ₀_mk] using hcomp

/-- A simplicial map that is bijective on connected components and on every
represented-vertex automorphism group induces an equivalence of fundamental
groupoids. -/
theorem isEquivalence_mapFundamentalGroupoid_of_bijective_mapπ₀_mapEnd
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (h₀ : Function.Bijective (SSet.mapπ₀ f))
    (h₁ : ∀ x : X _⦋0⦌, Function.Bijective
      ((SSet.mapFundamentalGroupoid f).map
        (X := SSet.FundamentalGroupoid.mk x)
        (Y := SSet.FundamentalGroupoid.mk x))) :
    (SSet.mapFundamentalGroupoid f).IsEquivalence := by
  let F := SSet.mapFundamentalGroupoid f
  let _ : F.EssSurj := (mapPiZero_surjective_iff_essSurj f).mp h₀.2
  let _ : F.Faithful := ⟨by
    intro a b g g' h
    have e : b ≅ a := (asIso g').symm
    rw [← cancel_mono e.hom]
    apply (h₁ a.pt).1
    simpa only [Functor.map_comp] using
      congrArg (fun k ↦ k ≫ F.map e.hom) h⟩
  let _ : F.Full := ⟨fun {a b} φ ↦ by
    have e : b ≅ a :=
      (mapPiZero_injective_reflects_iso f h₀.1 _ _
        ⟨(asIso φ).symm⟩).some
    obtain ⟨g, hg⟩ := (h₁ a.pt).2 (φ ≫ F.map e.hom)
    exact ⟨g ≫ e.inv, by aesop⟩⟩
  exact {}

end SSet

end
