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

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMap

/-!
# Outer-reindex coherence for exact-functor maps of Quillen Stage grids

Exact-functor maps of retained Quillen simplices, raw Stage-grid agreements,
and Stage-grid lifts commute strictly with outer simplex reindexing.  The
central coherence identifies the exact-functor simplex comparison before and
after reindexing, including the endpoint transports carried by the existing
shell-reindex equalities.

This file constructs no nerve, diagonal or realization map, exact-functor
identity/composition theorem, weak equivalence, group comparison, spectrum
map, or Q/S equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v₁ u₁ v₂ u₂

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance quillenStageGridMapReindexWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

local instance quillenStageGridMapReindexWaldhausenD : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

private theorem edgewiseStageWeakReindex_map
    {a b : SimplexCategory} (α : a ⟶ b) :
    edgewiseStageWeakReindex (C := C) α ⋙
        mapStageWeak C D F (edgewiseQ.obj a).len =
      mapStageWeak C D F (edgewiseQ.obj b).len ⋙
        edgewiseStageWeakReindex (C := D) α := by
  exact mapStageWeak_reindex C D F (edgewiseQ.map α)

private theorem edgewiseQuillenSimplexReindex_map
    {a b : SimplexCategory} (α : a ⟶ b) :
    edgewiseQuillenSimplexReindex (C := C) α ⋙
        (QuillenQ.map F).mapComposableArrows a.len =
      (QuillenQ.map F).mapComposableArrows b.len ⋙
        edgewiseQuillenSimplexReindex (C := D) α := by
  rfl

/-- The discrete exact-functor action on retained Quillen simplices commutes
strictly with outer reindexing. -/
theorem quillenQSimplexDiscreteMap_reindex
    {a b : SimplexCategory} (α : a ⟶ b) :
    quillenQSimplexDiscreteReindex (C := C) α ⋙
        quillenQSimplexDiscreteMap F a =
      quillenQSimplexDiscreteMap F b ⋙
        quillenQSimplexDiscreteReindex (C := D) α := by
  apply Discrete.functor_ext
  intro q
  rfl

/-- Source-functor equality used by the exact-functor simplex comparison
after outer reindexing. -/
theorem edgewiseStageQuillenSimplexFunctor_mapIso_reindex_source
    {a b : SimplexCategory} (α : a ⟶ b) :
    edgewiseStageWeakReindex (C := C) α ⋙
          mapStageWeak C D F (edgewiseQ.obj a).len ⋙
            edgewiseStageQuillenSimplexFunctor D a =
      mapStageWeak C D F (edgewiseQ.obj b).len ⋙
          edgewiseStageQuillenSimplexFunctor D b ⋙
            edgewiseQuillenSimplexReindex (C := D) α := by
  calc
    _ = (mapStageWeak C D F (edgewiseQ.obj b).len ⋙
          edgewiseStageWeakReindex (C := D) α) ⋙
            edgewiseStageQuillenSimplexFunctor D a := by
      exact congrArg (fun G ↦ G ⋙ edgewiseStageQuillenSimplexFunctor D a)
        (edgewiseStageWeakReindex_map F α)
    _ = mapStageWeak C D F (edgewiseQ.obj b).len ⋙
          (edgewiseStageWeakReindex (C := D) α ⋙
            edgewiseStageQuillenSimplexFunctor D a) := rfl
    _ = _ := by
      rw [edgewiseStageQuillenSimplexFunctor_reindex (C := D) α]

/-- Target-functor equality used by the exact-functor simplex comparison
after outer reindexing. -/
theorem edgewiseStageQuillenSimplexFunctor_mapIso_reindex_target
    {a b : SimplexCategory} (α : a ⟶ b) :
    edgewiseStageWeakReindex (C := C) α ⋙
          edgewiseStageQuillenSimplexFunctor C a ⋙
            (QuillenQ.map F).mapComposableArrows a.len =
      edgewiseStageQuillenSimplexFunctor C b ⋙
          (QuillenQ.map F).mapComposableArrows b.len ⋙
            edgewiseQuillenSimplexReindex (C := D) α := by
  calc
    _ = (edgewiseStageQuillenSimplexFunctor C b ⋙
          edgewiseQuillenSimplexReindex (C := C) α) ⋙
            (QuillenQ.map F).mapComposableArrows a.len := by
      exact congrArg
        (fun G ↦ G ⋙ (QuillenQ.map F).mapComposableArrows a.len)
        (edgewiseStageQuillenSimplexFunctor_reindex (C := C) α)
    _ = edgewiseStageQuillenSimplexFunctor C b ⋙
          (edgewiseQuillenSimplexReindex (C := C) α ⋙
            (QuillenQ.map F).mapComposableArrows a.len) := rfl
    _ = _ := by
      rw [edgewiseQuillenSimplexReindex_map F α]

private theorem edgewiseUnderlyingVertexMapIso_hom_id
    {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    (QuillenQ.underlyingIso (edgewiseStageVertexMapIso F A k)).hom =
      𝟙 _ := by
  change (QuillenQ.underlyingIso (F.mapIso (Iso.refl _))).hom = 𝟙 _
  rw [← congrArg Iso.hom (QuillenQ.underlyingIso_map F (Iso.refl _))]
  rw [QuillenQ.underlyingIso_refl]
  exact (QuillenQ.map F).map_id _

set_option backward.isDefEq.respectTransparency false in
/-- The exact-functor natural isomorphism between extracted Quillen
simplices is coherent with outer reindexing. -/
theorem edgewiseStageQuillenSimplexFunctor_mapIso_reindex
    {a b : SimplexCategory} (α : a ⟶ b) :
    Functor.whiskerLeft (edgewiseStageWeakReindex (C := C) α)
          (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom ≫
        eqToHom
          (edgewiseStageQuillenSimplexFunctor_mapIso_reindex_target F α) =
      eqToHom
          (edgewiseStageQuillenSimplexFunctor_mapIso_reindex_source F α) ≫
        Functor.whiskerRight
          (edgewiseStageQuillenSimplexFunctor_mapIso F b).hom
          (edgewiseQuillenSimplexReindex (C := D) α) := by
  apply NatTrans.ext
  funext A
  apply NatTrans.ext
  funext k
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, eqToHom_app]
  simp only [edgewiseStageQuillenSimplexFunctor_mapIso_hom_app_app]
  change (QuillenQ.underlyingIso
      (edgewiseStageVertexMapIso F
        ((edgewiseStageWeakReindex (C := C) α).obj A) k)).hom ≫
      eqToHom _ =
    eqToHom _ ≫
      (QuillenQ.underlyingIso
        (edgewiseStageVertexMapIso F A (α.toOrderHom k))).hom
  rw [edgewiseUnderlyingVertexMapIso_hom_id,
    edgewiseUnderlyingVertexMapIso_hom_id,
    Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Exact-functor maps of raw Stage-grid agreements commute strictly with
outer reindexing. -/
theorem quillenStageGridAgreementMap_reindex
    {a b : SimplexCategory} (α : a ⟶ b) :
    reindexQuillenStageGridAgreement (C := C) α ⋙
        quillenStageGridAgreementMap F a =
      quillenStageGridAgreementMap F b ⋙
        reindexQuillenStageGridAgreement (C := D) α := by
  let hG := edgewiseStageWeakReindex_map F α
  let hQ := edgewiseQuillenSimplexReindex_map F α
  let hD := quillenQSimplexDiscreteMap_reindex F α
  let hObj : ∀ X : QuillenStageGridAgreement C b,
      (reindexQuillenStageGridAgreement (C := C) α ⋙
        quillenStageGridAgreementMap F a).obj X =
      (quillenStageGridAgreementMap F b ⋙
        reindexQuillenStageGridAgreement (C := D) α).obj X := fun X ↦ by
    rcases X with ⟨left, right, hom⟩
    change ({
      left := (mapStageWeak C D F (edgewiseQ.obj a).len).obj
        ((edgewiseStageWeakReindex (C := C) α).obj left)
      right := (quillenQSimplexDiscreteMap F a).obj
        ((quillenQSimplexDiscreteReindex (C := C) α).obj right)
      hom :=
        (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app
            ((edgewiseStageWeakReindex (C := C) α).obj left) ≫
          ((QuillenQ.map F).mapComposableArrows a.len).map
            ((eqToHom (edgewiseStageQuillenSimplexFunctor_reindex
                (C := C) α)).app left ≫
              (edgewiseQuillenSimplexReindex (C := C) α).map hom ≫
              (eqToHom (quillenQSimplexDiscreteInclusion_reindex
                (C := C) α)).app right) ≫
          (eqToHom (quillenQSimplexDiscreteInclusion_map F a)).app
            ((quillenQSimplexDiscreteReindex (C := C) α).obj right)
      } : QuillenStageGridAgreement D a) = ({
      left := (edgewiseStageWeakReindex (C := D) α).obj
        ((mapStageWeak C D F (edgewiseQ.obj b).len).obj left)
      right := (quillenQSimplexDiscreteReindex (C := D) α).obj
        ((quillenQSimplexDiscreteMap F b).obj right)
      hom :=
        (eqToHom (edgewiseStageQuillenSimplexFunctor_reindex
          (C := D) α)).app
            ((mapStageWeak C D F (edgewiseQ.obj b).len).obj left) ≫
          (edgewiseQuillenSimplexReindex (C := D) α).map
            ((edgewiseStageQuillenSimplexFunctor_mapIso F b).hom.app left ≫
              ((QuillenQ.map F).mapComposableArrows b.len).map hom ≫
              (eqToHom (quillenQSimplexDiscreteInclusion_map F b)).app right) ≫
          (eqToHom (quillenQSimplexDiscreteInclusion_reindex
            (C := D) α)).app
              ((quillenQSimplexDiscreteMap F b).obj right)
      } : QuillenStageGridAgreement D a)
    rw [Comma.mk.injEq]
    refine ⟨Functor.congr_obj hG left, Functor.congr_obj hD right, ?_⟩
    simp only [eqToHom_app, Functor.map_comp, eqToHom_map,
      ← Category.assoc, comp_eqToHom_heq_iff,
      heq_comp_eqToHom_iff]
    have hIso := heq_of_eq (NatTrans.congr_app
      (edgewiseStageQuillenSimplexFunctor_mapIso_reindex F α) left)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, eqToHom_app] at hIso
    exact heq_comp rfl rfl rfl hIso (Functor.hcongr_hom hQ hom)
  refine CategoryTheory.Functor.ext hObj ?_
  intro X Y f
  apply Comma.hom_ext
  · change (mapStageWeak C D F (edgewiseQ.obj a).len).map
        ((edgewiseStageWeakReindex (C := C) α).map f.left) =
      (eqToHom (hObj X)).left ≫
        (edgewiseStageWeakReindex (C := D) α).map
          ((mapStageWeak C D F (edgewiseQ.obj b).len).map f.left) ≫
        (eqToHom (hObj Y).symm).left
    have h := Functor.congr_hom hG f.left
    change (mapStageWeak C D F (edgewiseQ.obj a).len).map
        ((edgewiseStageWeakReindex (C := C) α).map f.left) =
      eqToHom _ ≫
        (edgewiseStageWeakReindex (C := D) α).map
          ((mapStageWeak C D F (edgewiseQ.obj b).len).map f.left) ≫
        eqToHom _ at h
    simpa only [Comma.eqToHom_left] using h
  · exact Subsingleton.elim _ _

private theorem quillenStageGridLiftMap_reindex_obj
    {a b : SimplexCategory} (α : a ⟶ b) :
    ∀ X : QuillenStageGridLift C b,
      (reindexQuillenStageGridLift (C := C) α ⋙
        quillenStageGridLiftMap F a).obj X =
      (quillenStageGridLiftMap F b ⋙
        reindexQuillenStageGridLift (C := D) α).obj X := by
  intro X
  exact ObjectProperty.FullSubcategory.ext (Functor.congr_obj
    (quillenStageGridAgreementMap_reindex F α) X.obj)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenStageGridLiftMap_reindex_map
    {a b : SimplexCategory} (α : a ⟶ b)
    {X Y : QuillenStageGridLift C b} (f : X ⟶ Y) :
    (reindexQuillenStageGridLift (C := C) α ⋙
        quillenStageGridLiftMap F a).map f =
      eqToHom (quillenStageGridLiftMap_reindex_obj F α X) ≫
        (quillenStageGridLiftMap F b ⋙
          reindexQuillenStageGridLift (C := D) α).map f ≫
        eqToHom (quillenStageGridLiftMap_reindex_obj F α Y).symm := by
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · change (mapStageWeak C D F (edgewiseQ.obj a).len).map
        ((edgewiseStageWeakReindex (C := C) α).map f.hom.left) =
      ((eqToHom (quillenStageGridLiftMap_reindex_obj F α X)).hom).left ≫
        (edgewiseStageWeakReindex (C := D) α).map
          ((mapStageWeak C D F (edgewiseQ.obj b).len).map f.hom.left) ≫
        ((eqToHom
          (quillenStageGridLiftMap_reindex_obj F α Y).symm).hom).left
    have h := Functor.congr_hom
      (edgewiseStageWeakReindex_map F α) f.hom.left
    change (mapStageWeak C D F (edgewiseQ.obj a).len).map
        ((edgewiseStageWeakReindex (C := C) α).map f.hom.left) =
      eqToHom _ ≫
        (edgewiseStageWeakReindex (C := D) α).map
          ((mapStageWeak C D F (edgewiseQ.obj b).len).map f.hom.left) ≫
        eqToHom _ at h
    simpa only [ObjectProperty.eqToHom_hom, Comma.eqToHom_left] using h
  · exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- Exact-functor maps of Quillen Stage-grid lifts commute strictly with
outer reindexing. -/
theorem quillenStageGridLiftMap_reindex
    {a b : SimplexCategory} (α : a ⟶ b) :
    reindexQuillenStageGridLift (C := C) α ⋙
        quillenStageGridLiftMap F a =
      quillenStageGridLiftMap F b ⋙
        reindexQuillenStageGridLift (C := D) α := by
  refine CategoryTheory.Functor.ext
    (quillenStageGridLiftMap_reindex_obj F α) ?_
  intro X Y f
  exact quillenStageGridLiftMap_reindex_map F α f

end AlgebraicKTheory

end
