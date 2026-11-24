/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import
  MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellFunctorReindex
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Degreewise Stage-grid lifts of Quillen simplices

A degreewise lift consists of one material edgewise weak Stage, one retained
Quillen simplex, and an isomorphism from the simplex extracted from the Stage
to the retained simplex.  The Quillen side is discrete, so morphisms retain
an equality of Q-simplices rather than an arbitrary natural transformation.

The construction is functorial under outer simplex reindexing.  This file
constructs no inverse from a Q-simplex to a grid, no fiber contractibility,
nerve, diagonal, realization, or Q/S comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenStageGridLiftWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- Type of degree-`a` Quillen simplices. -/
abbrev QuillenQSimplex (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :=
  ComposableArrows (QuillenQ C) a.len

/-- Inclusion of the discrete category of retained Quillen simplices. -/
def quillenQSimplexDiscreteInclusion (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] (a : SimplexCategory) :
    Discrete (QuillenQSimplex C a) ⥤ QuillenQSimplex C a :=
  Discrete.functor (fun q : QuillenQSimplex C a ↦ q)

/-- Raw comma category of a grid, a retained Q-simplex, and an agreement
map between them. -/
abbrev QuillenStageGridAgreement (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] (a : SimplexCategory) :=
  Comma (edgewiseStageQuillenSimplexFunctor C a)
    (quillenQSimplexDiscreteInclusion C a)

/-- The agreement in a raw grid packet is required to be an isomorphism. -/
def quillenStageGridIsLift (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] (a : SimplexCategory) :
    ObjectProperty (QuillenStageGridAgreement C a) :=
  fun X ↦ IsIso X.hom

/-- Degreewise iso-comma category of Stage-grid lifts. -/
abbrev QuillenStageGridLift (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] (a : SimplexCategory) :=
  (quillenStageGridIsLift C a).FullSubcategory

namespace QuillenStageGridLift

/-- Material weak Stage carried by a grid lift. -/
abbrev grid {a : SimplexCategory} (X : QuillenStageGridLift C a) :
    StageWeakCategory C (edgewiseQ.obj a).len :=
  X.obj.left

/-- Retained Quillen simplex carried by a grid lift. -/
abbrev q {a : SimplexCategory} (X : QuillenStageGridLift C a) :
    QuillenQSimplex C a :=
  X.obj.right.as

theorem agreement_isIso {a : SimplexCategory}
    (X : QuillenStageGridLift C a) : IsIso X.obj.hom := by
  simpa only [quillenStageGridIsLift] using X.property

/-- Stored agreement, promoted from an isomorphism witness. -/
@[reducible]
noncomputable def agreementIso {a : SimplexCategory}
    (X : QuillenStageGridLift C a) :
    (edgewiseStageQuillenSimplexFunctor C a).obj X.grid ≅ X.q :=
  @asIso _ _ _ _ X.obj.hom (agreement_isIso X)

@[simp]
theorem agreementIso_hom {a : SimplexCategory}
    (X : QuillenStageGridLift C a) :
    X.agreementIso.hom = X.obj.hom :=
  by
    unfold agreementIso
    rfl

/-- Agreement on every interval of the retained Q-simplex. -/
theorem shell_agreement {a : SimplexCategory}
    (X : QuillenStageGridLift C a)
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    edgewiseStageShellClassNormalized X.grid.obj k l hkl ≫
        X.agreementIso.hom.app l =
      X.agreementIso.hom.app k ≫ X.q.map (homOfLE hkl) := by
  exact X.agreementIso.hom.naturality (homOfLE hkl)

/-- Canonical lift built from a material grid and identity agreement. -/
noncomputable def ofGrid {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    QuillenStageGridLift C a := by
  let q := (edgewiseStageQuillenSimplexFunctor C a).obj A
  let X : QuillenStageGridAgreement C a :=
    { left := A
      right := Discrete.mk q
      hom := 𝟙 q }
  exact ⟨X, by
    change IsIso (𝟙 q)
    infer_instance⟩

@[simp]
theorem ofGrid_grid {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    (ofGrid A).grid = A :=
  rfl

@[simp]
theorem ofGrid_q {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    (ofGrid A).q = (edgewiseStageQuillenSimplexFunctor C a).obj A :=
  rfl

@[simp]
theorem ofGrid_agreementIso_hom {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    (ofGrid A).agreementIso.hom = 𝟙 _ :=
  by
    simp [agreementIso, ofGrid]

end QuillenStageGridLift

/-- Projection from a grid lift to its material weak Stage. -/
def quillenStageGridProjection (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] (a : SimplexCategory) :
    QuillenStageGridLift C a ⥤
      (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
        StageWeakCategory C (edgewiseQ.obj a).len) :=
  (quillenStageGridIsLift C a).ι ⋙
    Comma.fst (edgewiseStageQuillenSimplexFunctor C a)
      (quillenQSimplexDiscreteInclusion C a)

/-- Projection from a grid lift to its retained discrete Quillen simplex. -/
def quillenStageGridQProjection (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] (a : SimplexCategory) :
    QuillenStageGridLift C a ⥤ Discrete (QuillenQSimplex C a) :=
  (quillenStageGridIsLift C a).ι ⋙
    Comma.snd (edgewiseStageQuillenSimplexFunctor C a)
      (quillenQSimplexDiscreteInclusion C a)

/-- Discrete reindexing of retained Quillen simplices. -/
def quillenQSimplexDiscreteReindex {a b : SimplexCategory} (α : a ⟶ b) :
    Discrete (QuillenQSimplex C b) ⥤
      Discrete (QuillenQSimplex C a) :=
  Discrete.functor (fun q : QuillenQSimplex C b ↦
    Discrete.mk ((edgewiseQuillenSimplexReindex (C := C) α).obj q))

@[simp]
theorem edgewiseStageWeakReindex_id (a : SimplexCategory) :
    edgewiseStageWeakReindex (C := C) (𝟙 a) =
      𝟭 (StageWeakCategory C (edgewiseQ.obj a).len) := by
  change reindexStageWeak C (edgewiseQ.map (𝟙 a)) = _
  rw [edgewiseQ.map_id, reindexStageWeak_id]

@[simp]
theorem edgewiseStageWeakReindex_comp
    {a b c : SimplexCategory} (α : a ⟶ b) (β : b ⟶ c) :
    edgewiseStageWeakReindex (C := C) (α ≫ β) =
      edgewiseStageWeakReindex (C := C) β ⋙
        edgewiseStageWeakReindex (C := C) α := by
  change reindexStageWeak C (edgewiseQ.map (α ≫ β)) =
    reindexStageWeak C (edgewiseQ.map β) ⋙
      reindexStageWeak C (edgewiseQ.map α)
  rw [edgewiseQ.map_comp, reindexStageWeak_comp]

/-- The discrete inclusion commutes strictly with Q-simplex reindexing. -/
theorem quillenQSimplexDiscreteInclusion_reindex
    {a b : SimplexCategory} (α : a ⟶ b) :
    quillenQSimplexDiscreteInclusion C b ⋙
        edgewiseQuillenSimplexReindex (C := C) α =
      quillenQSimplexDiscreteReindex (C := C) α ⋙
        quillenQSimplexDiscreteInclusion C a := by
  apply Discrete.functor_ext
  intro q
  rfl

@[simp]
theorem quillenQSimplexDiscreteReindex_id (a : SimplexCategory) :
    quillenQSimplexDiscreteReindex (C := C) (𝟙 a) =
      𝟭 (Discrete (QuillenQSimplex C a)) := by
  let hObj : ∀ q : Discrete (QuillenQSimplex C a),
      (quillenQSimplexDiscreteReindex (C := C) (𝟙 a)).obj q = q := by
    rintro ⟨q⟩
    exact congrArg Discrete.mk
      (Functor.congr_obj (edgewiseQuillenSimplexReindex_id (C := C) a) q)
  refine CategoryTheory.Functor.ext hObj ?_
  intro q r f
  exact Subsingleton.elim _ _

@[simp]
theorem quillenQSimplexDiscreteReindex_comp
    {a b c : SimplexCategory} (α : a ⟶ b) (β : b ⟶ c) :
    quillenQSimplexDiscreteReindex (C := C) (α ≫ β) =
      quillenQSimplexDiscreteReindex (C := C) β ⋙
        quillenQSimplexDiscreteReindex (C := C) α := by
  let hObj : ∀ q : Discrete (QuillenQSimplex C c),
      (quillenQSimplexDiscreteReindex (C := C) (α ≫ β)).obj q =
        (quillenQSimplexDiscreteReindex (C := C) β ⋙
          quillenQSimplexDiscreteReindex (C := C) α).obj q := by
    rintro ⟨q⟩
    exact congrArg Discrete.mk
      (Functor.congr_obj
        (edgewiseQuillenSimplexReindex_comp (C := C) α β) q)
  refine CategoryTheory.Functor.ext hObj ?_
  intro q r f
  exact Subsingleton.elim _ _

@[reducible]
noncomputable def reindexQuillenStageGridAgreement
    {a b : SimplexCategory} (α : a ⟶ b) :
    QuillenStageGridAgreement C b ⥤ QuillenStageGridAgreement C a :=
  Comma.map
    (F₁ := edgewiseStageWeakReindex (C := C) α)
    (F₂ := quillenQSimplexDiscreteReindex (C := C) α)
    (F := edgewiseQuillenSimplexReindex (C := C) α)
    (eqToIso (edgewiseStageQuillenSimplexFunctor_reindex
      (C := C) α)).hom
    (eqToIso (quillenQSimplexDiscreteInclusion_reindex
      (C := C) α)).hom

set_option linter.style.haveILetI false in
theorem reindexQuillenStageGridAgreement_isLift
    {a b : SimplexCategory} (α : a ⟶ b)
    (X : QuillenStageGridLift C b) :
    IsIso ((reindexQuillenStageGridAgreement (C := C) α).obj X.obj).hom := by
  have hX := X.property
  change IsIso X.obj.hom at hX
  letI : IsIso X.obj.hom := hX
  have hMap : IsIso
      ((edgewiseQuillenSimplexReindex (C := C) α).map X.obj.hom) :=
    @Functor.map_isIso _ _ _ _ _ _
      (edgewiseQuillenSimplexReindex (C := C) α) X.obj.hom hX
  letI : IsIso
      ((edgewiseQuillenSimplexReindex (C := C) α).map X.obj.hom) := hMap
  change IsIso
    ((eqToIso (edgewiseStageQuillenSimplexFunctor_reindex
        (C := C) α)).hom.app X.obj.left ≫
      (edgewiseQuillenSimplexReindex (C := C) α).map X.obj.hom ≫
      (eqToIso (quillenQSimplexDiscreteInclusion_reindex
        (C := C) α)).hom.app X.obj.right)
  exact IsIso.comp_isIso' (by infer_instance)
    (IsIso.comp_isIso' hMap (by infer_instance))

/-- Outer reindexing of degreewise Stage-grid lifts. -/
@[reducible]
noncomputable def reindexQuillenStageGridLift
    {a b : SimplexCategory} (α : a ⟶ b) :
    QuillenStageGridLift C b ⥤ QuillenStageGridLift C a where
  obj X := ⟨(reindexQuillenStageGridAgreement (C := C) α).obj X.obj,
    reindexQuillenStageGridAgreement_isLift α X⟩
  map f := ObjectProperty.homMk
    ((reindexQuillenStageGridAgreement (C := C) α).map f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · exact Subsingleton.elim _ _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · exact Subsingleton.elim _ _

@[simp]
theorem reindexQuillenStageGridLift_obj_grid
    {a b : SimplexCategory} (α : a ⟶ b)
    (X : QuillenStageGridLift C b) :
    ((reindexQuillenStageGridLift (C := C) α).obj X).grid =
      (edgewiseStageWeakReindex (C := C) α).obj X.grid :=
  rfl

@[simp]
theorem reindexQuillenStageGridLift_obj_q
    {a b : SimplexCategory} (α : a ⟶ b)
    (X : QuillenStageGridLift C b) :
    ((reindexQuillenStageGridLift (C := C) α).obj X).q =
      (edgewiseQuillenSimplexReindex (C := C) α).obj X.q :=
  rfl

/-- Outer reindexing is strictly unital. -/
@[simp]
theorem reindexQuillenStageGridLift_id (a : SimplexCategory) :
    reindexQuillenStageGridLift (C := C) (𝟙 a) =
      𝟭 (QuillenStageGridLift C a) := by
  let hG := edgewiseStageWeakReindex_id (C := C) a
  let hQ := edgewiseQuillenSimplexReindex_id (C := C) a
  let hD := quillenQSimplexDiscreteReindex_id (C := C) a
  let hObj : ∀ X : QuillenStageGridLift C a,
      (reindexQuillenStageGridLift (C := C) (𝟙 a)).obj X = X := fun X ↦ by
    apply ObjectProperty.FullSubcategory.ext
    rcases X with ⟨⟨left, right, hom⟩, property⟩
    change ({
      left := (edgewiseStageWeakReindex (C := C) (𝟙 a)).obj left
      right := (quillenQSimplexDiscreteReindex (C := C) (𝟙 a)).obj right
      hom := (eqToHom (edgewiseStageQuillenSimplexFunctor_reindex
          (C := C) (𝟙 a))).app left ≫
        (edgewiseQuillenSimplexReindex (C := C) (𝟙 a)).map hom ≫
        (eqToHom (quillenQSimplexDiscreteInclusion_reindex
          (C := C) (𝟙 a))).app right } : QuillenStageGridAgreement C a) =
      { left := left, right := right, hom := hom }
    rw [Comma.mk.injEq]
    refine ⟨Functor.congr_obj hG left, Functor.congr_obj hD right, ?_⟩
    simp only [eqToHom_app, eqToHom_comp_heq_iff,
      comp_eqToHom_heq_iff]
    exact Functor.hcongr_hom hQ hom
  refine CategoryTheory.Functor.ext hObj ?_
  intro X Y f
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · change (edgewiseStageWeakReindex (C := C) (𝟙 a)).map f.hom.left =
      ((eqToHom (hObj X)).hom).left ≫ f.hom.left ≫
        ((eqToHom (hObj Y).symm).hom).left
    have h := Functor.congr_hom hG f.hom.left
    change (edgewiseStageWeakReindex (C := C) (𝟙 a)).map f.hom.left =
      eqToHom _ ≫ f.hom.left ≫ eqToHom _ at h
    simpa only [ObjectProperty.eqToHom_hom, Comma.eqToHom_left] using
      h
  · exact Subsingleton.elim _ _

/-- Outer reindexing is strictly contravariant under composition. -/
@[simp]
theorem reindexQuillenStageGridLift_comp
    {a b c : SimplexCategory} (α : a ⟶ b) (β : b ⟶ c) :
    reindexQuillenStageGridLift (C := C) (α ≫ β) =
      reindexQuillenStageGridLift (C := C) β ⋙
        reindexQuillenStageGridLift (C := C) α := by
  let hG := edgewiseStageWeakReindex_comp (C := C) α β
  let hQ := edgewiseQuillenSimplexReindex_comp (C := C) α β
  let hD := quillenQSimplexDiscreteReindex_comp (C := C) α β
  let hObj : ∀ X : QuillenStageGridLift C c,
      (reindexQuillenStageGridLift (C := C) (α ≫ β)).obj X =
        (reindexQuillenStageGridLift (C := C) β ⋙
          reindexQuillenStageGridLift (C := C) α).obj X := fun X ↦ by
    apply ObjectProperty.FullSubcategory.ext
    rcases X with ⟨⟨left, right, hom⟩, property⟩
    change ({
      left := (edgewiseStageWeakReindex (C := C) (α ≫ β)).obj left
      right := (quillenQSimplexDiscreteReindex (C := C) (α ≫ β)).obj right
      hom := (eqToHom (edgewiseStageQuillenSimplexFunctor_reindex
          (C := C) (α ≫ β))).app left ≫
        (edgewiseQuillenSimplexReindex (C := C) (α ≫ β)).map hom ≫
        (eqToHom (quillenQSimplexDiscreteInclusion_reindex
          (C := C) (α ≫ β))).app right } : QuillenStageGridAgreement C a) =
      ({
        left := (edgewiseStageWeakReindex (C := C) α).obj
          ((edgewiseStageWeakReindex (C := C) β).obj left)
        right := (quillenQSimplexDiscreteReindex (C := C) α).obj
          ((quillenQSimplexDiscreteReindex (C := C) β).obj right)
        hom := (eqToHom (edgewiseStageQuillenSimplexFunctor_reindex
            (C := C) α)).app
              ((edgewiseStageWeakReindex (C := C) β).obj left) ≫
          (edgewiseQuillenSimplexReindex (C := C) α).map
            ((eqToHom (edgewiseStageQuillenSimplexFunctor_reindex
                (C := C) β)).app left ≫
              (edgewiseQuillenSimplexReindex (C := C) β).map hom ≫
              (eqToHom (quillenQSimplexDiscreteInclusion_reindex
                (C := C) β)).app right) ≫
          (eqToHom (quillenQSimplexDiscreteInclusion_reindex
            (C := C) α)).app
              ((quillenQSimplexDiscreteReindex (C := C) β).obj right)
        } : QuillenStageGridAgreement C a)
    rw [Comma.mk.injEq]
    refine ⟨Functor.congr_obj hG left, Functor.congr_obj hD right, ?_⟩
    simp only [eqToHom_app, Functor.map_comp, eqToHom_map,
      ← Category.assoc, eqToHom_trans, eqToHom_comp_heq_iff,
      comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    exact Functor.hcongr_hom hQ hom
  refine CategoryTheory.Functor.ext hObj ?_
  intro X Y f
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · change (edgewiseStageWeakReindex (C := C) (α ≫ β)).map
        f.hom.left = ((eqToHom (hObj X)).hom).left ≫
          (edgewiseStageWeakReindex (C := C) α).map
            ((edgewiseStageWeakReindex (C := C) β).map f.hom.left) ≫
          ((eqToHom (hObj Y).symm).hom).left
    have h := Functor.congr_hom hG f.hom.left
    change (edgewiseStageWeakReindex (C := C) (α ≫ β)).map
        f.hom.left = eqToHom _ ≫
          (edgewiseStageWeakReindex (C := C) α).map
            ((edgewiseStageWeakReindex (C := C) β).map f.hom.left) ≫
          eqToHom _ at h
    simpa only [ObjectProperty.eqToHom_hom, Comma.eqToHom_left] using
      h
  · exact Subsingleton.elim _ _

/-- Reindexing commutes strictly with the material-grid projection. -/
theorem reindexQuillenStageGridLift_comp_gridProjection
    {a b : SimplexCategory} (α : a ⟶ b) :
    reindexQuillenStageGridLift (C := C) α ⋙
        quillenStageGridProjection C a =
      quillenStageGridProjection C b ⋙
        edgewiseStageWeakReindex (C := C) α := by
  rfl

/-- Reindexing commutes strictly with the discrete Q-simplex projection. -/
theorem reindexQuillenStageGridLift_comp_qProjection
    {a b : SimplexCategory} (α : a ⟶ b) :
    reindexQuillenStageGridLift (C := C) α ⋙
        quillenStageGridQProjection C a =
      quillenStageGridQProjection C b ⋙
        quillenQSimplexDiscreteReindex (C := C) α := by
  rfl

end AlgebraicKTheory

end
