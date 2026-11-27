/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import all MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory.LiftingTest
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
universe w t uA vA uS uD vD vS uC vC s

open CategoryTheory TypeCat MorphismProperty

namespace MathlibExtTest.DiagramTaggedLiftingTestOwner

section FixedCollection

variable {A : Type uA} [Category.{vA} A] {S : Type uS}
  (T : S → A ⥤ Arrow (Type t))

private theorem entire_collection_object_function :
    (fun (p : A) (z : LiftingTest.CollectionLeft T p) =>
      ((LiftingTest.collectionFunctor T).obj p).hom z) =
    (fun (p : A) (z : LiftingTest.CollectionLeft T p) =>
      (⟨z.1, ((T z.1).obj p).hom z.2⟩ : LiftingTest.CollectionRight T p)) := rfl

private theorem entire_collection_source_map_function :
    (fun (p q : A) (τ : p ⟶ q) (z : LiftingTest.CollectionLeft T p) =>
      ((LiftingTest.collectionFunctor T).map τ).left z) =
    (fun (p q : A) (τ : p ⟶ q) (z : LiftingTest.CollectionLeft T p) =>
      (⟨z.1, ((T z.1).map τ).left z.2⟩ : LiftingTest.CollectionLeft T q)) := rfl

private theorem entire_collection_target_map_function :
    (fun (p q : A) (τ : p ⟶ q) (z : LiftingTest.CollectionRight T p) =>
      ((LiftingTest.collectionFunctor T).map τ).right z) =
    (fun (p q : A) (τ : p ⟶ q) (z : LiftingTest.CollectionRight T p) =>
      (⟨z.1, ((T z.1).map τ).right z.2⟩ : LiftingTest.CollectionRight T q)) := rfl

private theorem original_collection_square_function {p q : A} (τ : p ⟶ q) :
    (fun z : LiftingTest.CollectionLeft T p =>
      ((LiftingTest.collectionFunctor T).map τ).right
        (((LiftingTest.collectionFunctor T).obj p).hom z)) =
    (fun z : LiftingTest.CollectionLeft T p =>
      ((LiftingTest.collectionFunctor T).obj q).hom
        (((LiftingTest.collectionFunctor T).map τ).left z)) := by
  funext z
  exact (ConcreteCategory.congr_hom ((LiftingTest.collectionFunctor T).map τ).w z).symm

private theorem original_collection_all_tags_iff (p : A) :
    Function.Surjective ((LiftingTest.collectionFunctor T).obj p).hom ↔
      ∀ x : S, Function.Surjective ((T x).obj p).hom :=
  LiftingTest.collectionFunctor_surjective_iff T p

end FixedCollection

section OriginalNormalization

variable {A : Type uA} [Category.{vA} A] (T : A ⥤ Arrow (Type t))
  [∀ p, Small.{w} (T.obj p).left] [∀ p, Small.{w} (T.obj p).right]

private theorem normalization_entire_forward_function :
    (fun (p : A) (z : (T.obj p).left) =>
      ((LiftingTest.normalizedFunctor.{w} T).obj p).hom
        (equivShrink.{w} (T.obj p).left z)) =
    (fun (p : A) (z : (T.obj p).left) =>
      equivShrink.{w} (T.obj p).right ((T.obj p).hom z)) := by
  funext p z
  exact congrFun (LiftingTest.normalizedFunctor_hom_function.{w} T p) z

private theorem normalization_entire_inverse_function :
    (fun (p : A) (z : ((LiftingTest.normalizedFunctor.{w} T).obj p).left) =>
      (equivShrink.{w} (T.obj p).right).symm
        (((LiftingTest.normalizedFunctor.{w} T).obj p).hom z)) =
    (fun (p : A) (z : ((LiftingTest.normalizedFunctor.{w} T).obj p).left) =>
      (T.obj p).hom ((equivShrink.{w} (T.obj p).left).symm z)) := by
  funext p z
  exact (equivShrink.{w} (T.obj p).right).symm_apply_apply _

private theorem normalization_entire_source_map_function :
    (fun (p q : A) (τ : p ⟶ q) (z : (T.obj p).left) =>
      ((LiftingTest.normalizedFunctor.{w} T).map τ).left
        (equivShrink.{w} (T.obj p).left z)) =
    (fun (p q : A) (τ : p ⟶ q) (z : (T.obj p).left) =>
      equivShrink.{w} (T.obj q).left ((T.map τ).left z)) := by
  funext p q τ z
  exact congrFun (LiftingTest.normalizedFunctor_map_left_function.{w} T τ) z

private theorem normalization_entire_target_map_function :
    (fun (p q : A) (τ : p ⟶ q) (z : (T.obj p).right) =>
      ((LiftingTest.normalizedFunctor.{w} T).map τ).right
        (equivShrink.{w} (T.obj p).right z)) =
    (fun (p q : A) (τ : p ⟶ q) (z : (T.obj p).right) =>
      equivShrink.{w} (T.obj q).right ((T.map τ).right z)) := by
  funext p q τ z
  exact congrFun (LiftingTest.normalizedFunctor_map_right_function.{w} T τ) z

omit [∀ p, Small.{w} (T.obj p).right] in
private theorem normalization_original_source_roundtrip (p : A) :
    (fun z : (T.obj p).left =>
      (equivShrink.{w} (T.obj p).left).symm
        (equivShrink.{w} (T.obj p).left z)) = id := by
  funext z
  exact (equivShrink.{w} (T.obj p).left).symm_apply_apply z

omit [∀ p, Small.{w} (T.obj p).left] in
private theorem normalization_original_target_roundtrip (p : A) :
    (fun z : (T.obj p).right =>
      (equivShrink.{w} (T.obj p).right).symm
        (equivShrink.{w} (T.obj p).right z)) = id := by
  funext z
  exact (equivShrink.{w} (T.obj p).right).symm_apply_apply z

omit [∀ p, Small.{w} (T.obj p).right] in
private theorem normalization_small_source_roundtrip (p : A) :
    (fun z : Shrink.{w} (T.obj p).left =>
      equivShrink.{w} (T.obj p).left
        ((equivShrink.{w} (T.obj p).left).symm z)) = id := by
  funext z
  exact (equivShrink.{w} (T.obj p).left).apply_symm_apply z

omit [∀ p, Small.{w} (T.obj p).left] in
private theorem normalization_small_target_roundtrip (p : A) :
    (fun z : Shrink.{w} (T.obj p).right =>
      equivShrink.{w} (T.obj p).right
        ((equivShrink.{w} (T.obj p).right).symm z)) = id := by
  funext z
  exact (equivShrink.{w} (T.obj p).right).apply_symm_apply z

private theorem normalization_surjectivity_of_original_function (p : A) :
    Function.Surjective ((LiftingTest.normalizedFunctor.{w} T).obj p).hom ↔
      Function.Surjective (T.obj p).hom :=
  LiftingTest.normalizedFunctor_surjective_iff.{w} T p

end OriginalNormalization

section OriginalComponents

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {C : Type uC} [Category.{vC} C] {ι : Type s}
  [Small.{w} S] [Small.{w} ι] [LocallySmall.{w} C]
  (e : D ≌ S) (f : ι → Arrow C)

private abbrev OriginalComponent (p : Arrow (D ⥤ C)) (x : S) :=
  Arrow.mk (p.hom.app (e.inverse.obj x))

private abbrev OriginalSource (p : Arrow (D ⥤ C)) :=
  Σ x : S, LiftingTest.RawLifts f (OriginalComponent e p x)

private abbrev OriginalTarget (p : Arrow (D ⥤ C)) :=
  Σ x : S, LiftingTest.RawSquares f (OriginalComponent e p x)

private def encodeSource (p : Arrow (D ⥤ C)) (z : OriginalSource e f p) :
    ((LiftingTest.diagramFunctor.{w} e f).obj p).left :=
  equivShrink.{w} ((LiftingTest.diagramCollection.{w} e f).obj p).left
    ⟨z.1, LiftingTest.liftsEquiv.{w} f (OriginalComponent e p z.1) z.2⟩

private def encodeTarget (p : Arrow (D ⥤ C)) (z : OriginalTarget e f p) :
    ((LiftingTest.diagramFunctor.{w} e f).obj p).right :=
  equivShrink.{w} ((LiftingTest.diagramCollection.{w} e f).obj p).right
    ⟨z.1, LiftingTest.squaresEquiv.{w} f (OriginalComponent e p z.1) z.2⟩

private def originalForward (p : Arrow (D ⥤ C)) (z : OriginalSource e f p) :
    OriginalTarget e f p :=
  ⟨z.1, LiftingTest.liftToSquare f (OriginalComponent e p z.1) z.2⟩

private def originalSourceMap {p q : Arrow (D ⥤ C)} (τ : p ⟶ q)
    (z : OriginalSource e f p) : OriginalSource e f q :=
  ⟨z.1, ⟨z.2.1, z.2.2 ≫ τ.left.app (e.inverse.obj z.1)⟩⟩

private def originalTargetMap {p q : Arrow (D ⥤ C)} (τ : p ⟶ q)
    (z : OriginalTarget e f p) : OriginalTarget e f q :=
  ⟨z.1, ⟨z.2.1, z.2.2 ≫
    (Functor.mapArrow ((evaluation D C).obj (e.inverse.obj z.1))).map τ⟩⟩

private theorem entire_original_component_forward_function :
    (fun (p : Arrow (D ⥤ C)) (z : OriginalSource e f p) =>
      ((LiftingTest.diagramFunctor.{w} e f).obj p).hom (encodeSource e f p z)) =
    (fun (p : Arrow (D ⥤ C)) (z : OriginalSource e f p) =>
      encodeTarget e f p (originalForward e f p z)) := by
  funext p z
  let _ : ∀ p, Small.{w} ((LiftingTest.diagramCollection.{w} e f).obj p).left :=
    LiftingTest.diagramCollection_left_small.{w} e f
  let _ : ∀ p, Small.{w} ((LiftingTest.diagramCollection.{w} e f).obj p).right :=
    LiftingTest.diagramCollection_right_small.{w} e f
  let a : ((LiftingTest.diagramCollection.{w} e f).obj p).left :=
    ⟨z.1, LiftingTest.liftsEquiv.{w} f (OriginalComponent e p z.1) z.2⟩
  have hOuter :
    ((LiftingTest.diagramFunctor.{w} e f).obj p).hom (encodeSource e f p z) =
        equivShrink.{w} ((LiftingTest.diagramCollection.{w} e f).obj p).right
          (((LiftingTest.diagramCollection.{w} e f).obj p).hom a) :=
      congrFun (LiftingTest.normalizedFunctor_hom_function.{w}
        (LiftingTest.diagramCollection.{w} e f) p) a
  have hInner :
      equivShrink.{w} ((LiftingTest.diagramCollection.{w} e f).obj p).right
        (((LiftingTest.diagramCollection.{w} e f).obj p).hom a) =
      encodeTarget e f p (originalForward e f p z) := by
    apply congrArg (equivShrink.{w}
      ((LiftingTest.diagramCollection.{w} e f).obj p).right)
    apply congrArg (fun b => (⟨z.1, b⟩ :
      LiftingTest.CollectionRight (LiftingTest.componentFunctor.{w} e f) p))
    exact congrFun (LiftingTest.smallFunctor_hom_function.{w} f
      (OriginalComponent e p z.1)) z.2
  exact hOuter.trans hInner

private theorem entire_original_component_source_map_function :
    (fun (p q : Arrow (D ⥤ C)) (τ : p ⟶ q) (z : OriginalSource e f p) =>
      ((LiftingTest.diagramFunctor.{w} e f).map τ).left (encodeSource e f p z)) =
    (fun (p q : Arrow (D ⥤ C)) (τ : p ⟶ q) (z : OriginalSource e f p) =>
      encodeSource e f q (originalSourceMap e f τ z)) := by
  funext p q τ z
  let _ : ∀ p, Small.{w} ((LiftingTest.diagramCollection.{w} e f).obj p).left :=
    LiftingTest.diagramCollection_left_small.{w} e f
  let _ : ∀ p, Small.{w} ((LiftingTest.diagramCollection.{w} e f).obj p).right :=
    LiftingTest.diagramCollection_right_small.{w} e f
  let a : ((LiftingTest.diagramCollection.{w} e f).obj p).left :=
    ⟨z.1, LiftingTest.liftsEquiv.{w} f (OriginalComponent e p z.1) z.2⟩
  have hOuter :
    ((LiftingTest.diagramFunctor.{w} e f).map τ).left (encodeSource e f p z) =
        equivShrink.{w} ((LiftingTest.diagramCollection.{w} e f).obj q).left
          (((LiftingTest.diagramCollection.{w} e f).map τ).left a) :=
      congrFun (LiftingTest.normalizedFunctor_map_left_function.{w}
        (LiftingTest.diagramCollection.{w} e f) τ) a
  have hInner :
      equivShrink.{w} ((LiftingTest.diagramCollection.{w} e f).obj q).left
        (((LiftingTest.diagramCollection.{w} e f).map τ).left a) =
      encodeSource e f q (originalSourceMap e f τ z) := by
    apply congrArg (equivShrink.{w}
      ((LiftingTest.diagramCollection.{w} e f).obj q).left)
    apply congrArg (fun b => (⟨z.1, b⟩ :
      LiftingTest.CollectionLeft (LiftingTest.componentFunctor.{w} e f) q))
    exact congrFun (LiftingTest.smallFunctor_map_left_function.{w} f
      ((Functor.mapArrow ((evaluation D C).obj (e.inverse.obj z.1))).map τ)) z.2
  exact hOuter.trans hInner

private theorem entire_original_component_target_map_function :
    (fun (p q : Arrow (D ⥤ C)) (τ : p ⟶ q) (z : OriginalTarget e f p) =>
      ((LiftingTest.diagramFunctor.{w} e f).map τ).right (encodeTarget e f p z)) =
    (fun (p q : Arrow (D ⥤ C)) (τ : p ⟶ q) (z : OriginalTarget e f p) =>
      encodeTarget e f q (originalTargetMap e f τ z)) := by
  funext p q τ z
  let _ : ∀ p, Small.{w} ((LiftingTest.diagramCollection.{w} e f).obj p).left :=
    LiftingTest.diagramCollection_left_small.{w} e f
  let _ : ∀ p, Small.{w} ((LiftingTest.diagramCollection.{w} e f).obj p).right :=
    LiftingTest.diagramCollection_right_small.{w} e f
  let a : ((LiftingTest.diagramCollection.{w} e f).obj p).right :=
    ⟨z.1, LiftingTest.squaresEquiv.{w} f (OriginalComponent e p z.1) z.2⟩
  have hOuter :
    ((LiftingTest.diagramFunctor.{w} e f).map τ).right (encodeTarget e f p z) =
        equivShrink.{w} ((LiftingTest.diagramCollection.{w} e f).obj q).right
          (((LiftingTest.diagramCollection.{w} e f).map τ).right a) :=
      congrFun (LiftingTest.normalizedFunctor_map_right_function.{w}
        (LiftingTest.diagramCollection.{w} e f) τ) a
  have hInner :
      equivShrink.{w} ((LiftingTest.diagramCollection.{w} e f).obj q).right
        (((LiftingTest.diagramCollection.{w} e f).map τ).right a) =
      encodeTarget e f q (originalTargetMap e f τ z) := by
    apply congrArg (equivShrink.{w}
      ((LiftingTest.diagramCollection.{w} e f).obj q).right)
    apply congrArg (fun b => (⟨z.1, b⟩ :
      LiftingTest.CollectionRight (LiftingTest.componentFunctor.{w} e f) q))
    exact congrFun (LiftingTest.smallFunctor_map_right_function.{w} f
      ((Functor.mapArrow ((evaluation D C).obj (e.inverse.obj z.1))).map τ)) z.2
  exact hOuter.trans hInner

private theorem original_all_components_right_class (p : Arrow (D ⥤ C)) :
    Function.Surjective ((LiftingTest.diagramFunctor.{w} e f).obj p).hom ↔
      ∀ d : D, (MorphismProperty.ofHoms (fun k => (f k).hom)).rlp (p.hom.app d) :=
  LiftingTest.diagramFunctor_surjective_iff.{w} e f p

omit [Small.{w} S] [LocallySmall.{w} C] in
private theorem original_index_unit_all_four_fields (p : Arrow (D ⥤ C)) (d : D) :
    (unitComponentArrowIso e p.hom d).hom.left = p.left.map (e.unit.app d) ∧
      (unitComponentArrowIso e p.hom d).hom.right = p.right.map (e.unit.app d) ∧
      (unitComponentArrowIso e p.hom d).inv.left = p.left.map (e.unitInv.app d) ∧
      (unitComponentArrowIso e p.hom d).inv.right = p.right.map (e.unitInv.app d) :=
  unitComponentArrowIso_fields e p.hom d

end OriginalComponents
end MathlibExtTest.DiagramTaggedLiftingTestOwner
