/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import all MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory.LiftingTest
import all MathlibExtTest.CategoryTheory.MorphismProperty.LiftingTestTests
import Mathlib.CategoryTheory.CodiscreteCategory
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
universe w u v s

open CategoryTheory Limits TypeCat MorphismProperty

namespace MathlibExtTest.DiagramTaggedLiftingTest

private theorem point_component_iff (p : Arrow (Type w)) :
    (MorphismProperty.ofHoms (fun k => (TaggedLiftingTest.pointFamily.{w,
        w + 1} k).hom)).rlp p.hom ↔
      Function.Surjective p.hom :=
  (LiftingTest.smallFunctor_surjective_iff.{w} TaggedLiftingTest.pointFamily.{w,
      w + 1} p).symm.trans
    (TaggedLiftingTest.point_small_surjective_iff p)

private theorem fold_component_iff (p : Arrow (Type w)) :
    (MorphismProperty.ofHoms (fun k => (TaggedLiftingTest.foldFamily.{w, w + 1} k).hom)).rlp p.hom ↔
      Function.Injective p.hom :=
  (LiftingTest.smallFunctor_surjective_iff.{w} TaggedLiftingTest.foldFamily.{w, w + 1} p).symm.trans
    (TaggedLiftingTest.fold_small_surjective_iff p)

private theorem original_point_components {D : Type u} [Category.{v} D]
    {S : Type s} [Category S] [Small.{w} S] (e : D ≌ S)
    (p : Arrow (D ⥤ Type w)) :
    Function.Surjective
        ((LiftingTest.diagramFunctor.{w} e TaggedLiftingTest.pointFamily.{w, w + 1}).obj p).hom ↔
      ∀ d : D, Function.Surjective (p.hom.app d) := by
  rw [LiftingTest.diagramFunctor_surjective_iff.{w}]
  apply forall_congr'
  intro d
  exact point_component_iff (Arrow.mk (p.hom.app d))

private theorem original_fold_components {D : Type u} [Category.{v} D]
    {S : Type s} [Category S] [Small.{w} S] (e : D ≌ S)
    (p : Arrow (D ⥤ Type w)) :
    Function.Surjective
        ((LiftingTest.diagramFunctor.{w} e TaggedLiftingTest.foldFamily.{w, w + 1}).obj p).hom ↔
      ∀ d : D, Function.Injective (p.hom.app d) := by
  rw [LiftingTest.diagramFunctor_surjective_iff.{w}]
  apply forall_congr'
  intro d
  exact fold_component_iff (Arrow.mk (p.hom.app d))

private theorem empty_index_test
    {C : Type u} [Category.{v} C] {ι : Type s} [Small.{w} ι] [LocallySmall.{w} C]
    (f : ι → Arrow C) (p : Arrow (Discrete PEmpty ⥤ C)) :
    Function.Surjective
      ((LiftingTest.diagramFunctor.{w} (CategoryTheory.Equivalence.refl (C :=
        Discrete PEmpty)) f).obj p).hom := by
  rw [LiftingTest.diagramFunctor_surjective_iff.{w}]
  intro d
  cases d.as

private abbrev BigIndex := Codiscrete (Type w)

private abbrev SmallIndex := Codiscrete PUnit

private def originalLargeEquivalence : BigIndex.{w} ≌ SmallIndex where
  functor := Codiscrete.functor (fun _ => PUnit.unit)
  inverse := Codiscrete.functor (fun _ => (PUnit.{w + 1} : Type w))
  unitIso := Codiscrete.natIso
  counitIso := Codiscrete.natIso
  functor_unitIso_comp _ := Subsingleton.elim _ _

private theorem original_large_object_type_not_small :
    ¬Small.{w} BigIndex.{w} := by
  intro h
  let _ : Small.{w} BigIndex.{w} := h
  have hType : Small.{w} (Type w) :=
    small_of_surjective (codiscreteEquiv (α := Type w)).surjective
  exact not_small_type hType

private theorem original_large_index_test
    (p : Arrow (BigIndex.{w} ⥤ Type w)) :
    Function.Surjective
        ((LiftingTest.diagramFunctor.{w} originalLargeEquivalence
          TaggedLiftingTest.pointFamily.{w, w + 1}).obj p).hom ↔
      ∀ d : BigIndex.{w}, Function.Surjective (p.hom.app d) :=
  original_point_components originalLargeEquivalence p

private theorem original_large_unit_fields
    (p : Arrow (BigIndex.{w} ⥤ Type w)) (d : BigIndex.{w}) :
    (unitComponentArrowIso originalLargeEquivalence p.hom d).hom.left =
        p.left.map (originalLargeEquivalence.unit.app d) ∧
      (unitComponentArrowIso originalLargeEquivalence p.hom d).hom.right =
        p.right.map (originalLargeEquivalence.unit.app d) ∧
      (unitComponentArrowIso originalLargeEquivalence p.hom d).inv.left =
        p.left.map (originalLargeEquivalence.unitInv.app d) ∧
      (unitComponentArrowIso originalLargeEquivalence p.hom d).inv.right =
        p.right.map (originalLargeEquivalence.unitInv.app d) :=
  unitComponentArrowIso_fields originalLargeEquivalence p.hom d

private abbrev InfiniteNonthin := Discrete Nat × WalkingParallelPair

private def zeroObject (n : Nat) : InfiniteNonthin := (⟨n⟩, WalkingParallelPair.zero)

private def oneObject (n : Nat) : InfiniteNonthin := (⟨n⟩, WalkingParallelPair.one)

private def leftArrow (n : Nat) : zeroObject n ⟶ oneObject n :=
  (𝟙 _, WalkingParallelPairHom.left)

private def rightArrow (n : Nat) : zeroObject n ⟶ oneObject n :=
  (𝟙 _, WalkingParallelPairHom.right)

private theorem infinite_actual_objects : Function.Injective zeroObject := by
  intro n m h
  exact congrArg (fun d : InfiniteNonthin => d.1.as) h

private theorem actual_parallel_arrows_distinct (n : Nat) :
    leftArrow n ≠ rightArrow n := by
  intro h
  have hparallel := congrArg Prod.snd h
  cases hparallel

private def falseMap : PUnit.{w + 1} ⟶ ULift.{w} Bool :=
  ofHom (fun _ => ⟨false⟩)

private def trueMap : PUnit.{w + 1} ⟶ ULift.{w} Bool :=
  ofHom (fun _ => ⟨true⟩)

private def originalParallelDiagram : InfiniteNonthin ⥤ Type w :=
  CategoryTheory.Prod.snd (Discrete Nat) WalkingParallelPair ⋙ parallelPair falseMap trueMap

private def originalPointDiagram : InfiniteNonthin ⥤ Type w :=
  (Functor.const InfiniteNonthin).obj PUnit.{w + 1}

private def originalCollapse : originalParallelDiagram.{w} ⟶ originalPointDiagram where
  app _ := ofHom (fun _ => PUnit.unit)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro z
    rfl

private theorem original_parallel_actions_distinct (n : Nat) :
    originalParallelDiagram.{w}.map (leftArrow n) ≠
      originalParallelDiagram.map (rightArrow n) := by
  intro h
  have hfalseTrue := congrArg ULift.down (ConcreteCategory.congr_hom h PUnit.unit)
  exact Bool.false_ne_true hfalseTrue

private theorem original_collapse_components_surjective (d : InfiniteNonthin) :
    Function.Surjective (originalCollapse.{w}.app d) := by
  intro y
  cases y
  rcases d with ⟨n, d⟩
  cases d
  · exact ⟨PUnit.unit, rfl⟩
  · exact ⟨⟨false⟩, rfl⟩

private theorem original_infinite_nonthin_point_test :
    Function.Surjective
      ((LiftingTest.diagramFunctor.{w} (CategoryTheory.Equivalence.refl (C := InfiniteNonthin))
        TaggedLiftingTest.pointFamily.{w, w + 1}).obj (Arrow.mk originalCollapse)).hom := by
  rw [original_point_components]
  exact original_collapse_components_surjective

private theorem original_infinite_nonthin_fold_test_fails :
    ¬Function.Surjective
      ((LiftingTest.diagramFunctor.{w} (CategoryTheory.Equivalence.refl (C := InfiniteNonthin))
        TaggedLiftingTest.foldFamily.{w, w + 1}).obj (Arrow.mk originalCollapse)).hom := by
  rw [original_fold_components]
  intro h
  have heq : (⟨false⟩ : ULift.{w} Bool) = ⟨true⟩ :=
    h (oneObject 7) rfl
  exact Bool.false_ne_true (congrArg ULift.down heq)

private theorem original_left_action_collapse (n : Nat) :
    originalParallelDiagram.{w}.map (leftArrow n) ≫ originalCollapse.app (oneObject n) =
      originalCollapse.app (zeroObject n) :=
  originalCollapse.naturality (leftArrow n)

private theorem original_right_action_collapse (n : Nat) :
    originalParallelDiagram.{w}.map (rightArrow n) ≫ originalCollapse.app (oneObject n) =
      originalCollapse.app (zeroObject n) :=
  originalCollapse.naturality (rightArrow n)

section DistinctRepresentativeTags

variable (p : Arrow (Discrete Bool ⥤ Type w))

private theorem original_representative_source_tags_distinct
    (a : ((LiftingTest.componentFunctor.{w} (CategoryTheory.Equivalence.refl (C := Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1} ⟨false⟩).obj p).left)
    (b : ((LiftingTest.componentFunctor.{w} (CategoryTheory.Equivalence.refl (C := Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1} ⟨true⟩).obj p).left) :
    (⟨⟨false⟩, a⟩ : LiftingTest.CollectionLeft
      (LiftingTest.componentFunctor.{w} (CategoryTheory.Equivalence.refl (C := Discrete Bool))
        TaggedLiftingTest.pointFamily.{w, w + 1}) p) ≠ ⟨⟨true⟩, b⟩ := by
  intro h
  have htag := congrArg (fun z => z.1.as) h
  exact Bool.false_ne_true htag

private theorem original_representative_target_tags_distinct
    (a : ((LiftingTest.componentFunctor.{w} (CategoryTheory.Equivalence.refl (C := Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1} ⟨false⟩).obj p).right)
    (b : ((LiftingTest.componentFunctor.{w} (CategoryTheory.Equivalence.refl (C := Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1} ⟨true⟩).obj p).right) :
    (⟨⟨false⟩, a⟩ : LiftingTest.CollectionRight
      (LiftingTest.componentFunctor.{w} (CategoryTheory.Equivalence.refl (C := Discrete Bool))
        TaggedLiftingTest.pointFamily.{w, w + 1}) p) ≠ ⟨⟨true⟩, b⟩ := by
  intro h
  have htag := congrArg (fun z => z.1.as) h
  exact Bool.false_ne_true htag

private theorem normalized_representative_source_tags_distinct
    (a : ((LiftingTest.componentFunctor.{w} (CategoryTheory.Equivalence.refl (C := Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1} ⟨false⟩).obj p).left)
    (b : ((LiftingTest.componentFunctor.{w} (CategoryTheory.Equivalence.refl (C := Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1} ⟨true⟩).obj p).left) :
    equivShrink ((LiftingTest.diagramCollection.{w} (CategoryTheory.Equivalence.refl (C :=
      Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1}).obj p).left ⟨⟨false⟩, a⟩ ≠
    equivShrink ((LiftingTest.diagramCollection.{w} (CategoryTheory.Equivalence.refl (C :=
      Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1}).obj p).left ⟨⟨true⟩, b⟩ := by
  intro h
  exact original_representative_source_tags_distinct p a b
    ((equivShrink _).injective h)

private theorem normalized_representative_target_tags_distinct
    (a : ((LiftingTest.componentFunctor.{w} (CategoryTheory.Equivalence.refl (C := Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1} ⟨false⟩).obj p).right)
    (b : ((LiftingTest.componentFunctor.{w} (CategoryTheory.Equivalence.refl (C := Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1} ⟨true⟩).obj p).right) :
    equivShrink ((LiftingTest.diagramCollection.{w} (CategoryTheory.Equivalence.refl (C :=
      Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1}).obj p).right ⟨⟨false⟩, a⟩ ≠
    equivShrink ((LiftingTest.diagramCollection.{w} (CategoryTheory.Equivalence.refl (C :=
      Discrete Bool))
      TaggedLiftingTest.pointFamily.{w, w + 1}).obj p).right ⟨⟨true⟩, b⟩ := by
  intro h
  exact original_representative_target_tags_distinct p a b
    ((equivShrink _).injective h)

end DistinctRepresentativeTags
end MathlibExtTest.DiagramTaggedLiftingTest
