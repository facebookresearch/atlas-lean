/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.TopCat.Suspension
public import MathlibExt.Topology.Homeomorph.Set

/-!
# Cone and suspension height-cover comparison

This module documents the functorial comparison between the cone and suspension
height covers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u
universe w

namespace TopCat

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem suspensionReflection_mem_suspensionLower_iff
    (X : TopCat.{u}) (z : (suspensionFunctor.obj X).right) :
    suspensionReflection X z ∈ suspensionLowerSet X ↔
      z ∈ suspensionUpperSet X := by
  have h := ConcreteCategory.congr_hom (suspensionReflection_mappingConeHeight X) z
  change mappingConeHeight (terminalArrowFunctor.obj X) (suspensionReflection X z) =
    TopCat.I.symm (mappingConeHeight (terminalArrowFunctor.obj X) z) at h
  change ((TopCat.I.homeomorph
      (mappingConeHeight (terminalArrowFunctor.obj X) (suspensionReflection X z)) :
        unitInterval) : ℝ) < 2 / 3 ↔
    (1 : ℝ) / 3 < ((TopCat.I.homeomorph
      (mappingConeHeight (terminalArrowFunctor.obj X) z) : unitInterval) : ℝ)
  rw [h, TopCat.I.homeomorph_symm, unitInterval.coe_symm_eq]
  constructor <;> intro hz <;> linarith

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem suspensionReflection_mem_suspensionUpper_iff
    (X : TopCat.{u}) (z : (suspensionFunctor.obj X).right) :
    suspensionReflection X z ∈ suspensionUpperSet X ↔
      z ∈ suspensionLowerSet X := by
  have h := ConcreteCategory.congr_hom (suspensionReflection_mappingConeHeight X) z
  change mappingConeHeight (terminalArrowFunctor.obj X) (suspensionReflection X z) =
    TopCat.I.symm (mappingConeHeight (terminalArrowFunctor.obj X) z) at h
  change (1 : ℝ) / 3 < ((TopCat.I.homeomorph
      (mappingConeHeight (terminalArrowFunctor.obj X) (suspensionReflection X z)) :
        unitInterval) : ℝ) ↔
    ((TopCat.I.homeomorph
      (mappingConeHeight (terminalArrowFunctor.obj X) z) : unitInterval) : ℝ) < 2 / 3
  rw [h, TopCat.I.homeomorph_symm, unitInterval.coe_symm_eq]
  constructor <;> intro hz <;> linarith

noncomputable def suspensionUpperToLowerHomeomorph (X : TopCat.{u}) :
    suspensionUpperSet X ≃ₜ suspensionLowerSet X where
  toFun z := ⟨suspensionReflection X z.1, by
    rw [suspensionReflection_mem_suspensionLower_iff]
    exact z.2⟩
  invFun z := ⟨suspensionReflection X z.1, by
    rw [suspensionReflection_mem_suspensionUpper_iff]
    exact z.2⟩
  left_inv z := by
    apply Subtype.ext
    change suspensionReflection X (suspensionReflection X z.1) = z.1
    exact suspensionReflection_involutive X z.1
  right_inv z := by
    apply Subtype.ext
    change suspensionReflection X (suspensionReflection X z.1) = z.1
    exact suspensionReflection_involutive X z.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (suspensionReflection X).hom.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (suspensionReflection X).hom.continuous.comp continuous_subtype_val

@[simp]
theorem suspensionUpperToLowerHomeomorph_apply
    (X : TopCat.{u}) (z : suspensionUpperSet X) :
    (suspensionUpperToLowerHomeomorph X z).1 = suspensionReflection X z.1 :=
  rfl

@[simp]
theorem suspensionUpperToLowerHomeomorph_symm_apply
    (X : TopCat.{u}) (z : suspensionLowerSet X) :
    ((suspensionUpperToLowerHomeomorph X).symm z).1 = suspensionReflection X z.1 :=
  rfl

noncomputable def coneUpperToSuspensionLowerHomeomorph (X : TopCat.{u}) :
    coneUpperSet X ≃ₜ suspensionLowerSet X :=
  (coneUpperToSuspensionUpperHomeomorph X).trans (suspensionUpperToLowerHomeomorph X)

@[simp]
theorem coneUpperToSuspensionLowerHomeomorph_apply
    (X : TopCat.{u}) (z : coneUpperSet X) :
    (coneUpperToSuspensionLowerHomeomorph X z).1 = coneToSuspension X z.1 := by
  change (suspensionUpperToLowerHomeomorph X
      (coneUpperToSuspensionUpperHomeomorph X z)).1 = _
  rw [suspensionUpperToLowerHomeomorph_apply, coneUpperToSuspensionUpperHomeomorph_apply]
  have h := ConcreteCategory.congr_hom (mappingConeInr_suspensionReflection X) z.1
  change suspensionReflection X (pushout.inr (isTerminalPUnit.from X) (coneBase X) z.1) =
    coneToSuspension X z.1 at h
  exact h

noncomputable def coneHeightInterToSuspensionHeightInterHomeomorph
    (X : TopCat.{u}) :
    (coneLowerSet X ∩ coneUpperSet X : Set (cone X)) ≃ₜ
      (suspensionUpperSet X ∩ suspensionLowerSet X :
        Set ((suspensionFunctor.obj X).right)) :=
  Homeomorph.inter (coneUpperToSuspensionLowerHomeomorph X)
    (fun z => by
      rw [coneUpperToSuspensionLowerHomeomorph_apply]
      exact (coneToSuspension_mem_suspensionUpper_iff X z.1).symm)

@[simp]
theorem coneHeightInterToSuspensionHeightInterHomeomorph_apply
    (X : TopCat.{u})
    (z : (coneLowerSet X ∩ coneUpperSet X : Set (cone X))) :
    (coneHeightInterToSuspensionHeightInterHomeomorph X z : (suspensionFunctor.obj X).right) =
      coneToSuspension X z.1 := by
  have h_eq : coneHeightInterToSuspensionHeightInterHomeomorph X =
      Homeomorph.inter (coneUpperToSuspensionLowerHomeomorph X)
        (fun z => by
          rw [coneUpperToSuspensionLowerHomeomorph_apply]
          exact (coneToSuspension_mem_suspensionUpper_iff X z.1).symm) := rfl
  rw [h_eq, Homeomorph.inter_apply_coe, coneUpperToSuspensionLowerHomeomorph_apply]

end TopCat

namespace TopPair

open AlgebraicTopology AlgebraicTopology.OrderedTwoSetCover

noncomputable def coneToSuspensionHeightCoverRightInterPairIso
    (X : TopCat.{u}) :
    rightInterPairFunctor.obj (TopCat.coneHeightCoverFunctor.obj X) ≅
      rightInterPairFunctor.obj (TopCat.suspensionHeightCoverFunctor.obj X) :=
  CategoryTheory.MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo (TopCat.coneHeightInterToSuspensionHeightInterHomeomorph X))
    (TopCat.isoOfHomeo (TopCat.coneUpperToSuspensionLowerHomeomorph X)) (by
      apply TopCat.hom_ext
      ext z
      apply Subtype.ext
      change (TopCat.coneHeightInterToSuspensionHeightInterHomeomorph X ⟨z.1, z.2⟩).1 =
        (TopCat.coneUpperToSuspensionLowerHomeomorph X ⟨z.1, z.2.2⟩).1
      rw [TopCat.coneHeightInterToSuspensionHeightInterHomeomorph_apply,
        TopCat.coneUpperToSuspensionLowerHomeomorph_apply])

@[simp]
theorem coneToSuspensionHeightCoverRightInterPairIso_hom
    (X : TopCat.{u}) :
    (TopPair.coneToSuspensionHeightCoverRightInterPairIso X).hom =
      rightInterPairFunctor.map
        (TopCat.coneToSuspensionHeightCoverNatTrans.app X) := by
  apply CategoryTheory.MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    ext ⟨x, hx⟩
    apply Subtype.ext
    have h1 : (TopCat.coneHeightInterToSuspensionHeightInterHomeomorph X ⟨x, hx⟩).1 =
        TopCat.coneToSuspension X x :=
      TopCat.coneHeightInterToSuspensionHeightInterHomeomorph_apply X ⟨x, hx⟩
    exact h1
  · apply TopCat.hom_ext
    ext ⟨x, hx⟩
    apply Subtype.ext
    have h1 : (TopCat.coneUpperToSuspensionLowerHomeomorph X ⟨x, hx⟩).1 =
        TopCat.coneToSuspension X x :=
      TopCat.coneUpperToSuspensionLowerHomeomorph_apply X ⟨x, hx⟩
    exact h1

noncomputable instance isIso_coneToSuspensionHeightCoverRightInterPairMap
    (X : TopCat.{u}) :
    IsIso (rightInterPairFunctor.map
      (TopCat.coneToSuspensionHeightCoverNatTrans.app X)) := by
  rw [← TopPair.coneToSuspensionHeightCoverRightInterPairIso_hom X]
  infer_instance

noncomputable def coneToSuspensionHeightCoverRightInterPairNatIso :
    TopCat.coneHeightCoverFunctor ⋙ rightInterPairFunctor ≅
      TopCat.suspensionHeightCoverFunctor ⋙ rightInterPairFunctor :=
  NatIso.ofComponents
    (fun X => TopPair.coneToSuspensionHeightCoverRightInterPairIso X)
    (fun {X Y} f => by
      rw [TopPair.coneToSuspensionHeightCoverRightInterPairIso_hom,
        TopPair.coneToSuspensionHeightCoverRightInterPairIso_hom]
      exact (Functor.whiskerRight TopCat.coneToSuspensionHeightCoverNatTrans
        rightInterPairFunctor).naturality f)

@[simp]
theorem coneToSuspensionHeightCoverRightInterPairNatIso_hom_app
    (X : TopCat.{u}) :
    (TopPair.coneToSuspensionHeightCoverRightInterPairNatIso.hom.app X) =
      rightInterPairFunctor.map
        (TopCat.coneToSuspensionHeightCoverNatTrans.app X) :=
  TopPair.coneToSuspensionHeightCoverRightInterPairIso_hom X

theorem conePairToSuspensionPair_heightCover (X : PointedTopCat.{w}) :
    conePairToHeightCoverNatTrans.app X ≫
        spaceLeftPairFunctor.map
          (TopCat.coneToSuspensionHeightCoverNatTrans.app X.right) =
      conePairToSuspensionPairNatTrans.app X ≫
        suspensionPairToHeightCoverNatTrans.app X := by
  apply CategoryTheory.MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (TopCat.coneBase_coneToSuspension X.right) x
  · apply TopCat.hom_ext
    ext x
    rfl

end TopPair
