/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHomotopyCategory
import MathlibExt.Topology.Category.PointedCGWH.Smash
import MathlibExt.Topology.Homotopy.WeaklyPointedHomotopyRel
import MathlibExt.Topology.Category.TopCat.ProdPushout
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Pointed CGWH homotopies and the homotopy category

A continuous homotopy of pointed maps which is stationary on the selected
source point descends to a native reduced smash cylinder.  Its projection is
an explicit deformation retraction, so the resulting categorical left
homotopy identifies the two maps in the canonical homotopy category.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open HomotopicalAlgebra MorphismProperty Topology
open scoped CGWH.modelCategory

namespace PointedCGWH

/-- The native CGWH interval, with its carrier lifted to the ambient carrier
universe. -/
private noncomputable def cgwhInterval : CGWH.{u, v} :=
  CGWH.of (ULift.{v} unitInterval)

/-- Inclusion of a native product with the interval into the selected
categorical product of the included spaces. -/
private noncomputable def intervalProdComparisonIso (A : CGWH.{u, v}) :
    CGWH.cgwhToTop.obj (cgwhInterval.{u, v} ⨯ A) ≅
      (CGWH.cgwhToTop.obj cgwhInterval.{u, v} ⨯
        CGWH.cgwhToTop.obj A) := by
  let _ : LocallyCompactSpace cgwhInterval.{u, v} := by
    change LocallyCompactSpace (ULift.{v} unitInterval)
    infer_instance
  let _ : T2Space cgwhInterval.{u, v} := by
    change T2Space (ULift.{v} unitInterval)
    infer_instance
  let _ : IsIso (CGWH.prodComparisonToTop cgwhInterval.{u, v} A) :=
    (TopCat.isIso_iff_isHomeomorph _).2
      (CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_left
        cgwhInterval.{u, v} A)
  exact asIso (CGWH.prodComparisonToTop cgwhInterval.{u, v} A) ≪≫
    (TopCat.prodIsoProd (CGWH.cgwhToTop.obj cgwhInterval.{u, v})
      (CGWH.cgwhToTop.obj A)).symm

/-- Inverse product comparisons commute with maps in the second factor. -/
private theorem intervalProdComparisonIso_naturality
    {A B : CGWH.{u, v}} (a : A ⟶ B) :
    Limits.prod.map (𝟙 (CGWH.cgwhToTop.obj cgwhInterval.{u, v}))
          (CGWH.cgwhToTop.map a) ≫
        (intervalProdComparisonIso B).inv =
      (intervalProdComparisonIso A).inv ≫
        CGWH.cgwhToTop.map
          (Limits.prod.map (𝟙 cgwhInterval.{u, v}) a) := by
  have qHom (Z : CGWH.{u, v}) :
      (intervalProdComparisonIso Z).hom =
        Limits.prodComparison CGWH.cgwhToTop.{u, v}
          cgwhInterval.{u, v} Z := by
    unfold intervalProdComparisonIso CGWH.prodComparisonToTop
    simp
  have hForward :
      CGWH.cgwhToTop.map
          (Limits.prod.map (𝟙 cgwhInterval.{u, v}) a) ≫
          (intervalProdComparisonIso B).hom =
        (intervalProdComparisonIso A).hom ≫
          Limits.prod.map
            (𝟙 (CGWH.cgwhToTop.obj cgwhInterval.{u, v}))
            (CGWH.cgwhToTop.map a) := by
    rw [qHom, qHom]
    rw [← CGWH.cgwhToTop.map_id]
    exact Limits.prodComparison_natural
      (F := CGWH.cgwhToTop.{u, v})
      (𝟙 cgwhInterval.{u, v}) a
  apply (cancel_mono (intervalProdComparisonIso B).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    Limits.prod.map
          (𝟙 (CGWH.cgwhToTop.obj cgwhInterval.{u, v}))
          (CGWH.cgwhToTop.map a) =
        𝟙 _ ≫ Limits.prod.map
          (𝟙 (CGWH.cgwhToTop.obj cgwhInterval.{u, v}))
          (CGWH.cgwhToTop.map a) := (Category.id_comp _).symm
    _ = ((intervalProdComparisonIso A).inv ≫
          (intervalProdComparisonIso A).hom) ≫
        Limits.prod.map
          (𝟙 (CGWH.cgwhToTop.obj cgwhInterval.{u, v}))
          (CGWH.cgwhToTop.map a) := by rw [Iso.inv_hom_id]
    _ = (intervalProdComparisonIso A).inv ≫
        ((intervalProdComparisonIso A).hom ≫
          Limits.prod.map
            (𝟙 (CGWH.cgwhToTop.obj cgwhInterval.{u, v}))
            (CGWH.cgwhToTop.map a)) := Category.assoc _ _ _
    _ = (intervalProdComparisonIso A).inv ≫
        (CGWH.cgwhToTop.map
            (Limits.prod.map (𝟙 cgwhInterval.{u, v}) a) ≫
          (intervalProdComparisonIso B).hom) := by rw [hForward]
    _ = ((intervalProdComparisonIso A).inv ≫
          CGWH.cgwhToTop.map
            (Limits.prod.map (𝟙 cgwhInterval.{u, v}) a)) ≫
        (intervalProdComparisonIso B).hom :=
      (Category.assoc _ _ _).symm

/-- The freely pointed native interval. -/
private noncomputable abbrev freePointedInterval : PointedCGWH.{u, v} :=
  Under.mk (coprod.inl : CGWH.point.{u, v} ⟶
    CGWH.point.{u, v} ⨿ cgwhInterval.{u, v})

/-- The zero endpoint of the native interval. -/
private def intervalEndpointZero :
    CGWH.point.{u, v} ⟶ cgwhInterval.{u, v} :=
  ConcreteCategory.ofHom
    (ContinuousMap.const _ (ULift.up (0 : unitInterval)))

/-- The one endpoint of the native interval. -/
private def intervalEndpointOne :
    CGWH.point.{u, v} ⟶ cgwhInterval.{u, v} :=
  ConcreteCategory.ofHom
    (ContinuousMap.const _ (ULift.up (1 : unitInterval)))

/-- A fixed interval endpoint into a selected categorical product in
`TopCat`. -/
private noncomputable def rawIntervalEndpoint
    (e : CGWH.point.{u, v} ⟶ cgwhInterval.{u, v}) (Z : TopCat.{v}) :
    Z ⟶ CGWH.cgwhToTop.obj cgwhInterval.{u, v} ⨯ Z :=
  Limits.prod.lift
    (TopCat.isTerminalPUnit.from Z ≫ CGWH.cgwhToTop.map e) (𝟙 Z)

/-- The raw endpoint agrees with the included native endpoint through the
chosen-product comparison. -/
private theorem rawIntervalEndpoint_comparison
    (e : CGWH.point.{u, v} ⟶ cgwhInterval.{u, v})
    (Z : CGWH.{u, v}) :
    rawIntervalEndpoint e (CGWH.cgwhToTop.obj Z) ≫
        (intervalProdComparisonIso Z).inv =
      CGWH.cgwhToTop.map
        (Limits.prod.lift
          (CGWH.point_isTerminal.from Z ≫ e) (𝟙 Z)) := by
  let I := cgwhInterval.{u, v}
  let T := CGWH.cgwhToTop.{u, v}
  let nativeEndpoint : Z ⟶ I ⨯ Z :=
    Limits.prod.lift (CGWH.point_isTerminal.from Z ≫ e) (𝟙 Z)
  have qHom : (intervalProdComparisonIso Z).hom =
      Limits.prodComparison T I Z := by
    unfold intervalProdComparisonIso CGWH.prodComparisonToTop
    simp
    rfl
  have qF : (intervalProdComparisonIso Z).hom ≫ Limits.prod.fst =
      T.map (Limits.prod.fst : I ⨯ Z ⟶ I) := by
    rw [qHom, Limits.prodComparison_fst]
  have qS : (intervalProdComparisonIso Z).hom ≫ Limits.prod.snd =
      T.map (Limits.prod.snd : I ⨯ Z ⟶ Z) := by
    rw [qHom, Limits.prodComparison_snd]
  change rawIntervalEndpoint e (T.obj Z) ≫
      (intervalProdComparisonIso Z).inv = T.map nativeEndpoint
  apply (cancel_mono (intervalProdComparisonIso Z).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply Limits.prod.hom_ext
  · calc
      rawIntervalEndpoint e (T.obj Z) ≫ Limits.prod.fst =
          TopCat.isTerminalPUnit.from (T.obj Z) ≫ T.map e :=
        Limits.prod.lift_fst _ _
      _ = T.map (CGWH.point_isTerminal.from Z) ≫ T.map e := by
        exact congrArg (fun k => k ≫ T.map e)
          (TopCat.isTerminalPUnit.hom_ext
            (TopCat.isTerminalPUnit.from (T.obj Z))
            (T.map (CGWH.point_isTerminal.from Z)))
      _ = T.map (CGWH.point_isTerminal.from Z ≫ e) :=
        (T.map_comp _ _).symm
      _ = T.map nativeEndpoint ≫ T.map
          (Limits.prod.fst : I ⨯ Z ⟶ I) := by
        rw [← T.map_comp, Limits.prod.lift_fst]
      _ = T.map nativeEndpoint ≫
          (intervalProdComparisonIso Z).hom ≫ Limits.prod.fst := by
        rw [qF]
  · calc
      rawIntervalEndpoint e (T.obj Z) ≫ Limits.prod.snd = 𝟙 _ :=
        Limits.prod.lift_snd _ _
      _ = T.map (𝟙 Z) := (T.map_id Z).symm
      _ = T.map nativeEndpoint ≫ T.map
          (Limits.prod.snd : I ⨯ Z ⟶ Z) := by
        rw [← T.map_comp, Limits.prod.lift_snd]
      _ = T.map nativeEndpoint ≫
          (intervalProdComparisonIso Z).hom ≫ Limits.prod.snd := by
        rw [qS]

/-- Raw interval endpoints are natural in their second factor. -/
private theorem rawIntervalEndpoint_naturality
    (e : CGWH.point.{u, v} ⟶ cgwhInterval.{u, v})
    {Z Z' : TopCat.{v}} (a : Z ⟶ Z') :
    a ≫ rawIntervalEndpoint e Z' =
      rawIntervalEndpoint e Z ≫ Limits.prod.map
        (𝟙 (CGWH.cgwhToTop.obj cgwhInterval.{u, v})) a := by
  apply Limits.prod.hom_ext
  · dsimp only [rawIntervalEndpoint]
    simp only [Category.assoc, Limits.prod.lift_fst,
      Limits.prod.map_fst, Category.comp_id]
    exact congrArg (fun k => k ≫ CGWH.cgwhToTop.map e)
      (TopCat.isTerminalPUnit.hom_ext
        (a ≫ TopCat.isTerminalPUnit.from Z')
        (TopCat.isTerminalPUnit.from Z))
  · dsimp only [rawIntervalEndpoint]
    simp

/-- The reduced smash cylinder object. -/
private noncomputable def pointedCylinderObj
    (X : PointedCGWH.{u, v}) : PointedCGWH.{u, v} :=
  (PointedCGWH.smash.obj freePointedInterval.{u, v}).obj X

/-- Inclusion of a fixed interval endpoint into the reduced smash cylinder. -/
private noncomputable def pointedCylinderEndpoint
    (e : CGWH.point.{u, v} ⟶ cgwhInterval.{u, v})
    (X : PointedCGWH.{u, v}) : X ⟶ pointedCylinderObj X := by
  let I := cgwhInterval.{u, v}
  let J := freePointedInterval.{u, v}
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal J X
  let z : CGWH.point.{u, v} ⟶ J.right := e ≫ coprod.inr
  let endpoint : X.right ⟶ J.right ⊗ X.right :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from X.right ≫ z) (𝟙 X.right)
  let leftFace : J.right ⟶ J.right ⊗ X.right :=
    CartesianMonoidalCategory.lift (𝟙 J.right)
      (CGWH.point_isTerminal.from J.right ≫ X.hom)
  let wRaw : pushout J.hom X.hom ⟶ J.right ⊗ X.right := p.1.right
  have hpInl : pushout.inl J.hom X.hom ≫ wRaw = leftFace := by
    change pushout.inl J.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inl_desc]
    rfl
  have hPoint : X.hom ≫ endpoint = z ≫ leftFace := by
    dsimp only [endpoint, leftFace, z, J, freePointedInterval]
    cat_disch
  let m : X.right ⟶ (pointedCylinderObj X).right :=
    endpoint ≫ p.2.1.inl
  refine Under.homMk m ?_
  have hCondition : wRaw ≫ p.2.1.inl =
      CGWH.point_isTerminal.from (pushout J.hom X.hom) ≫ p.2.1.inr := by
    change p.1.right ≫ p.2.1.inl =
      CGWH.point_isTerminal.from
          (((CategoryTheory.Pointed.wedge CGWH.point).obj J).obj X).right ≫
        p.2.1.inr
    exact p.2.1.condition
  change X.hom ≫ endpoint ≫ p.2.1.inl = p.2.1.inr
  rw [← Category.assoc, hPoint, Category.assoc]
  rw [← hpInl, Category.assoc, Category.assoc, hCondition]
  rw [← Category.assoc]
  have ht : z ≫ pushout.inl J.hom X.hom ≫
      CGWH.point_isTerminal.from (pushout J.hom X.hom) = 𝟙 _ :=
    CGWH.point_isTerminal.hom_ext _ _
  dsimp only [z] at ht
  simpa only [Category.assoc, Category.id_comp] using congrArg
    (fun k : CGWH.point.{u, v} ⟶ CGWH.point ↦ k ≫ p.2.1.inr) ht

/-- The zero endpoint inclusion into the reduced smash cylinder. -/
private noncomputable def pointedCylinderI0
    (X : PointedCGWH.{u, v}) : X ⟶ pointedCylinderObj X :=
  pointedCylinderEndpoint intervalEndpointZero X

/-- The one endpoint inclusion into the reduced smash cylinder. -/
private noncomputable def pointedCylinderI1
    (X : PointedCGWH.{u, v}) : X ⟶ pointedCylinderObj X :=
  pointedCylinderEndpoint intervalEndpointOne X

/-- Projection of the reduced smash cylinder to its source. -/
private noncomputable def pointedCylinderProjection
    (X : PointedCGWH.{u, v}) :
    { pi : pointedCylinderObj X ⟶ X //
      pointedCylinderI0 X ≫ pi = 𝟙 X ∧
        pointedCylinderI1 X ≫ pi = 𝟙 X } := by
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  letI : IsMonoidalDistrib CGWH.{u, v} := inferInstance
  let I := cgwhInterval.{u, v}
  let J := freePointedInterval.{u, v}
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal J X
  let baseBranch : CGWH.point.{u, v} ⊗ X.right ⟶ X.right :=
    CGWH.point_isTerminal.from _ ≫ X.hom
  let intervalBranch : I ⊗ X.right ⟶ X.right :=
    CartesianMonoidalCategory.snd I X.right
  let projProd : J.right ⊗ X.right ⟶ X.right :=
    (rightDistrib X.right CGWH.point I).inv ≫
      coprod.desc baseBranch intervalBranch
  let leftFace : J.right ⟶ J.right ⊗ X.right :=
    CartesianMonoidalCategory.lift (𝟙 J.right)
      (CGWH.point_isTerminal.from J.right ≫ X.hom)
  let rightFace : X.right ⟶ J.right ⊗ X.right :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from X.right ≫ J.hom) (𝟙 X.right)
  let wRaw : pushout J.hom X.hom ⟶ J.right ⊗ X.right := p.1.right
  have hpInl : pushout.inl J.hom X.hom ≫ wRaw = leftFace := by
    change pushout.inl J.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inl_desc]
    rfl
  have hpInr : pushout.inr J.hom X.hom ≫ wRaw = rightFace := by
    change pushout.inr J.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inr_desc]
    rfl
  have hLeft : leftFace ≫ projProd =
      CGWH.point_isTerminal.from J.right ≫ X.hom := by
    apply coprod.hom_ext
    · let insert : CGWH.point.{u, v} ⟶ CGWH.point ⊗ X.right :=
        CartesianMonoidalCategory.lift (𝟙 _) X.hom
      have hFactor : coprod.inl ≫ leftFace =
          insert ≫ (coprod.inl ▷ X.right) := by
        dsimp only [leftFace, insert]
        rw [CartesianMonoidalCategory.comp_lift,
          CartesianMonoidalCategory.lift_whiskerRight]
        congr 1
      rw [← Category.assoc, hFactor, Category.assoc]
      dsimp only [projProd]
      rw [CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv_assoc,
        CategoryTheory.Limits.coprod.inl_desc]
      dsimp only [baseBranch]
      simpa only [Category.assoc] using congrArg
        (fun k : CGWH.point.{u, v} ⟶ CGWH.point ↦ k ≫ X.hom)
        (CGWH.point_isTerminal.hom_ext
          (insert ≫ CGWH.point_isTerminal.from
            (CGWH.point.{u, v} ⊗ X.right))
          (coprod.inl ≫ CGWH.point_isTerminal.from J.right))
    · let insert : I ⟶ I ⊗ X.right :=
        CartesianMonoidalCategory.lift (𝟙 I)
          (CGWH.point_isTerminal.from I ≫ X.hom)
      have hFactor : coprod.inr ≫ leftFace =
          insert ≫ (coprod.inr ▷ X.right) := by
        dsimp only [leftFace, insert]
        rw [CartesianMonoidalCategory.comp_lift,
          CartesianMonoidalCategory.lift_whiskerRight]
        congr 1
      rw [← Category.assoc, hFactor, Category.assoc]
      dsimp only [projProd]
      rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc,
        CategoryTheory.Limits.coprod.inr_desc]
      dsimp only [insert, intervalBranch]
      rw [CartesianMonoidalCategory.lift_snd]
      rw [← Category.assoc]
      congr 1
  have hRight : rightFace ≫ projProd =
      CGWH.point_isTerminal.from X.right ≫ X.hom := by
    let insert : X.right ⟶ CGWH.point.{u, v} ⊗ X.right :=
      CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from X.right) (𝟙 X.right)
    have hFactor : rightFace = insert ≫ (coprod.inl ▷ X.right) := by
      dsimp only [rightFace, insert, J, freePointedInterval]
      cat_disch
    rw [hFactor]
    dsimp only [projProd]
    calc
      (insert ≫ (coprod.inl ▷ X.right)) ≫
            (rightDistrib X.right CGWH.point I).inv ≫
              coprod.desc baseBranch intervalBranch =
          insert ≫ ((coprod.inl ▷ X.right) ≫
            (rightDistrib X.right CGWH.point I).inv ≫
              coprod.desc baseBranch intervalBranch) := by
                simp only [Category.assoc]
      _ = insert ≫ (coprod.inl ≫
          coprod.desc baseBranch intervalBranch) := by
        rw [CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv_assoc]
      _ = insert ≫ baseBranch := by rw [CategoryTheory.Limits.coprod.inl_desc]
      _ = CGWH.point_isTerminal.from X.right ≫ X.hom := by
        dsimp only [insert, baseBranch]
        rw [← Category.assoc]
        congr 1
  have hCompat : wRaw ≫ projProd =
      CGWH.point_isTerminal.from (pushout J.hom X.hom) ≫ X.hom := by
    apply pushout.hom_ext
    · rw [← Category.assoc, hpInl, hLeft]
      simpa only [Category.assoc] using congrArg
        (fun k : J.right ⟶ CGWH.point ↦ k ≫ X.hom)
        (CGWH.point_isTerminal.hom_ext
          (CGWH.point_isTerminal.from J.right)
          (pushout.inl J.hom X.hom ≫
            CGWH.point_isTerminal.from (pushout J.hom X.hom)))
    · rw [← Category.assoc, hpInr, hRight]
      simpa only [Category.assoc] using congrArg
        (fun k : X.right ⟶ CGWH.point ↦ k ≫ X.hom)
        (CGWH.point_isTerminal.hom_ext
          (CGWH.point_isTerminal.from X.right)
          (pushout.inr J.hom X.hom ≫
            CGWH.point_isTerminal.from (pushout J.hom X.hom)))
  have hCompatP : p.1.right ≫ projProd =
      CGWH.point_isTerminal.from
          (((CategoryTheory.Pointed.wedge CGWH.point).obj J).obj X).right ≫
        X.hom := by
    change wRaw ≫ projProd =
      CGWH.point_isTerminal.from (pushout J.hom X.hom) ≫ X.hom
    exact hCompat
  let pi : pointedCylinderObj X ⟶ X := Under.homMk
    (PushoutCocone.IsColimit.desc p.2.2 projProd X.hom hCompatP)
    (PushoutCocone.IsColimit.inr_desc p.2.2 _ _ _)
  let z (e : CGWH.point.{u, v} ⟶ I) : CGWH.point.{u, v} ⟶ J.right :=
    e ≫ coprod.inr
  let endpoint (e : CGWH.point.{u, v} ⟶ I) :
      X.right ⟶ J.right ⊗ X.right :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from X.right ≫ z e) (𝟙 X.right)
  have hEndpointProj (e : CGWH.point.{u, v} ⟶ I) :
      endpoint e ≫ projProd = 𝟙 X.right := by
    let insert : X.right ⟶ I ⊗ X.right :=
      CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from X.right ≫ e) (𝟙 X.right)
    have hFactor : endpoint e = insert ≫ (coprod.inr ▷ X.right) := by
      dsimp only [endpoint, insert, z, J, freePointedInterval]
      cat_disch
    rw [hFactor]
    dsimp only [projProd]
    calc
      (insert ≫ (coprod.inr ▷ X.right)) ≫
            (rightDistrib X.right CGWH.point I).inv ≫
              coprod.desc baseBranch intervalBranch =
          insert ≫ ((coprod.inr ▷ X.right) ≫
            (rightDistrib X.right CGWH.point I).inv ≫
              coprod.desc baseBranch intervalBranch) := by
                simp only [Category.assoc]
      _ = insert ≫ (coprod.inr ≫
          coprod.desc baseBranch intervalBranch) := by
        rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc]
      _ = insert ≫ intervalBranch := by
        rw [CategoryTheory.Limits.coprod.inr_desc]
      _ = 𝟙 X.right := by
        dsimp only [insert, intervalBranch]
        rw [CartesianMonoidalCategory.lift_snd]
  have hSection (e : CGWH.point.{u, v} ⟶ I) :
      pointedCylinderEndpoint e X ≫ pi = 𝟙 X := by
    apply Under.UnderMorphism.ext
    change (endpoint e ≫ p.2.1.inl) ≫
        PushoutCocone.IsColimit.desc p.2.2 projProd X.hom hCompatP =
      𝟙 X.right
    rw [Category.assoc, PushoutCocone.IsColimit.inl_desc]
    exact hEndpointProj e
  refine ⟨pi, ?_, ?_⟩
  · exact hSection intervalEndpointZero
  · exact hSection intervalEndpointOne

/-- The interval branch of a relative homotopy, imported from the explicit
product to the native CGWH product. -/
private noncomputable def liftedHomotopyIntervalBranch
    {X Y : PointedCGWH.{u, v}} (f g : X ⟶ Y)
    (H : ContinuousMap.HomotopyRel
      (ConcreteCategory.hom f.right : C(X.right, Y.right))
      (ConcreteCategory.hom g.right : C(X.right, Y.right))
      (Set.range (ConcreteCategory.hom X.hom :
        C(CGWH.point.{u, v}, X.right)))) :
    cgwhInterval.{u, v} ⊗ X.right ⟶ Y.right := by
  let eTensor : cgwhInterval.{u, v} ⊗ X.right ≅
      cgwhInterval.{u, v} ⨯ X.right :=
    (CartesianMonoidalCategory.tensorLeftIsoProd
      cgwhInterval.{u, v}).app X.right
  exact CGWH.fullyFaithfulCgwhToTop.preimage
    (CGWH.cgwhToTop.map eTensor.hom ≫
      CGWH.prodComparisonToTop cgwhInterval.{u, v} X.right ≫
        TopCat.ofHom
          { toFun := fun z => H (ULift.down z.1, z.2)
            continuous_toFun := H.continuous.comp
              ((continuous_uliftDown.comp continuous_fst).prodMk
                continuous_snd) })

/-- A relative homotopy descends through the reduced smash cylinder. -/
private noncomputable def homotopyRelCylinderMap
    {X Y : PointedCGWH.{u, v}} (f g : X ⟶ Y)
    (H : ContinuousMap.HomotopyRel
      (ConcreteCategory.hom f.right : C(X.right, Y.right))
      (ConcreteCategory.hom g.right : C(X.right, Y.right))
      (Set.range (ConcreteCategory.hom X.hom :
        C(CGWH.point.{u, v}, X.right)))) :
    { h : pointedCylinderObj X ⟶ Y //
      pointedCylinderI0 X ≫ h = f ∧
        pointedCylinderI1 X ≫ h = g } := by
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  letI : IsMonoidalDistrib CGWH.{u, v} := inferInstance
  let I := cgwhInterval.{u, v}
  let J := freePointedInterval.{u, v}
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal J X
  let hI := liftedHomotopyIntervalBranch f g H
  let constantBranch : CGWH.point.{u, v} ⊗ X.right ⟶ Y.right :=
    CGWH.point_isTerminal.from _ ≫ Y.hom
  let hProd : (CGWH.point.{u, v} ⨿ I) ⊗ X.right ⟶ Y.right :=
    (rightDistrib X.right CGWH.point I).inv ≫
      coprod.desc constantBranch hI
  let leftFace : (CGWH.point.{u, v} ⨿ I) ⟶
      (CGWH.point.{u, v} ⨿ I) ⊗ X.right :=
    CartesianMonoidalCategory.lift (𝟙 (CGWH.point.{u, v} ⨿ I))
      (CGWH.point_isTerminal.from (CGWH.point.{u, v} ⨿ I) ≫ X.hom)
  let rightFace : X.right ⟶
      (CGWH.point.{u, v} ⨿ I) ⊗ X.right :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from X.right ≫
        (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point ⨿ I))
      (𝟙 X.right)
  let wRaw : pushout J.hom X.hom ⟶
      (CGWH.point.{u, v} ⨿ I) ⊗ X.right := p.1.right
  have hpInl : pushout.inl J.hom X.hom ≫ wRaw = leftFace := by
    change pushout.inl J.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inl_desc]
    rfl
  have hpInr : pushout.inr J.hom X.hom ≫ wRaw = rightFace := by
    change pushout.inr J.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inr_desc]
    rfl
  have hInterval :
      CartesianMonoidalCategory.lift (𝟙 I)
          (CGWH.point_isTerminal.from I ≫ X.hom) ≫ hI =
        CGWH.point_isTerminal.from I ≫ Y.hom := by
    apply ConcreteCategory.hom_ext
    intro t
    let insert : I ⟶ I ⊗ X.right :=
      CartesianMonoidalCategory.lift (𝟙 I)
        (CGWH.point_isTerminal.from I ≫ X.hom)
    let eTensor : I ⊗ X.right ≅ I ⨯ X.right :=
      (CartesianMonoidalCategory.tensorLeftIsoProd I).app X.right
    let RawPair : TopCat.{v} := TopCat.of
      (↑(CGWH.cgwhToTop.obj I) × ↑(CGWH.cgwhToTop.obj X.right))
    let tensorToRaw : CGWH.cgwhToTop.obj (I ⊗ X.right) ⟶ RawPair :=
      CGWH.cgwhToTop.map eTensor.hom ≫
        CGWH.prodComparisonToTop I X.right
    have eTensor_fst : eTensor.hom ≫
        (Limits.prod.fst : I ⨯ X.right ⟶ I) =
      CartesianMonoidalCategory.fst I X.right :=
      IsLimit.conePointUniqueUpToIso_hom_comp
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct I X.right)
        (limit.isLimit _) ⟨WalkingPair.left⟩
    have eTensor_snd : eTensor.hom ≫
        (Limits.prod.snd : I ⨯ X.right ⟶ X.right) =
      CartesianMonoidalCategory.snd I X.right :=
      IsLimit.conePointUniqueUpToIso_hom_comp
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct I X.right)
        (limit.isLimit _) ⟨WalkingPair.right⟩
    have tensorToRaw_fst : tensorToRaw ≫ TopCat.prodFst =
        CGWH.cgwhToTop.map
          (CartesianMonoidalCategory.fst I X.right) := by
      dsimp only [tensorToRaw]
      rw [Category.assoc, CGWH.prodComparisonToTop_fst,
        ← CGWH.cgwhToTop.map_comp, eTensor_fst]
    have tensorToRaw_snd : tensorToRaw ≫ TopCat.prodSnd =
        CGWH.cgwhToTop.map
          (CartesianMonoidalCategory.snd I X.right) := by
      dsimp only [tensorToRaw]
      rw [Category.assoc, CGWH.prodComparisonToTop_snd,
        ← CGWH.cgwhToTop.map_comp, eTensor_snd]
    have hMap := CGWH.fullyFaithfulCgwhToTop.map_preimage
      (tensorToRaw ≫ TopCat.ofHom
        { toFun := fun z => H (ULift.down z.1, z.2)
          continuous_toFun := H.continuous.comp
            ((continuous_uliftDown.comp continuous_fst).prodMk
              continuous_snd) })
    have ht := ConcreteCategory.congr_hom hMap (insert t)
    have hfst := ConcreteCategory.congr_hom
      tensorToRaw_fst (insert t)
    have hsnd := ConcreteCategory.congr_hom
      tensorToRaw_snd (insert t)
    have hInsertFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst (𝟙 I)
        (CGWH.point_isTerminal.from I ≫ X.hom)) t
    have hInsertSnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd (𝟙 I)
        (CGWH.point_isTerminal.from I ≫ X.hom)) t
    change hI (insert t) = H (ULift.down (tensorToRaw (insert t)).1,
      (tensorToRaw (insert t)).2) at ht
    change (tensorToRaw (insert t)).1 =
      CartesianMonoidalCategory.fst I X.right (insert t) at hfst
    change (tensorToRaw (insert t)).2 =
      CartesianMonoidalCategory.snd I X.right (insert t) at hsnd
    change CartesianMonoidalCategory.fst I X.right (insert t) = t at hInsertFst
    change CartesianMonoidalCategory.snd I X.right (insert t) =
      X.hom (CGWH.point_isTerminal.from I t) at hInsertSnd
    rw [hInsertFst] at hfst
    rw [hInsertSnd] at hsnd
    rw [hfst, hsnd] at ht
    have hFixed := H.eq_fst (ULift.down t)
      ⟨CGWH.point_isTerminal.from I t, rfl⟩
    have hPoint := ConcreteCategory.congr_hom (Under.w f)
      (CGWH.point_isTerminal.from I t)
    exact ht.trans (hFixed.trans hPoint)
  have hI_apply (t : I) (x : X.right) :
      hI (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from X.right ≫
          ConcreteCategory.ofHom (ContinuousMap.const _ t))
        (𝟙 X.right) x) = H (ULift.down t, x) := by
    let endpoint : CGWH.point.{u, v} ⟶ I :=
      ConcreteCategory.ofHom (ContinuousMap.const _ t)
    let insert : X.right ⟶ I ⊗ X.right :=
      CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from X.right ≫ endpoint) (𝟙 X.right)
    let eTensor : I ⊗ X.right ≅ I ⨯ X.right :=
      (CartesianMonoidalCategory.tensorLeftIsoProd I).app X.right
    let RawPair : TopCat.{v} := TopCat.of
      (↑(CGWH.cgwhToTop.obj I) × ↑(CGWH.cgwhToTop.obj X.right))
    let tensorToRaw : CGWH.cgwhToTop.obj (I ⊗ X.right) ⟶ RawPair :=
      CGWH.cgwhToTop.map eTensor.hom ≫
        CGWH.prodComparisonToTop I X.right
    have eTensor_fst : eTensor.hom ≫
        (Limits.prod.fst : I ⨯ X.right ⟶ I) =
      CartesianMonoidalCategory.fst I X.right :=
      IsLimit.conePointUniqueUpToIso_hom_comp
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct I X.right)
        (limit.isLimit _) ⟨WalkingPair.left⟩
    have eTensor_snd : eTensor.hom ≫
        (Limits.prod.snd : I ⨯ X.right ⟶ X.right) =
      CartesianMonoidalCategory.snd I X.right :=
      IsLimit.conePointUniqueUpToIso_hom_comp
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct I X.right)
        (limit.isLimit _) ⟨WalkingPair.right⟩
    have tensorToRaw_fst : tensorToRaw ≫ TopCat.prodFst =
        CGWH.cgwhToTop.map
          (CartesianMonoidalCategory.fst I X.right) := by
      dsimp only [tensorToRaw]
      rw [Category.assoc, CGWH.prodComparisonToTop_fst,
        ← CGWH.cgwhToTop.map_comp, eTensor_fst]
    have tensorToRaw_snd : tensorToRaw ≫ TopCat.prodSnd =
        CGWH.cgwhToTop.map
          (CartesianMonoidalCategory.snd I X.right) := by
      dsimp only [tensorToRaw]
      rw [Category.assoc, CGWH.prodComparisonToTop_snd,
        ← CGWH.cgwhToTop.map_comp, eTensor_snd]
    have hMap := CGWH.fullyFaithfulCgwhToTop.map_preimage
      (tensorToRaw ≫ TopCat.ofHom
        { toFun := fun z => H (ULift.down z.1, z.2)
          continuous_toFun := H.continuous.comp
            ((continuous_uliftDown.comp continuous_fst).prodMk
              continuous_snd) })
    have ht := ConcreteCategory.congr_hom hMap (insert x)
    have hfst := ConcreteCategory.congr_hom tensorToRaw_fst (insert x)
    have hsnd := ConcreteCategory.congr_hom tensorToRaw_snd (insert x)
    have hInsertFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst
        (CGWH.point_isTerminal.from X.right ≫ endpoint) (𝟙 X.right)) x
    have hInsertSnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd
        (CGWH.point_isTerminal.from X.right ≫ endpoint) (𝟙 X.right)) x
    change hI (insert x) = H (ULift.down (tensorToRaw (insert x)).1,
      (tensorToRaw (insert x)).2) at ht
    change (tensorToRaw (insert x)).1 =
      CartesianMonoidalCategory.fst I X.right (insert x) at hfst
    change (tensorToRaw (insert x)).2 =
      CartesianMonoidalCategory.snd I X.right (insert x) at hsnd
    change CartesianMonoidalCategory.fst I X.right (insert x) = t at hInsertFst
    change CartesianMonoidalCategory.snd I X.right (insert x) = x at hInsertSnd
    rw [hInsertFst] at hfst
    rw [hInsertSnd] at hsnd
    rw [hfst, hsnd] at ht
    simpa only [insert, endpoint] using ht
  have hLeft : leftFace ≫ hProd =
      CGWH.point_isTerminal.from (CGWH.point.{u, v} ⨿ I) ≫ Y.hom := by
    apply coprod.hom_ext
    · let insert : CGWH.point.{u, v} ⟶ CGWH.point ⊗ X.right :=
        CartesianMonoidalCategory.lift (𝟙 _)
          X.hom
      have hFactor : coprod.inl ≫ leftFace =
          insert ≫ (coprod.inl ▷ X.right) := by
        dsimp only [leftFace, insert]
        rw [CartesianMonoidalCategory.comp_lift,
          CartesianMonoidalCategory.lift_whiskerRight]
        congr 1
      rw [← Category.assoc, hFactor, Category.assoc]
      dsimp only [hProd]
      rw [CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv_assoc,
        CategoryTheory.Limits.coprod.inl_desc]
      dsimp only [constantBranch]
      simpa only [Category.assoc] using congrArg
        (fun k : CGWH.point.{u, v} ⟶ CGWH.point ↦ k ≫ Y.hom)
        (CGWH.point_isTerminal.hom_ext
          (insert ≫ CGWH.point_isTerminal.from
            (CGWH.point.{u, v} ⊗ X.right))
          (coprod.inl ≫ CGWH.point_isTerminal.from
            (CGWH.point.{u, v} ⨿ I)))
    · let insert : I ⟶ I ⊗ X.right :=
        CartesianMonoidalCategory.lift (𝟙 I)
          (CGWH.point_isTerminal.from I ≫ X.hom)
      have hFactor : coprod.inr ≫ leftFace =
          insert ≫ (coprod.inr ▷ X.right) := by
        dsimp only [leftFace, insert]
        rw [CartesianMonoidalCategory.comp_lift,
          CartesianMonoidalCategory.lift_whiskerRight]
        congr 1
      rw [← Category.assoc, hFactor, Category.assoc]
      dsimp only [hProd]
      rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc,
        CategoryTheory.Limits.coprod.inr_desc]
      dsimp only [insert]
      rw [hInterval]
      rw [← Category.assoc]
      congr 1
  have hRight : rightFace ≫ hProd =
      CGWH.point_isTerminal.from X.right ≫ Y.hom := by
    let insert : X.right ⟶ CGWH.point.{u, v} ⊗ X.right :=
      CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from X.right) (𝟙 X.right)
    have hFactor : rightFace = insert ≫ (coprod.inl ▷ X.right) := by
      dsimp only [rightFace, insert]
      rw [CartesianMonoidalCategory.lift_whiskerRight]
    rw [hFactor]
    dsimp only [hProd]
    calc
      (insert ≫ (coprod.inl ▷ X.right)) ≫
            (rightDistrib X.right CGWH.point I).inv ≫
              coprod.desc constantBranch hI =
          insert ≫ ((coprod.inl ▷ X.right) ≫
            (rightDistrib X.right CGWH.point I).inv ≫
              coprod.desc constantBranch hI) := by
                simp only [Category.assoc]
      _ = insert ≫ (coprod.inl ≫
          coprod.desc constantBranch hI) := by
        rw [CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv_assoc]
      _ = insert ≫ constantBranch := by
        rw [CategoryTheory.Limits.coprod.inl_desc]
      _ = CGWH.point_isTerminal.from X.right ≫ Y.hom := by
        dsimp only [constantBranch, insert]
        rw [← Category.assoc]
        congr 1
  have hCompat : wRaw ≫ hProd =
      CGWH.point_isTerminal.from (pushout J.hom X.hom) ≫ Y.hom := by
    apply pushout.hom_ext
    · rw [← Category.assoc, hpInl, hLeft]
      simpa only [Category.assoc] using congrArg
        (fun k : (CGWH.point.{u, v} ⨿ I) ⟶ CGWH.point ↦ k ≫ Y.hom)
        (CGWH.point_isTerminal.hom_ext
          (CGWH.point_isTerminal.from (CGWH.point.{u, v} ⨿ I))
          (pushout.inl J.hom X.hom ≫
            CGWH.point_isTerminal.from (pushout J.hom X.hom)))
    · rw [← Category.assoc, hpInr, hRight]
      simpa only [Category.assoc] using congrArg
        (fun k : X.right ⟶ CGWH.point ↦ k ≫ Y.hom)
        (CGWH.point_isTerminal.hom_ext
          (CGWH.point_isTerminal.from X.right)
          (pushout.inr J.hom X.hom ≫
            CGWH.point_isTerminal.from (pushout J.hom X.hom)))
  have hCompatP : p.1.right ≫ hProd =
      CGWH.point_isTerminal.from
          (((CategoryTheory.Pointed.wedge CGWH.point).obj J).obj X).right ≫
        Y.hom := by
    change wRaw ≫ hProd =
      CGWH.point_isTerminal.from (pushout J.hom X.hom) ≫ Y.hom
    exact hCompat
  let desc : p.2.1.pt ⟶ Y.right :=
    PushoutCocone.IsColimit.desc p.2.2 hProd Y.hom hCompatP
  let hCyl : pointedCylinderObj X ⟶ Y := Under.homMk desc
    (PushoutCocone.IsColimit.inr_desc p.2.2 _ _ _)
  have hCylRight : hCyl.right = desc := rfl
  have hq : p.2.1.inl ≫ desc = hProd := by
    dsimp only [desc]
    rw [PushoutCocone.IsColimit.inl_desc]
  let insertI (e : CGWH.point.{u, v} ⟶ I) :
      X.right ⟶ I ⊗ X.right :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from X.right ≫ e) (𝟙 X.right)
  let endpoint (e : CGWH.point.{u, v} ⟶ I) :
      X.right ⟶ J.right ⊗ X.right :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from X.right ≫ e ≫ coprod.inr)
      (𝟙 X.right)
  have hEndpointFactor (e : CGWH.point.{u, v} ⟶ I) :
      endpoint e = insertI e ≫ (coprod.inr ▷ X.right) := by
    dsimp only [endpoint, insertI, J, freePointedInterval]
    cat_disch
  have hI0 : insertI intervalEndpointZero ≫ hI = f.right := by
    apply ConcreteCategory.hom_ext
    intro x
    have hx := hI_apply (ULift.up (0 : unitInterval)) x
    change hI (insertI intervalEndpointZero x) = H ((0 : unitInterval), x) at hx
    exact hx.trans (H.map_zero_left x)
  have hI1 : insertI intervalEndpointOne ≫ hI = g.right := by
    apply ConcreteCategory.hom_ext
    intro x
    have hx := hI_apply (ULift.up (1 : unitInterval)) x
    change hI (insertI intervalEndpointOne x) = H ((1 : unitInterval), x) at hx
    exact hx.trans (H.map_one_left x)
  have hEndpoint0 : endpoint intervalEndpointZero ≫ hProd = f.right := by
    rw [hEndpointFactor, Category.assoc]
    dsimp only [hProd]
    rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc,
      CategoryTheory.Limits.coprod.inr_desc]
    exact hI0
  have hEndpoint1 : endpoint intervalEndpointOne ≫ hProd = g.right := by
    rw [hEndpointFactor, Category.assoc]
    dsimp only [hProd]
    rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc,
      CategoryTheory.Limits.coprod.inr_desc]
    exact hI1
  have hi0Right : (pointedCylinderI0 X).right =
      endpoint intervalEndpointZero ≫ p.2.1.inl := by rfl
  have hi1Right : (pointedCylinderI1 X).right =
      endpoint intervalEndpointOne ≫ p.2.1.inl := by rfl
  refine ⟨hCyl, ?_, ?_⟩
  · apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro x
    have hi := ConcreteCategory.congr_hom hi0Right x
    have hq' := ConcreteCategory.congr_hom hq (endpoint intervalEndpointZero x)
    have he := ConcreteCategory.congr_hom hEndpoint0 x
    calc
      hCyl.right ((pointedCylinderI0 X).right x) =
          hCyl.right ((endpoint intervalEndpointZero ≫ p.2.1.inl) x) :=
        congrArg (fun z => hCyl.right z) hi
      _ = desc ((endpoint intervalEndpointZero ≫ p.2.1.inl) x) :=
        congrArg (fun k => k ((endpoint intervalEndpointZero ≫ p.2.1.inl) x))
          hCylRight
      _ = hProd (endpoint intervalEndpointZero x) := hq'
      _ = f.right x := he
  · apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro x
    have hi := ConcreteCategory.congr_hom hi1Right x
    have hq' := ConcreteCategory.congr_hom hq (endpoint intervalEndpointOne x)
    have he := ConcreteCategory.congr_hom hEndpoint1 x
    calc
      hCyl.right ((pointedCylinderI1 X).right x) =
          hCyl.right ((endpoint intervalEndpointOne ≫ p.2.1.inl) x) :=
        congrArg (fun z => hCyl.right z) hi
      _ = desc ((endpoint intervalEndpointOne ≫ p.2.1.inl) x) :=
        congrArg (fun k => k ((endpoint intervalEndpointOne ≫ p.2.1.inl) x))
          hCylRight
      _ = hProd (endpoint intervalEndpointOne x) := hq'
      _ = g.right x := he

/-- Multiplication on the interval contracts the free interval to its zero
endpoint while preserving its freely adjoined point. -/
private noncomputable def freeIntervalContraction :
    { c : cgwhInterval.{u, v} ⊗ freePointedInterval.{u, v}.right ⟶
        freePointedInterval.{u, v}.right //
      (cgwhInterval.{u, v} ◁ freePointedInterval.{u, v}.hom) ≫ c =
        CGWH.point_isTerminal.from
            (cgwhInterval.{u, v} ⊗ CGWH.point.{u, v}) ≫
          freePointedInterval.{u, v}.hom ∧
      CartesianMonoidalCategory.lift
            (CGWH.point_isTerminal.from freePointedInterval.{u, v}.right ≫
              intervalEndpointZero.{u, v})
            (𝟙 freePointedInterval.{u, v}.right) ≫ c =
        coprod.desc coprod.inl
          (CGWH.point_isTerminal.from cgwhInterval.{u, v} ≫
            intervalEndpointZero.{u, v} ≫ coprod.inr) ∧
      CartesianMonoidalCategory.lift
            (CGWH.point_isTerminal.from freePointedInterval.{u, v}.right ≫
              intervalEndpointOne.{u, v})
            (𝟙 freePointedInterval.{u, v}.right) ≫ c = 𝟙 _ } := by
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  letI : IsMonoidalDistrib CGWH.{u, v} := inferInstance
  let I := cgwhInterval.{u, v}
  let eTensor : I ⊗ I ≅ I ⨯ I :=
    (CartesianMonoidalCategory.tensorLeftIsoProd I).app I
  let RawPair : TopCat.{v} := TopCat.of
    (↑(CGWH.cgwhToTop.obj I) × ↑(CGWH.cgwhToTop.obj I))
  let tensorToRaw : CGWH.cgwhToTop.obj (I ⊗ I) ⟶ RawPair :=
    CGWH.cgwhToTop.map eTensor.hom ≫ CGWH.prodComparisonToTop I I
  have eTensor_fst : eTensor.hom ≫
      (Limits.prod.fst : I ⨯ I ⟶ I) =
    CartesianMonoidalCategory.fst I I :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct I I)
      (limit.isLimit _) ⟨WalkingPair.left⟩
  have eTensor_snd : eTensor.hom ≫
      (Limits.prod.snd : I ⨯ I ⟶ I) =
    CartesianMonoidalCategory.snd I I :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct I I)
      (limit.isLimit _) ⟨WalkingPair.right⟩
  have tensorToRaw_fst : tensorToRaw ≫ TopCat.prodFst =
      CGWH.cgwhToTop.map (CartesianMonoidalCategory.fst I I) := by
    dsimp only [tensorToRaw]
    rw [Category.assoc, CGWH.prodComparisonToTop_fst,
      ← CGWH.cgwhToTop.map_comp, eTensor_fst]
  have tensorToRaw_snd : tensorToRaw ≫ TopCat.prodSnd =
      CGWH.cgwhToTop.map (CartesianMonoidalCategory.snd I I) := by
    dsimp only [tensorToRaw]
    rw [Category.assoc, CGWH.prodComparisonToTop_snd,
      ← CGWH.cgwhToTop.map_comp, eTensor_snd]
  let mulRaw : C(RawPair, I) :=
    { toFun := fun z => ULift.up (ULift.down z.1 * ULift.down z.2)
      continuous_toFun := continuous_uliftUp.comp
        ((continuous_uliftDown.comp continuous_fst).mul
          (continuous_uliftDown.comp continuous_snd)) }
  let mulTop : CGWH.cgwhToTop.obj (I ⊗ I) ⟶ CGWH.cgwhToTop.obj I :=
    tensorToRaw ≫ TopCat.ofHom mulRaw
  let mulNative : I ⊗ I ⟶ I :=
    CGWH.fullyFaithfulCgwhToTop.preimage mulTop
  have hMulZero : CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from I ≫ intervalEndpointZero.{u, v})
        (𝟙 I) ≫ mulNative =
      CGWH.point_isTerminal.from I ≫ intervalEndpointZero.{u, v} := by
    apply ConcreteCategory.hom_ext
    intro t
    let insert : I ⟶ I ⊗ I := CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from I ≫ intervalEndpointZero.{u, v}) (𝟙 I)
    have hMap := CGWH.fullyFaithfulCgwhToTop.map_preimage mulTop
    have ht := ConcreteCategory.congr_hom hMap (insert t)
    have hfst := ConcreteCategory.congr_hom tensorToRaw_fst (insert t)
    have hsnd := ConcreteCategory.congr_hom tensorToRaw_snd (insert t)
    have hInsertFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst
        (CGWH.point_isTerminal.from I ≫ intervalEndpointZero.{u, v}) (𝟙 I)) t
    have hInsertSnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd
        (CGWH.point_isTerminal.from I ≫ intervalEndpointZero.{u, v}) (𝟙 I)) t
    change mulNative (insert t) =
      ULift.up (ULift.down (tensorToRaw (insert t)).1 *
        ULift.down (tensorToRaw (insert t)).2) at ht
    change (tensorToRaw (insert t)).1 =
      CartesianMonoidalCategory.fst I I (insert t) at hfst
    change (tensorToRaw (insert t)).2 =
      CartesianMonoidalCategory.snd I I (insert t) at hsnd
    change CartesianMonoidalCategory.fst I I (insert t) =
      ULift.up (0 : unitInterval) at hInsertFst
    change CartesianMonoidalCategory.snd I I (insert t) = t at hInsertSnd
    rw [hInsertFst] at hfst
    rw [hInsertSnd] at hsnd
    rw [hfst, hsnd] at ht
    have ht' : mulNative (insert t) = ULift.up (0 : unitInterval) := by
      simpa using ht
    have hEndpoint :
        (ConcreteCategory.hom intervalEndpointZero)
            ((ConcreteCategory.hom (CGWH.point_isTerminal.from I)) t) =
          ULift.up (0 : unitInterval) := rfl
    simpa [insert] using ht'.trans hEndpoint.symm
  have hMulOne : CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from I ≫ intervalEndpointOne.{u, v})
        (𝟙 I) ≫ mulNative = 𝟙 I := by
    apply ConcreteCategory.hom_ext
    intro t
    let insert : I ⟶ I ⊗ I := CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from I ≫ intervalEndpointOne.{u, v}) (𝟙 I)
    have hMap := CGWH.fullyFaithfulCgwhToTop.map_preimage mulTop
    have ht := ConcreteCategory.congr_hom hMap (insert t)
    have hfst := ConcreteCategory.congr_hom tensorToRaw_fst (insert t)
    have hsnd := ConcreteCategory.congr_hom tensorToRaw_snd (insert t)
    have hInsertFst := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst
        (CGWH.point_isTerminal.from I ≫ intervalEndpointOne.{u, v}) (𝟙 I)) t
    have hInsertSnd := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd
        (CGWH.point_isTerminal.from I ≫ intervalEndpointOne.{u, v}) (𝟙 I)) t
    change mulNative (insert t) =
      ULift.up (ULift.down (tensorToRaw (insert t)).1 *
        ULift.down (tensorToRaw (insert t)).2) at ht
    change (tensorToRaw (insert t)).1 =
      CartesianMonoidalCategory.fst I I (insert t) at hfst
    change (tensorToRaw (insert t)).2 =
      CartesianMonoidalCategory.snd I I (insert t) at hsnd
    change CartesianMonoidalCategory.fst I I (insert t) =
      ULift.up (1 : unitInterval) at hInsertFst
    change CartesianMonoidalCategory.snd I I (insert t) = t at hInsertSnd
    rw [hInsertFst] at hfst
    rw [hInsertSnd] at hsnd
    rw [hfst, hsnd] at ht
    have ht' : mulNative (insert t) = ULift.up (ULift.down t) := by
      simpa using ht
    simpa [insert] using ht'.trans (ULift.up_down t)
  let baseBranch : I ⊗ CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ I :=
    CGWH.point_isTerminal.from _ ≫ coprod.inl
  let intervalBranch : I ⊗ I ⟶ CGWH.point.{u, v} ⨿ I :=
    mulNative ≫ coprod.inr
  let c := (leftDistrib I CGWH.point I).inv ≫
    coprod.desc baseBranch intervalBranch
  refine ⟨c, ?_, ?_, ?_⟩
  · change (I ◁ (coprod.inl : CGWH.point.{u, v} ⟶
        CGWH.point ⨿ I)) ≫ c =
      CGWH.point_isTerminal.from (I ⊗ CGWH.point) ≫ coprod.inl
    dsimp only [c]
    calc
      (I ◁ (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point ⨿ I)) ≫
            (leftDistrib I CGWH.point I).inv ≫
              coprod.desc baseBranch intervalBranch =
          ((I ◁ (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point ⨿ I)) ≫
            (leftDistrib I CGWH.point I).inv) ≫
              coprod.desc baseBranch intervalBranch :=
        (Category.assoc _ _ _).symm
      _ = coprod.inl ≫ coprod.desc baseBranch intervalBranch := by
        rw [CategoryTheory.whiskerLeft_coprod_inl_leftDistrib_inv]
      _ = baseBranch := CategoryTheory.Limits.coprod.inl_desc _ _
      _ = CGWH.point_isTerminal.from (I ⊗ CGWH.point) ≫ coprod.inl := rfl
  · change CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from (CGWH.point.{u, v} ⨿ I) ≫
            intervalEndpointZero) (𝟙 (CGWH.point ⨿ I)) ≫ c =
      coprod.desc coprod.inl
        (CGWH.point_isTerminal.from I ≫ intervalEndpointZero ≫ coprod.inr)
    apply coprod.hom_ext
    · let insert : CGWH.point.{u, v} ⟶ I ⊗ CGWH.point :=
        CartesianMonoidalCategory.lift intervalEndpointZero (𝟙 _)
      have hFactor : coprod.inl ≫
          CartesianMonoidalCategory.lift
            (CGWH.point_isTerminal.from (CGWH.point.{u, v} ⨿ I) ≫
              intervalEndpointZero) (𝟙 _) =
        insert ≫ (I ◁ coprod.inl) := by
        dsimp only [insert]
        cat_disch
      rw [← Category.assoc, hFactor, Category.assoc]
      dsimp only [c]
      rw [CategoryTheory.whiskerLeft_coprod_inl_leftDistrib_inv_assoc,
        CategoryTheory.Limits.coprod.inl_desc]
      dsimp only [baseBranch]
      rw [CategoryTheory.Limits.coprod.inl_desc]
      congr 1
    · let insert : I ⟶ I ⊗ I := CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from I ≫ intervalEndpointZero) (𝟙 I)
      have hFactor : coprod.inr ≫
          CartesianMonoidalCategory.lift
            (CGWH.point_isTerminal.from (CGWH.point.{u, v} ⨿ I) ≫
              intervalEndpointZero) (𝟙 _) =
        insert ≫ (I ◁ coprod.inr) := by
        dsimp only [insert]
        cat_disch
      rw [← Category.assoc, hFactor, Category.assoc]
      dsimp only [c]
      rw [CategoryTheory.whiskerLeft_coprod_inr_leftDistrib_inv_assoc,
        CategoryTheory.Limits.coprod.inr_desc]
      dsimp only [intervalBranch, insert]
      rw [← Category.assoc, hMulZero, Category.assoc,
        CategoryTheory.Limits.coprod.inr_desc]
  · change CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from (CGWH.point.{u, v} ⨿ I) ≫
            intervalEndpointOne) (𝟙 (CGWH.point ⨿ I)) ≫ c =
      𝟙 (CGWH.point ⨿ I)
    apply coprod.hom_ext
    · let insert : CGWH.point.{u, v} ⟶ I ⊗ CGWH.point :=
        CartesianMonoidalCategory.lift intervalEndpointOne (𝟙 _)
      have hFactor : coprod.inl ≫
          CartesianMonoidalCategory.lift
            (CGWH.point_isTerminal.from (CGWH.point.{u, v} ⨿ I) ≫
              intervalEndpointOne) (𝟙 _) =
        insert ≫ (I ◁ coprod.inl) := by
        dsimp only [insert]
        cat_disch
      rw [← Category.assoc, hFactor, Category.assoc]
      dsimp only [c]
      rw [CategoryTheory.whiskerLeft_coprod_inl_leftDistrib_inv_assoc,
        CategoryTheory.Limits.coprod.inl_desc]
      dsimp only [baseBranch]
      have hPoint : insert ≫ CGWH.point_isTerminal.from (I ⊗ CGWH.point) =
          𝟙 CGWH.point := CGWH.point_isTerminal.hom_ext _ _
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun k => k ≫ (coprod.inl : CGWH.point ⟶ CGWH.point ⨿ I)) hPoint
    · let insert : I ⟶ I ⊗ I := CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from I ≫ intervalEndpointOne) (𝟙 I)
      have hFactor : coprod.inr ≫
          CartesianMonoidalCategory.lift
            (CGWH.point_isTerminal.from (CGWH.point.{u, v} ⨿ I) ≫
              intervalEndpointOne) (𝟙 _) =
        insert ≫ (I ◁ coprod.inr) := by
        dsimp only [insert]
        cat_disch
      rw [← Category.assoc, hFactor, Category.assoc]
      dsimp only [c]
      rw [CategoryTheory.whiskerLeft_coprod_inr_leftDistrib_inv_assoc,
        CategoryTheory.Limits.coprod.inr_desc]
      dsimp only [intervalBranch, insert]
      rw [← Category.assoc, hMulOne, Category.id_comp, Category.comp_id]

/-- The contraction of the reduced cylinder, still parameterized by the
included lifted interval and the selected TopCat categorical product. -/
private noncomputable def pointedCylinderRawContraction
    (X : PointedCGWH.{u, v}) :
    let I := cgwhInterval.{u, v}
    let T := CGWH.cgwhToTop.{u, v}
    let P := (pointedCylinderObj X).right
    let z0 : T.obj P ⟶ T.obj I ⨯ T.obj P :=
      rawIntervalEndpoint intervalEndpointZero (T.obj P)
    let z1 : T.obj P ⟶ T.obj I ⨯ T.obj P :=
      rawIntervalEndpoint intervalEndpointOne (T.obj P)
    { K : T.obj I ⨯ T.obj P ⟶ T.obj P //
      z0 ≫ K = T.map
        ((pointedCylinderProjection X).1.right ≫
          (pointedCylinderI0 X).right) ∧
      z1 ≫ K = 𝟙 (T.obj P) } := by
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  letI : IsMonoidalDistrib CGWH.{u, v} := inferInstance
  let I := cgwhInterval.{u, v}
  let J := freePointedInterval.{u, v}
  let P := pointedCylinderObj X
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal J X
  let W := pushout J.hom X.hom
  let A := J.right ⊗ X.right
  let B := CGWH.point.{u, v}
  let i : W ⟶ A := p.1.right
  let fW : W ⟶ B := CGWH.point_isTerminal.from W
  let r : A ⟶ P.right := p.2.1.inl
  let b : B ⟶ P.right := p.2.1.inr
  let contractJ : I ⊗ J.right ⟶ J.right :=
    freeIntervalContraction.{u, v}.1
  have hContractBase : (I ◁ J.hom) ≫ contractJ =
      CGWH.point_isTerminal.from (I ⊗ B) ≫ J.hom :=
    freeIntervalContraction.{u, v}.2.1
  let leftFace : J.right ⟶ A :=
    CartesianMonoidalCategory.lift (𝟙 J.right)
      (CGWH.point_isTerminal.from J.right ≫ X.hom)
  let rightFace : X.right ⟶ A :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from X.right ≫ J.hom) (𝟙 X.right)
  have hpInl : pushout.inl J.hom X.hom ≫ i = leftFace := by
    dsimp only [i, p, CategoryTheory.Pointed.smashPresentation]
    change pushout.inl J.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inl_desc]
    rfl
  have hpInr : pushout.inr J.hom X.hom ≫ i = rightFace := by
    dsimp only [i, p, CategoryTheory.Pointed.smashPresentation]
    change pushout.inr J.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inr_desc]
    rfl
  have hCondition : i ≫ r = fW ≫ b := by
    exact p.2.1.condition
  have hAssocLeft : (I ◁ leftFace) ≫ (α_ I J.right X.right).inv ≫
        (contractJ ⊗ₘ 𝟙 X.right) = contractJ ≫ leftFace := by
    have hPair : (I ◁ leftFace) ≫ (α_ I J.right X.right).inv ≫
        CartesianMonoidalCategory.fst (I ⊗ J.right) X.right =
      𝟙 (I ⊗ J.right) := by
      dsimp only [leftFace]
      cat_disch
    have hX : (I ◁ leftFace) ≫ (α_ I J.right X.right).inv ≫
        CartesianMonoidalCategory.snd (I ⊗ J.right) X.right =
      CGWH.point_isTerminal.from (I ⊗ J.right) ≫ X.hom := by
      dsimp only [leftFace]
      cat_disch
    apply CartesianMonoidalCategory.hom_ext
    · calc
        ((I ◁ leftFace) ≫ (α_ I J.right X.right).inv ≫
              (contractJ ⊗ₘ 𝟙 X.right)) ≫
            CartesianMonoidalCategory.fst J.right X.right =
          ((I ◁ leftFace) ≫ (α_ I J.right X.right).inv ≫
              CartesianMonoidalCategory.fst (I ⊗ J.right) X.right) ≫
            contractJ := by
              simp only [Category.assoc,
                CartesianMonoidalCategory.tensorHom_fst]
        _ = (𝟙 (I ⊗ J.right)) ≫ contractJ := by rw [hPair]
        _ = contractJ := Category.id_comp _
        _ = (contractJ ≫ leftFace) ≫
            CartesianMonoidalCategory.fst J.right X.right := by
          rw [Category.assoc]
          dsimp only [leftFace]
          rw [CartesianMonoidalCategory.lift_fst, Category.comp_id]
    · calc
        ((I ◁ leftFace) ≫ (α_ I J.right X.right).inv ≫
              (contractJ ⊗ₘ 𝟙 X.right)) ≫
            CartesianMonoidalCategory.snd J.right X.right =
          (I ◁ leftFace) ≫ (α_ I J.right X.right).inv ≫
            CartesianMonoidalCategory.snd (I ⊗ J.right) X.right := by
              simp only [Category.assoc,
                CartesianMonoidalCategory.tensorHom_snd, Category.comp_id]
        _ = CGWH.point_isTerminal.from (I ⊗ J.right) ≫ X.hom := hX
        _ = contractJ ≫ CGWH.point_isTerminal.from J.right ≫ X.hom := by
          rw [show CGWH.point_isTerminal.from (I ⊗ J.right) =
            contractJ ≫ CGWH.point_isTerminal.from J.right from
              CGWH.point_isTerminal.hom_ext _ _, Category.assoc]
        _ = (contractJ ≫ leftFace) ≫
            CartesianMonoidalCategory.snd J.right X.right := by
          rw [Category.assoc]
          dsimp only [leftFace]
          rw [CartesianMonoidalCategory.lift_snd]
  have hAssocRight : (I ◁ rightFace) ≫ (α_ I J.right X.right).inv ≫
        (contractJ ⊗ₘ 𝟙 X.right) =
      CartesianMonoidalCategory.snd I X.right ≫ rightFace := by
    let toBase : I ⊗ X.right ⟶ I ⊗ B :=
      I ◁ CGWH.point_isTerminal.from X.right
    have hPair : (I ◁ rightFace) ≫ (α_ I J.right X.right).inv ≫
        CartesianMonoidalCategory.fst (I ⊗ J.right) X.right =
      toBase ≫ (I ◁ J.hom) := by
      dsimp only [rightFace, toBase]
      cat_disch
    have hX : (I ◁ rightFace) ≫ (α_ I J.right X.right).inv ≫
        CartesianMonoidalCategory.snd (I ⊗ J.right) X.right =
      CartesianMonoidalCategory.snd I X.right := by
      dsimp only [rightFace]
      cat_disch
    apply CartesianMonoidalCategory.hom_ext
    · calc
        ((I ◁ rightFace) ≫ (α_ I J.right X.right).inv ≫
              (contractJ ⊗ₘ 𝟙 X.right)) ≫
            CartesianMonoidalCategory.fst J.right X.right =
          ((I ◁ rightFace) ≫ (α_ I J.right X.right).inv ≫
              CartesianMonoidalCategory.fst (I ⊗ J.right) X.right) ≫
            contractJ := by
              simp only [Category.assoc,
                CartesianMonoidalCategory.tensorHom_fst]
        _ = (toBase ≫ (I ◁ J.hom)) ≫ contractJ := by rw [hPair]
        _ = toBase ≫ CGWH.point_isTerminal.from (I ⊗ B) ≫ J.hom := by
          rw [Category.assoc, hContractBase]
        _ = CartesianMonoidalCategory.snd I X.right ≫
            CGWH.point_isTerminal.from X.right ≫ J.hom := by
          dsimp only [toBase]
          have ht : (I ◁ CGWH.point_isTerminal.from X.right) ≫
                CGWH.point_isTerminal.from (I ⊗ B) =
              CartesianMonoidalCategory.snd I X.right ≫
                CGWH.point_isTerminal.from X.right :=
            CGWH.point_isTerminal.hom_ext _ _
          simpa only [Category.assoc] using congrArg
            (fun k : I ⊗ X.right ⟶ B ↦ k ≫ J.hom) ht
        _ = (CartesianMonoidalCategory.snd I X.right ≫ rightFace) ≫
            CartesianMonoidalCategory.fst J.right X.right := by
          rw [Category.assoc]
          dsimp only [rightFace]
          rw [CartesianMonoidalCategory.lift_fst]
    · calc
        ((I ◁ rightFace) ≫ (α_ I J.right X.right).inv ≫
              (contractJ ⊗ₘ 𝟙 X.right)) ≫
            CartesianMonoidalCategory.snd J.right X.right =
          (I ◁ rightFace) ≫ (α_ I J.right X.right).inv ≫
            CartesianMonoidalCategory.snd (I ⊗ J.right) X.right := by
              simp only [Category.assoc,
                CartesianMonoidalCategory.tensorHom_snd, Category.comp_id]
        _ = CartesianMonoidalCategory.snd I X.right := hX
        _ = (CartesianMonoidalCategory.snd I X.right ≫ rightFace) ≫
            CartesianMonoidalCategory.snd J.right X.right := by
          symm
          calc
            (CartesianMonoidalCategory.snd I X.right ≫ rightFace) ≫
                  CartesianMonoidalCategory.snd J.right X.right =
                CartesianMonoidalCategory.snd I X.right ≫
                  (rightFace ≫
                    CartesianMonoidalCategory.snd J.right X.right) :=
              Category.assoc _ _ _
            _ = CartesianMonoidalCategory.snd I X.right ≫ 𝟙 X.right := by
              dsimp only [rightFace]
              rw [CartesianMonoidalCategory.lift_snd]
            _ = CartesianMonoidalCategory.snd I X.right := Category.comp_id _
  let cA : I ⊗ A ⟶ P.right :=
    (α_ I J.right X.right).inv ≫
      (contractJ ⊗ₘ 𝟙 X.right) ≫ r
  let cB : I ⊗ B ⟶ P.right :=
    CGWH.point_isTerminal.from (I ⊗ B) ≫ b
  let kA_native : I ⨯ A ⟶ P.right :=
    (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app A ≫ cA
  let kB_native : I ⨯ B ⟶ P.right :=
    (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app B ≫ cB
  have hNative : Limits.prod.map (𝟙 I) i ≫ kA_native =
      Limits.prod.map (𝟙 I) fW ≫ kB_native := by
    have hEi := (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.naturality i
    have hEf := (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.naturality fW
    change (Limits.prod.functor.obj I).map i ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app A =
      (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app W ≫
        (I ◁ i) at hEi
    change (Limits.prod.functor.obj I).map fW ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app B =
      (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app W ≫
        (I ◁ fW) at hEf
    let hPush := (MonoidalCategory.tensorLeft I).map_isPushout
      (IsPushout.of_hasPushout J.hom X.hom)
    have hInner : (I ◁ i) ≫ cA = (I ◁ fW) ≫ cB := by
      apply hPush.hom_ext
      · change (I ◁ pushout.inl J.hom X.hom) ≫
            (I ◁ i) ≫ cA =
          (I ◁ pushout.inl J.hom X.hom) ≫
            (I ◁ fW) ≫ cB
        have hLi : (I ◁ pushout.inl J.hom X.hom) ≫ (I ◁ i) =
            I ◁ leftFace := by
          change (MonoidalCategory.tensorLeft I).map
              (pushout.inl J.hom X.hom) ≫
                (MonoidalCategory.tensorLeft I).map i =
            (MonoidalCategory.tensorLeft I).map leftFace
          rw [← Functor.map_comp, hpInl]
        calc
          (I ◁ pushout.inl J.hom X.hom) ≫ (I ◁ i) ≫ cA =
              (I ◁ leftFace) ≫ cA := by
            rw [← Category.assoc, hLi]
          _ = contractJ ≫ leftFace ≫ r := by
            dsimp only [cA]
            simpa only [Category.assoc] using congrArg
              (fun k => k ≫ r) hAssocLeft
          _ = contractJ ≫ pushout.inl J.hom X.hom ≫ i ≫ r := by
            simpa only [Category.assoc] using (congrArg
              (fun k => contractJ ≫ k ≫ r) hpInl).symm
          _ = contractJ ≫ pushout.inl J.hom X.hom ≫ fW ≫ b := by
            simpa only [Category.assoc] using congrArg
              (fun k => contractJ ≫ pushout.inl J.hom X.hom ≫ k)
              hCondition
          _ = (I ◁ pushout.inl J.hom X.hom) ≫
                (I ◁ fW) ≫ cB := by
            dsimp only [cB]
            have ht : contractJ ≫ pushout.inl J.hom X.hom ≫ fW =
                (I ◁ pushout.inl J.hom X.hom) ≫
                  (I ◁ fW) ≫ CGWH.point_isTerminal.from (I ⊗ B) :=
              CGWH.point_isTerminal.hom_ext _ _
            simpa only [Category.assoc] using congrArg
              (fun k : I ⊗ J.right ⟶ B ↦ k ≫ b) ht
      · change (I ◁ pushout.inr J.hom X.hom) ≫
            (I ◁ i) ≫ cA =
          (I ◁ pushout.inr J.hom X.hom) ≫
            (I ◁ fW) ≫ cB
        have hRi : (I ◁ pushout.inr J.hom X.hom) ≫ (I ◁ i) =
            I ◁ rightFace := by
          change (MonoidalCategory.tensorLeft I).map
              (pushout.inr J.hom X.hom) ≫
                (MonoidalCategory.tensorLeft I).map i =
            (MonoidalCategory.tensorLeft I).map rightFace
          rw [← Functor.map_comp, hpInr]
        calc
          (I ◁ pushout.inr J.hom X.hom) ≫ (I ◁ i) ≫ cA =
              (I ◁ rightFace) ≫ cA := by
            rw [← Category.assoc, hRi]
          _ = CartesianMonoidalCategory.snd I X.right ≫ rightFace ≫ r := by
            dsimp only [cA]
            simpa only [Category.assoc] using congrArg
              (fun k => k ≫ r) hAssocRight
          _ = CartesianMonoidalCategory.snd I X.right ≫
                pushout.inr J.hom X.hom ≫ i ≫ r := by
            simpa only [Category.assoc] using (congrArg
              (fun k => CartesianMonoidalCategory.snd I X.right ≫ k ≫ r)
              hpInr).symm
          _ = CartesianMonoidalCategory.snd I X.right ≫
                pushout.inr J.hom X.hom ≫ fW ≫ b := by
            simpa only [Category.assoc] using congrArg
              (fun k => CartesianMonoidalCategory.snd I X.right ≫
                pushout.inr J.hom X.hom ≫ k) hCondition
          _ = (I ◁ pushout.inr J.hom X.hom) ≫
                (I ◁ fW) ≫ cB := by
            dsimp only [cB]
            have ht : CartesianMonoidalCategory.snd I X.right ≫
                  pushout.inr J.hom X.hom ≫ fW =
                (I ◁ pushout.inr J.hom X.hom) ≫
                  (I ◁ fW) ≫ CGWH.point_isTerminal.from (I ⊗ B) :=
              CGWH.point_isTerminal.hom_ext _ _
            simpa only [Category.assoc] using congrArg
              (fun k : I ⊗ X.right ⟶ B ↦ k ≫ b) ht
    change (Limits.prod.functor.obj I).map i ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app A ≫ cA =
      (Limits.prod.functor.obj I).map fW ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app B ≫ cB
    calc
      (Limits.prod.functor.obj I).map i ≫
            (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app A ≫ cA =
          ((Limits.prod.functor.obj I).map i ≫
            (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app A) ≫
              cA := (Category.assoc _ _ _).symm
      _ = ((CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app W ≫
            (I ◁ i)) ≫ cA := by rw [hEi]
      _ = (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app W ≫
            ((I ◁ i) ≫ cA) := Category.assoc _ _ _
      _ = (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app W ≫
            ((I ◁ fW) ≫ cB) := by rw [hInner]
      _ = ((CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app W ≫
            (I ◁ fW)) ≫ cB := (Category.assoc _ _ _).symm
      _ = ((Limits.prod.functor.obj I).map fW ≫
            (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app B) ≫
              cB := by rw [hEf]
      _ = (Limits.prod.functor.obj I).map fW ≫
            (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app B ≫ cB :=
        Category.assoc _ _ _
  have hi : IsClosedEmbedding (ConcreteCategory.hom
      (CGWH.cgwhToTop.map i)) := by
    change IsClosedEmbedding (ConcreteCategory.hom i)
    exact PointedCGWH.wedgeToProduct_isClosedEmbedding J X
  let R := pushout (CGWH.cgwhToTop.map i) (CGWH.cgwhToTop.map fW)
  let rawInl : CGWH.cgwhToTop.obj A ⟶ R :=
    pushout.inl (CGWH.cgwhToTop.map i) (CGWH.cgwhToTop.map fW)
  let rawInr : CGWH.cgwhToTop.obj B ⟶ R :=
    pushout.inr (CGWH.cgwhToTop.map i) (CGWH.cgwhToTop.map fW)
  let eP : R ≅ CGWH.cgwhToTop.obj P.right :=
    CGWH.pushoutClosedComparisonIso i fW hi
  let qA := intervalProdComparisonIso A
  let qB := intervalProdComparisonIso B
  let qW := intervalProdComparisonIso W
  let kA_raw := qA.inv ≫ CGWH.cgwhToTop.map kA_native
  let kB_raw := qB.inv ≫ CGWH.cgwhToTop.map kB_native
  have hRaw : Limits.prod.map (𝟙 (CGWH.cgwhToTop.obj I))
        (CGWH.cgwhToTop.map i) ≫ kA_raw =
      Limits.prod.map (𝟙 (CGWH.cgwhToTop.obj I))
        (CGWH.cgwhToTop.map fW) ≫ kB_raw := by
    dsimp only [kA_raw, kB_raw, qA, qB, qW]
    rw [← Category.assoc, intervalProdComparisonIso_naturality,
      ← Category.assoc, intervalProdComparisonIso_naturality]
    rw [Category.assoc, Category.assoc, ← CGWH.cgwhToTop.map_comp,
      ← CGWH.cgwhToTop.map_comp, hNative]
  let _ : LocallyCompactSpace (CGWH.cgwhToTop.obj I) := by
    change LocallyCompactSpace (ULift.{v} unitInterval)
    infer_instance
  let hProd := TopCat.isPushout_prodMap_left_of_isPushout
    (K := CGWH.cgwhToTop.obj I)
    (IsPushout.of_hasPushout (CGWH.cgwhToTop.map i)
      (CGWH.cgwhToTop.map fW))
  let d : (CGWH.cgwhToTop.obj I ⨯ R) ⟶
      CGWH.cgwhToTop.obj P.right :=
    hProd.desc kA_raw kB_raw hRaw
  let T := CGWH.cgwhToTop.{u, v}
  let nativeEndpoint (e : CGWH.point.{u, v} ⟶ I) (Z : CGWH.{u, v}) :
      Z ⟶ I ⨯ Z :=
    Limits.prod.lift (CGWH.point_isTerminal.from Z ≫ e) (𝟙 Z)
  have hQE (e : CGWH.point.{u, v} ⟶ I) (Z : CGWH.{u, v}) :
      rawIntervalEndpoint e (T.obj Z) ≫ (intervalProdComparisonIso Z).inv =
        T.map (nativeEndpoint e Z) := by
    exact rawIntervalEndpoint_comparison e Z
  have hApex (e : CGWH.point.{u, v} ⟶ I) :
      eP.hom ≫ rawIntervalEndpoint e (T.obj P.right) ≫
          Limits.prod.map (𝟙 (T.obj I)) eP.inv =
        rawIntervalEndpoint e R := by
    rw [← Category.assoc, rawIntervalEndpoint_naturality]
    dsimp only [T, I]
    simp only [Category.assoc, Limits.prod.map_map,
      Iso.hom_inv_id, Category.comp_id,
      Limits.prod.map_id_id]
  have hLegL (e : CGWH.point.{u, v} ⟶ I) :
      rawInl ≫ rawIntervalEndpoint e R =
        rawIntervalEndpoint e (T.obj A) ≫
          Limits.prod.map (𝟙 (T.obj I)) rawInl :=
    rawIntervalEndpoint_naturality e rawInl
  have hLegR (e : CGWH.point.{u, v} ⟶ I) :
      rawInr ≫ rawIntervalEndpoint e R =
        rawIntervalEndpoint e (T.obj B) ≫
          Limits.prod.map (𝟙 (T.obj I)) rawInr :=
    rawIntervalEndpoint_naturality e rawInr
  have hDInl : Limits.prod.map (𝟙 (T.obj I)) rawInl ≫ d = kA_raw :=
    hProd.inl_desc kA_raw kB_raw hRaw
  have hDInr : Limits.prod.map (𝟙 (T.obj I)) rawInr ≫ d = kB_raw :=
    hProd.inr_desc kA_raw kB_raw hRaw
  have hr : pushout.inl i fW = r := by rfl
  have hb : pushout.inr i fW = b := by rfl
  have hEPInl : rawInl ≫ eP.hom = T.map r := by
    rw [← hr]
    exact CGWH.pushoutClosedComparisonIso_hom_inl i fW hi
  have hEPInr : rawInr ≫ eP.hom = T.map b := by
    rw [← hb]
    exact CGWH.pushoutClosedComparisonIso_hom_inr i fW hi
  let Kraw := Limits.prod.map (𝟙 (T.obj I)) eP.inv ≫ d
  have endpoint_tensor (e : CGWH.point.{u, v} ⟶ I) (Z : CGWH.{u, v}) :
      nativeEndpoint e Z ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app Z =
        CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from Z ≫ e) (𝟙 Z) := by
    let eTensor : I ⊗ Z ≅ I ⨯ Z :=
      (CartesianMonoidalCategory.tensorLeftIsoProd I).app Z
    change nativeEndpoint e Z ≫ eTensor.inv = _
    have hFst : eTensor.inv ≫
          CartesianMonoidalCategory.fst I Z =
        (Limits.prod.fst : I ⨯ Z ⟶ I) := by
      dsimp only [eTensor]
      exact IsLimit.conePointUniqueUpToIso_inv_comp
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct I Z)
        (limit.isLimit _) ⟨WalkingPair.left⟩
    have hSnd : eTensor.inv ≫
          CartesianMonoidalCategory.snd I Z =
        (Limits.prod.snd : I ⨯ Z ⟶ Z) := by
      dsimp only [eTensor]
      exact IsLimit.conePointUniqueUpToIso_inv_comp
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct I Z)
        (limit.isLimit _) ⟨WalkingPair.right⟩
    apply CartesianMonoidalCategory.hom_ext
    · change nativeEndpoint e Z ≫
          (eTensor.inv ≫ CartesianMonoidalCategory.fst I Z) = _
      rw [hFst, Limits.prod.lift_fst,
        CartesianMonoidalCategory.lift_fst]
    · change nativeEndpoint e Z ≫
          (eTensor.inv ≫ CartesianMonoidalCategory.snd I Z) = _
      rw [hSnd, Limits.prod.lift_snd,
        CartesianMonoidalCategory.lift_snd]
  let insert (e : CGWH.point.{u, v} ⟶ I) :
      J.right ⟶ I ⊗ J.right :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from J.right ≫ e) (𝟙 J.right)
  let eA : I ⊗ A ≅ I ⨯ A :=
    (CartesianMonoidalCategory.tensorLeftIsoProd I).app A
  let eB : I ⊗ B ≅ I ⨯ B :=
    (CartesianMonoidalCategory.tensorLeftIsoProd I).app B
  have endpoint_assoc (e : CGWH.point.{u, v} ⟶ I) :
      nativeEndpoint e A ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd I).inv.app A ≫
          (α_ I J.right X.right).inv =
        insert e ⊗ₘ 𝟙 X.right := by
    change nativeEndpoint e A ≫ eA.inv ≫
      (α_ I J.right X.right).inv = _
    calc
      nativeEndpoint e A ≫ eA.inv ≫ (α_ I J.right X.right).inv =
          (nativeEndpoint e A ≫ eA.inv) ≫
            (α_ I J.right X.right).inv :=
        (Category.assoc _ _ _).symm
      _ = CartesianMonoidalCategory.lift
            (CGWH.point_isTerminal.from A ≫ e) (𝟙 A) ≫
          (α_ I J.right X.right).inv := by
        rw [show nativeEndpoint e A ≫ eA.inv =
          CartesianMonoidalCategory.lift
            (CGWH.point_isTerminal.from A ≫ e) (𝟙 A) from endpoint_tensor e A]
      _ = insert e ⊗ₘ 𝟙 X.right := by
        apply CartesianMonoidalCategory.hom_ext <;>
          dsimp only [insert, A] <;> cat_disch
  have hANative (e : CGWH.point.{u, v} ⟶ I) :
      nativeEndpoint e A ≫ kA_native =
        ((insert e ≫ contractJ) ⊗ₘ 𝟙 X.right) ≫ r := by
    dsimp only [kA_native, cA]
    change nativeEndpoint e A ≫ eA.inv ≫
      (α_ I J.right X.right).inv ≫
        (contractJ ⊗ₘ 𝟙 X.right) ≫ r = _
    have hAssoc := endpoint_assoc e
    change nativeEndpoint e A ≫ eA.inv ≫
      (α_ I J.right X.right).inv = _ at hAssoc
    slice_lhs 1 3 => rw [hAssoc]
    slice_lhs 1 2 =>
      rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  have hBNative (e : CGWH.point.{u, v} ⟶ I) :
      nativeEndpoint e B ≫ kB_native = b := by
    have ht : nativeEndpoint e B ≫ eB.inv ≫
          CGWH.point_isTerminal.from (I ⊗ B) = 𝟙 B :=
      CGWH.point_isTerminal.hom_ext _ _
    dsimp only [kB_native, cB]
    change nativeEndpoint e B ≫ eB.inv ≫
      CGWH.point_isTerminal.from (I ⊗ B) ≫ b = b
    slice_lhs 1 3 => rw [ht]
    rw [Category.id_comp]
  have hAOne : nativeEndpoint intervalEndpointOne A ≫ kA_native = r := by
    rw [hANative]
    rw [freeIntervalContraction.2.2.2]
    rw [MonoidalCategory.id_tensorHom,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have hBOne : nativeEndpoint intervalEndpointOne B ≫ kB_native = b :=
    hBNative intervalEndpointOne
  let pi := pointedCylinderProjection X
  let i0 := pointedCylinderI0 X
  let projBaseBranch : CGWH.point.{u, v} ⊗ X.right ⟶ X.right :=
    CGWH.point_isTerminal.from _ ≫ X.hom
  let projIntervalBranch : I ⊗ X.right ⟶ X.right :=
    CartesianMonoidalCategory.snd I X.right
  let projProd : J.right ⊗ X.right ⟶ X.right :=
    (rightDistrib X.right CGWH.point I).inv ≫
      coprod.desc projBaseBranch projIntervalBranch
  have hRProj : r ≫ pi.1.right = projProd := by
    change p.2.1.inl ≫
        PushoutCocone.IsColimit.desc p.2.2 projProd X.hom _ = projProd
    rw [PushoutCocone.IsColimit.inl_desc]
  let endpointZero : X.right ⟶ A :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from X.right ≫ intervalEndpointZero ≫
        coprod.inr) (𝟙 X.right)
  have hi0Right : i0.right = endpointZero ≫ r := by rfl
  have hi0Point : X.hom ≫ i0.right = b := by
    have h := Under.w i0
    change X.hom ≫ i0.right = b at h
    exact h
  have hRightR : rightFace ≫ r =
      CGWH.point_isTerminal.from X.right ≫ b := by
    calc
      rightFace ≫ r =
          (pushout.inr J.hom X.hom ≫ i) ≫ r := by rw [hpInr]
      _ = pushout.inr J.hom X.hom ≫ (i ≫ r) :=
        Category.assoc _ _ _
      _ = pushout.inr J.hom X.hom ≫ (fW ≫ b) := by rw [hCondition]
      _ = (pushout.inr J.hom X.hom ≫ fW) ≫ b :=
        (Category.assoc _ _ _).symm
      _ = CGWH.point_isTerminal.from X.right ≫ b := by
        simpa only using congrArg (fun k : X.right ⟶ B => k ≫ b)
          (CGWH.point_isTerminal.hom_ext _ _)
  let zeroJ : J.right ⟶ J.right :=
    coprod.desc coprod.inl
      (CGWH.point_isTerminal.from I ≫ intervalEndpointZero ≫ coprod.inr)
  have hZeroBase : (coprod.inl : CGWH.point.{u, v} ⟶ J.right) ≫ zeroJ =
      coprod.inl := by
    dsimp only [zeroJ]
    rw [CategoryTheory.Limits.coprod.inl_desc]
  have hZeroInterval : (coprod.inr : I ⟶ J.right) ≫ zeroJ =
      CGWH.point_isTerminal.from I ≫ intervalEndpointZero ≫ coprod.inr := by
    dsimp only [zeroJ]
    rw [CategoryTheory.Limits.coprod.inr_desc]
  let zeroInsert : I ⊗ X.right ⟶ A :=
    (CGWH.point_isTerminal.from I ≫ intervalEndpointZero ≫ coprod.inr) ⊗ₘ
      𝟙 X.right
  have hTensorBase : (coprod.inl ▷ X.right) ≫
        (zeroJ ⊗ₘ 𝟙 X.right) = coprod.inl ▷ X.right := by
    rw [MonoidalCategory.tensorHom_id,
      ← MonoidalCategory.comp_whiskerRight, hZeroBase]
  have hTensorInterval : (coprod.inr ▷ X.right) ≫
        (zeroJ ⊗ₘ 𝟙 X.right) = zeroInsert := by
    dsimp only [zeroInsert]
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_id,
      ← MonoidalCategory.comp_whiskerRight, hZeroInterval]
  let baseToX : CGWH.point.{u, v} ⊗ X.right ⟶ X.right :=
    CartesianMonoidalCategory.snd CGWH.point X.right
  have hBaseFactor : (coprod.inl ▷ X.right) = baseToX ≫ rightFace := by
    apply CartesianMonoidalCategory.hom_ext <;>
      dsimp only [baseToX, rightFace, J, freePointedInterval] <;> cat_disch
  have hBaseProj : (coprod.inl ▷ X.right) ≫ projProd = projBaseBranch := by
    dsimp only [projProd]
    rw [CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv_assoc,
      CategoryTheory.Limits.coprod.inl_desc]
  have hIntervalProj : (coprod.inr ▷ X.right) ≫ projProd =
      projIntervalBranch := by
    dsimp only [projProd]
    rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc,
      CategoryTheory.Limits.coprod.inr_desc]
  have hEndpointZeroFactor :
      CartesianMonoidalCategory.snd I X.right ≫ endpointZero =
        zeroInsert := by
    apply CartesianMonoidalCategory.hom_ext
    · dsimp only [endpointZero, zeroInsert, A]
      simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.tensorHom_fst]
      have ht : CartesianMonoidalCategory.snd I X.right ≫
            CGWH.point_isTerminal.from X.right =
          CartesianMonoidalCategory.fst I X.right ≫
            CGWH.point_isTerminal.from I :=
        CGWH.point_isTerminal.hom_ext _ _
      simpa only [Category.assoc] using congrArg
        (fun k : I ⊗ X.right ⟶ CGWH.point.{u, v} =>
          k ≫ intervalEndpointZero ≫ coprod.inr) ht
    · dsimp only [endpointZero, zeroInsert, A]
      simp only [Category.assoc, CartesianMonoidalCategory.lift_snd,
        CartesianMonoidalCategory.tensorHom_snd,
        Category.comp_id]
  have hSmashZero : (zeroJ ⊗ₘ 𝟙 X.right) ≫ r =
      r ≫ pi.1.right ≫ i0.right := by
    apply (cancel_epi (rightDistrib X.right CGWH.point I).hom).1
    apply coprod.hom_ext
    · simp only [← Category.assoc, coprod_inl_rightDistrib_hom]
      calc
        (coprod.inl ▷ X.right) ≫ (zeroJ ⊗ₘ 𝟙 X.right) ≫ r =
            (coprod.inl ▷ X.right) ≫ r := by
          rw [← Category.assoc, hTensorBase]
        _ = (baseToX ≫ rightFace) ≫ r := by rw [← hBaseFactor]
        _ = baseToX ≫ (rightFace ≫ r) := Category.assoc _ _ _
        _ = baseToX ≫ CGWH.point_isTerminal.from X.right ≫ b := by
          rw [hRightR]
        _ = CGWH.point_isTerminal.from
              (CGWH.point.{u, v} ⊗ X.right) ≫ b := by
          have ht : baseToX ≫ CGWH.point_isTerminal.from X.right =
              CGWH.point_isTerminal.from
                (CGWH.point.{u, v} ⊗ X.right) :=
            CGWH.point_isTerminal.hom_ext _ _
          simpa only [Category.assoc] using congrArg
            (fun k : CGWH.point.{u, v} ⊗ X.right ⟶ B => k ≫ b)
            ht
        _ = projBaseBranch ≫ i0.right := by
          dsimp only [projBaseBranch]
          rw [Category.assoc, hi0Point]
        _ = ((coprod.inl ▷ X.right) ≫ projProd) ≫ i0.right := by
          exact (congrArg (fun k => k ≫ i0.right) hBaseProj).symm.trans
            (Category.assoc _ _ _)
        _ = (coprod.inl ▷ X.right) ≫
              (r ≫ pi.1.right) ≫ i0.right := by
          rw [hRProj]
          exact Category.assoc _ _ _
    · simp only [← Category.assoc, coprod_inr_rightDistrib_hom]
      calc
        (coprod.inr ▷ X.right) ≫ (zeroJ ⊗ₘ 𝟙 X.right) ≫ r =
            zeroInsert ≫ r := by rw [← Category.assoc, hTensorInterval]
        _ = (CartesianMonoidalCategory.snd I X.right ≫ endpointZero) ≫ r := by
          rw [hEndpointZeroFactor]
        _ = CartesianMonoidalCategory.snd I X.right ≫
              (endpointZero ≫ r) := Category.assoc _ _ _
        _ = projIntervalBranch ≫ i0.right := by
          dsimp only [projIntervalBranch]
          rw [← hi0Right]
        _ = ((coprod.inr ▷ X.right) ≫ projProd) ≫ i0.right := by
          exact (congrArg (fun k => k ≫ i0.right) hIntervalProj).symm.trans
            (Category.assoc _ _ _)
        _ = (coprod.inr ▷ X.right) ≫
              (r ≫ pi.1.right) ≫ i0.right := by
          rw [hRProj]
          exact Category.assoc _ _ _
  have hAZero : nativeEndpoint intervalEndpointZero A ≫ kA_native =
      r ≫ pi.1.right ≫ i0.right := by
    rw [hANative]
    dsimp only [insert]
    rw [freeIntervalContraction.2.2.1]
    exact hSmashZero
  have hPiPoint : b ≫ pi.1.right = X.hom := by
    have h := Under.w pi.1
    change b ≫ pi.1.right = X.hom at h
    exact h
  have hBEndo : b ≫ pi.1.right ≫ i0.right = b := by
    rw [← Category.assoc, hPiPoint, hi0Point]
  have hBZero : nativeEndpoint intervalEndpointZero B ≫ kB_native =
      b ≫ pi.1.right ≫ i0.right :=
    (hBNative intervalEndpointZero).trans hBEndo.symm
  have endpoint_raw (e : CGWH.point.{u, v} ⟶ I)
      (endo : P.right ⟶ P.right)
      (hA : nativeEndpoint e A ≫ kA_native = r ≫ endo)
      (hB : nativeEndpoint e B ≫ kB_native = b ≫ endo) :
      rawIntervalEndpoint e (T.obj P.right) ≫ Kraw = T.map endo := by
    apply (cancel_epi eP.hom).1
    apply (IsPushout.of_hasPushout (T.map i) (T.map fW)).hom_ext
    · calc
        rawInl ≫ eP.hom ≫ rawIntervalEndpoint e (T.obj P.right) ≫ Kraw =
            rawInl ≫ eP.hom ≫ rawIntervalEndpoint e (T.obj P.right) ≫
              Limits.prod.map (𝟙 (T.obj I)) eP.inv ≫ d := by rfl
        _ = rawInl ≫ rawIntervalEndpoint e R ≫ d := by
          simpa only [Category.assoc] using
            congrArg (fun k => rawInl ≫ k ≫ d) (hApex e)
        _ = rawIntervalEndpoint e (T.obj A) ≫
              Limits.prod.map (𝟙 (T.obj I)) rawInl ≫ d := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ d) (hLegL e)
        _ = rawIntervalEndpoint e (T.obj A) ≫ kA_raw := by
          simpa only [Category.assoc] using congrArg
            (fun k => rawIntervalEndpoint e (T.obj A) ≫ k) hDInl
        _ = (rawIntervalEndpoint e (T.obj A) ≫ qA.inv) ≫ T.map kA_native :=
          (Category.assoc _ _ _).symm
        _ = T.map (nativeEndpoint e A) ≫ T.map kA_native := by rw [hQE]
        _ = T.map (nativeEndpoint e A ≫ kA_native) :=
          (T.map_comp _ _).symm
        _ = T.map (r ≫ endo) := by rw [hA]
        _ = T.map r ≫ T.map endo := T.map_comp _ _
        _ = rawInl ≫ eP.hom ≫ T.map endo := by
          rw [← hEPInl, Category.assoc]
    · calc
        rawInr ≫ eP.hom ≫ rawIntervalEndpoint e (T.obj P.right) ≫ Kraw =
            rawInr ≫ eP.hom ≫ rawIntervalEndpoint e (T.obj P.right) ≫
              Limits.prod.map (𝟙 (T.obj I)) eP.inv ≫ d := by rfl
        _ = rawInr ≫ rawIntervalEndpoint e R ≫ d := by
          simpa only [Category.assoc] using
            congrArg (fun k => rawInr ≫ k ≫ d) (hApex e)
        _ = rawIntervalEndpoint e (T.obj B) ≫
              Limits.prod.map (𝟙 (T.obj I)) rawInr ≫ d := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ d) (hLegR e)
        _ = rawIntervalEndpoint e (T.obj B) ≫ kB_raw := by
          simpa only [Category.assoc] using congrArg
            (fun k => rawIntervalEndpoint e (T.obj B) ≫ k) hDInr
        _ = (rawIntervalEndpoint e (T.obj B) ≫ qB.inv) ≫ T.map kB_native :=
          (Category.assoc _ _ _).symm
        _ = T.map (nativeEndpoint e B) ≫ T.map kB_native := by rw [hQE]
        _ = T.map (nativeEndpoint e B ≫ kB_native) :=
          (T.map_comp _ _).symm
        _ = T.map (b ≫ endo) := by rw [hB]
        _ = T.map b ≫ T.map endo := T.map_comp _ _
        _ = rawInr ≫ eP.hom ≫ T.map endo := by
          rw [← hEPInr, Category.assoc]
  refine ⟨Kraw, ?_, ?_⟩
  · exact endpoint_raw intervalEndpointZero
      (pi.1.right ≫ i0.right) hAZero hBZero
  · have hOne := endpoint_raw intervalEndpointOne (𝟙 P.right)
      (by simpa only [Category.comp_id] using hAOne)
      (by simpa only [Category.comp_id] using hBOne)
    simpa only [T.map_id] using hOne

/-- The ordinary continuous homotopy contracting the reduced cylinder onto
its zero section. -/
private noncomputable def pointedCylinderContraction
    (X : PointedCGWH.{u, v}) :
    ContinuousMap.Homotopy
      ((ConcreteCategory.hom (pointedCylinderI0 X).right :
          C(X.right, (pointedCylinderObj X).right)).comp
        (ConcreteCategory.hom (pointedCylinderProjection X).1.right :
          C((pointedCylinderObj X).right, X.right)))
      (ContinuousMap.id (pointedCylinderObj X).right) := by
  let I := cgwhInterval.{u, v}
  let T := CGWH.cgwhToTop.{u, v}
  let P := (pointedCylinderObj X).right
  let raw := pointedCylinderRawContraction X
  let rP := TopCat.prodIsoProd (T.obj I) (T.obj P)
  let up : C(unitInterval, ULift.{v} unitInterval) :=
    ⟨ULift.up, continuous_uliftUp⟩
  let upProdId : C(unitInterval × P, ULift.{v} unitInterval × P) :=
    ContinuousMap.prodMap up (ContinuousMap.id P)
  let Kpair : C(unitInterval × P, P) :=
    (ConcreteCategory.hom raw.1).comp
      ((ConcreteCategory.hom rP.inv).comp upProdId)
  refine
    { toContinuousMap := Kpair
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro x
    have hpt : rP.inv (ULift.up (0 : unitInterval), x) =
        rawIntervalEndpoint intervalEndpointZero (T.obj P) x := by
      apply Limits.Concrete.limit_ext
      rintro ⟨⟨⟩⟩
      · change (rP.inv ≫ Limits.prod.fst)
            (ULift.up (0 : unitInterval), x) =
          (rawIntervalEndpoint intervalEndpointZero (T.obj P) ≫
            Limits.prod.fst) x
        dsimp only [rawIntervalEndpoint]
        rw [TopCat.prodIsoProd_inv_fst, Limits.prod.lift_fst]
        rfl
      · change (rP.inv ≫ Limits.prod.snd)
            (ULift.up (0 : unitInterval), x) =
          (rawIntervalEndpoint intervalEndpointZero (T.obj P) ≫
            Limits.prod.snd) x
        dsimp only [rawIntervalEndpoint]
        rw [TopCat.prodIsoProd_inv_snd, Limits.prod.lift_snd]
        rfl
    have h0 := raw.2.1
    have hx := ConcreteCategory.congr_hom h0 x
    change raw.1 (rP.inv (ULift.up (0 : unitInterval), x)) = _
    rw [hpt]
    change raw.1 (rawIntervalEndpoint intervalEndpointZero (T.obj P) x) =
      (T.map ((pointedCylinderProjection X).1.right ≫
        (pointedCylinderI0 X).right)) x
    exact hx
  · intro x
    have hpt : rP.inv (ULift.up (1 : unitInterval), x) =
        rawIntervalEndpoint intervalEndpointOne (T.obj P) x := by
      apply Limits.Concrete.limit_ext
      rintro ⟨⟨⟩⟩
      · change (rP.inv ≫ Limits.prod.fst)
            (ULift.up (1 : unitInterval), x) =
          (rawIntervalEndpoint intervalEndpointOne (T.obj P) ≫
            Limits.prod.fst) x
        dsimp only [rawIntervalEndpoint]
        rw [TopCat.prodIsoProd_inv_fst, Limits.prod.lift_fst]
        rfl
      · change (rP.inv ≫ Limits.prod.snd)
            (ULift.up (1 : unitInterval), x) =
          (rawIntervalEndpoint intervalEndpointOne (T.obj P) ≫
            Limits.prod.snd) x
        dsimp only [rawIntervalEndpoint]
        rw [TopCat.prodIsoProd_inv_snd, Limits.prod.lift_snd]
        rfl
    have h1 := raw.2.2
    have hx := ConcreteCategory.congr_hom h1 x
    change raw.1 (rP.inv (ULift.up (1 : unitInterval), x)) = x
    rw [hpt]
    exact hx

/-- The cylinder projection is a homotopy equivalence, with inverse its zero
section. -/
private noncomputable def pointedCylinderProjectionHomotopyEquiv
    (X : PointedCGWH.{u, v}) :
    ContinuousMap.HomotopyEquiv (pointedCylinderObj X).right X.right where
  toFun := ConcreteCategory.hom (pointedCylinderProjection X).1.right
  invFun := ConcreteCategory.hom (pointedCylinderI0 X).right
  left_inv := ⟨pointedCylinderContraction X⟩
  right_inv := by
    have hRight : (pointedCylinderI0 X).right ≫
          (pointedCylinderProjection X).1.right = 𝟙 X.right :=
      congrArg (fun k : X ⟶ X => k.right)
        (pointedCylinderProjection X).2.1
    have hComp :
        (ConcreteCategory.hom (pointedCylinderProjection X).1.right :
          C((pointedCylinderObj X).right, X.right)).comp
            (ConcreteCategory.hom (pointedCylinderI0 X).right :
              C(X.right, (pointedCylinderObj X).right)) =
          ContinuousMap.id X.right := by
      apply ContinuousMap.ext
      intro x
      have hx := ConcreteCategory.congr_hom hRight x
      simpa using hx
    rw [hComp]

/-- The reduced-cylinder projection is a selected pointed CGWH weak
equivalence. -/
private theorem pointedCylinderProjection_weakEquivalence
    (X : PointedCGWH.{u, v}) :
    WeakEquivalence (pointedCylinderProjection X).1 := by
  apply (PointedCGWH.weakEquivalence_iff _).2
  apply (HomotopicalAlgebra.weakEquivalence_iff _).2
  change TopCat.weakHomotopyEquivalences
    (CGWH.cgwhToTop.map (pointedCylinderProjection X).1.right)
  change TopCat.weakHomotopyEquivalences
    (TopCat.ofHom (pointedCylinderProjectionHomotopyEquiv X).toFun)
  exact TopCat.homotopyEquiv_toFun_mem
    (pointedCylinderProjectionHomotopyEquiv X)

/-- The reduced smash cylinder as a categorical cylinder in the selected
pointed CGWH model structure. -/
private noncomputable def pointedCylinder
    (X : PointedCGWH.{u, v}) : HomotopicalAlgebra.Cylinder X where
  I := pointedCylinderObj X
  i₀ := pointedCylinderI0 X
  i₁ := pointedCylinderI1 X
  π := (pointedCylinderProjection X).1
  i₀_π := (pointedCylinderProjection X).2.1
  i₁_π := (pointedCylinderProjection X).2.2
  weakEquivalence_π := pointedCylinderProjection_weakEquivalence X

/-- A homotopy stationary on the selected point is represented by the
reduced smash cylinder. -/
private noncomputable def homotopyRelLeftHomotopy
    {X Y : PointedCGWH.{u, v}} (f g : X ⟶ Y)
    (H : ContinuousMap.HomotopyRel
      (ConcreteCategory.hom f.right : C(X.right, Y.right))
      (ConcreteCategory.hom g.right : C(X.right, Y.right))
      (Set.range (ConcreteCategory.hom X.hom :
        C(CGWH.point.{u, v}, X.right)))) :
    (pointedCylinder X).LeftHomotopy f g where
  h := (homotopyRelCylinderMap f g H).1
  h₀ := (homotopyRelCylinderMap f g H).2.1
  h₁ := (homotopyRelCylinderMap f g H).2.2

/-- A continuous homotopy of pointed maps which is stationary at the source
point gives the categorical left-homotopy relation, without a cofibrancy
hypothesis on the source. -/
theorem leftHomotopyRel_of_homotopyRel
    {X Y : PointedCGWH.{u, v}} (f g : X ⟶ Y)
    (H : ContinuousMap.HomotopyRel
      (ConcreteCategory.hom f.right : C(X.right, Y.right))
      (ConcreteCategory.hom g.right : C(X.right, Y.right))
      (Set.range (ConcreteCategory.hom X.hom :
        C(CGWH.point.{u, v}, X.right)))) :
    HomotopicalAlgebra.LeftHomotopyRel f g :=
  (homotopyRelLeftHomotopy f g H).leftHomotopyRel

/-- Pointed maps joined by a continuous homotopy stationary at the source
point have equal images in the canonical pointed CGWH homotopy category. -/
theorem toHomotopyCategory_map_eq_of_homotopyRel
    {X Y : PointedCGWH.{u, v}} (f g : X ⟶ Y)
    (H : ContinuousMap.HomotopyRel
      (ConcreteCategory.hom f.right : C(X.right, Y.right))
      (ConcreteCategory.hom g.right : C(X.right, Y.right))
      (Set.range (ConcreteCategory.hom X.hom :
        C(CGWH.point.{u, v}, X.right)))) :
    PointedCGWH.toHomotopyCategory.map f =
      PointedCGWH.toHomotopyCategory.map g :=
  (HomotopicalAlgebra.LeftHomotopyRel.factorsThroughLocalization
    PointedCGWH (leftHomotopyRel_of_homotopyRel f g H)).map_eq
      PointedCGWH.toHomotopyCategory

end PointedCGWH
