/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderCofibration
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderLevelSDR
import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingInstances
import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances

/-!
# Closed original mapping-cylinder successors and actual telescope evaluation

The SAME original joint endpoint arrow is evaluated through its actual whole
scalar Arrow comparison. Its original finite boundary smashed with every
arbitrary level object is closed. The SAME original attachment pushout then
makes the original coproduct fold, source and target legs level closed, with
no source or target cofibrancy. Every original recursively built telescope
transition is closed, including every finite composite. The whole actual
level colimit comparison retains all original chosen objects, legs and maps.
Based HEP, homotopy-group colimits, FS identities and stable recognition are
separate obligations; no law for any of them is assumed here.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH

/-- Every original chosen point is a closed embedding in its native CGWH space. -/
private theorem pointMap_isClosedEmbedding (X : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom X.hom) := by
  let _ : Subsingleton CGWH.point.{u, v} := by
    change Subsingleton PUnit.{v + 1}
    infer_instance
  exact ⟨IsEmbedding.of_subsingleton _, (Set.finite_range _).isClosed⟩

/-- The actual initial pointed arrow retains the SAME original closed point map. -/
private theorem initialMap_isClosedEmbedding (X : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom (Under.mkIdInitial.to X).right) := by
  simpa only [Under.mkIdInitial_to_right] using pointMap_isClosedEmbedding X

/-- The actual pointed coproduct is the pushout of BOTH original chosen basepoint maps. -/
private theorem binaryCoproduct_isPushout (X Y : PointedCGWH.{u, v}) :
    IsPushout X.hom Y.hom (coprod.inl : X ⟶ X ⨿ Y).right
      (coprod.inr : Y ⟶ X ⨿ Y).right := by
  have h : IsPushout (Under.mkIdInitial.to X) (Under.mkIdInitial.to Y)
      (coprod.inl : X ⟶ X ⨿ Y) (coprod.inr : Y ⟶ X ⨿ Y) :=
    IsPushout.of_is_coproduct (coprodIsCoprod X Y) Under.mkIdInitial
  have hm := h.map pointedToCGWH
  change IsPushout (Under.mkIdInitial.to X).right (Under.mkIdInitial.to Y).right
    (coprod.inl : X ⟶ X ⨿ Y).right (coprod.inr : Y ⟶ X ⨿ Y).right at hm
  simpa only [Under.mkIdInitial_to_right] using hm

/-- The original first pointed coprojection is closed for arbitrary pointed objects. -/
private theorem coprod_inl_isClosedEmbedding (X Y : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom (coprod.inl : X ⟶ X ⨿ Y).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  have h : IsPushout (Under.mkIdInitial.to X) (Under.mkIdInitial.to Y)
      (coprod.inl : X ⟶ X ⨿ Y) (coprod.inr : Y ⟶ X ⨿ Y) :=
    IsPushout.of_is_coproduct (coprodIsCoprod X Y) Under.mkIdInitial
  exact MorphismProperty.of_isPushout h (show P (Under.mkIdInitial.to Y) from
    initialMap_isClosedEmbedding Y)

/-- The original second pointed coprojection is closed for arbitrary pointed objects. -/
private theorem coprod_inr_isClosedEmbedding (X Y : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom (coprod.inr : Y ⟶ X ⨿ Y).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  have h : IsPushout (Under.mkIdInitial.to X) (Under.mkIdInitial.to Y)
      (coprod.inl : X ⟶ X ⨿ Y) (coprod.inr : Y ⟶ X ⨿ Y) :=
    IsPushout.of_is_coproduct (coprodIsCoprod X Y) Under.mkIdInitial
  exact MorphismProperty.of_isPushout h.flip (show P (Under.mkIdInitial.to X) from
    initialMap_isClosedEmbedding X)

end PointedCGWH

namespace PointedCGWH.EnrichedIntervalMappingCylinderClosed
open PointedCGWH.EnrichedFunctorMapping PointedCGWH.EnrichedIntervalCylinderModel
open PointedCGWH.EnrichedIntervalMappingCylinder
open PointedCGWH.EnrichedIntervalMappingCylinderModel
attribute [local instance] MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The evaluated SAME original scalar functor has every original right-tensor map. -/
theorem scalarEvaluationMap (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I)
    {M N : PointedCGWH.{u, v}} (h : M ⟶ N) :
    (evaluation (V := PointedCGWH.{u, v}) a).map
      ((WeightedEndVariance.tensorBifunctor.flip.obj X).map h) =
      h ▷ X.toEnrichedFunctor.obj a := scalarTensorMap_component h X a

/-- The ENTIRE original scalar/evaluation functor is the actual fixed-level smash functor. -/
def scalarEvaluationIso (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    WeightedEndVariance.tensorBifunctor.flip.obj X ⋙ evaluation a ≅
      tensorRight (X.toEnrichedFunctor.obj a) :=
  NatIso.ofComponents (fun M => Iso.refl (M ⊗ X.toEnrichedFunctor.obj a)) (by
    intro M N h
    change (evaluation a).map ((WeightedEndVariance.tensorBifunctor.flip.obj X).map h) ≫ 𝟙 _ =
      𝟙 _ ≫ h ▷ X.toEnrichedFunctor.obj a
    rw [Category.comp_id, Category.id_comp, scalarEvaluationMap])

/-- Every complete original scalar/evaluation comparison is the SAME identity level Iso. -/
theorem scalarEvaluationIso_app (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (a : I) (M : PointedCGWH.{u, v}) :
    (scalarEvaluationIso X a).app M = Iso.refl (M ⊗ X.toEnrichedFunctor.obj a) := rfl

/-- The actual level coproduct comparison retains BOTH original chosen coproducts. -/
def evaluationCoprodIso (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    (X ⨿ Y).toEnrichedFunctor.obj a ≅
      X.toEnrichedFunctor.obj a ⨿ Y.toEnrichedFunctor.obj a :=
  (PreservesColimitPair.iso (evaluation a) X Y).symm

/-- The complete first coprojection of the inverse comparison is the original evaluated leg. -/
@[reassoc]
theorem evaluationCoprodIso_inl_inv (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (a : I) :
    coprod.inl ≫ (evaluationCoprodIso X Y a).inv =
      component (coprod.inl : X ⟶ X ⨿ Y) a := by
  change coprod.inl ≫ coprodComparison (evaluation a) X Y = _
  exact coprod.inl_desc _ _

/-- The complete second coprojection of the inverse comparison is the original evaluated leg. -/
@[reassoc]
theorem evaluationCoprodIso_inr_inv (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (a : I) :
    coprod.inr ≫ (evaluationCoprodIso X Y a).inv =
      component (coprod.inr : Y ⟶ X ⨿ Y) a := by
  change coprod.inr ≫ coprodComparison (evaluation a) X Y = _
  exact coprod.inr_desc _ _

/-- The forward comparison sends the SAME complete first evaluated leg to the original leg. -/
@[reassoc]
theorem evaluationCoprodIso_inl_hom (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (a : I) :
    component (coprod.inl : X ⟶ X ⨿ Y) a ≫ (evaluationCoprodIso X Y a).hom =
      coprod.inl := by
  rw [← evaluationCoprodIso_inl_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The forward comparison sends the SAME complete second evaluated leg to the original leg. -/
@[reassoc]
theorem evaluationCoprodIso_inr_hom (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (a : I) :
    component (coprod.inr : Y ⟶ X ⨿ Y) a ≫ (evaluationCoprodIso X Y a).hom =
      coprod.inr := by
  rw [← evaluationCoprodIso_inr_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The whole evaluated original joint Arrow is its SAME original coefficient smashed with level. -/
def jointMapComponentArrowIso (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    Arrow.mk (component (jointMap X) a) ≅
      Arrow.mk (IntervalCoefficient.jointEndpoints ▷ X.toEnrichedFunctor.obj a) := by
  let e : Arrow.mk (component (jointMap X) a) ≅
      Arrow.mk ((evaluation a).map ((WeightedEndVariance.tensorBifunctor.flip.obj X).map
        IntervalCoefficient.jointEndpoints)) :=
    (evaluation a).mapArrow.mapIso (jointMapArrowIso X)
  refine e ≪≫ Arrow.isoMk' _ _
    ((scalarEvaluationIso X a).app _) ((scalarEvaluationIso X a).app _) ?_
  exact ((scalarEvaluationIso X a).hom.naturality IntervalCoefficient.jointEndpoints).symm

/-- Every SAME original joint inclusion is closed at every arbitrary level, with no Cof premise. -/
theorem jointMap_component_isClosedEmbedding
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component (jointMap X) a).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  let _ : Cofibration IntervalCoefficient.jointEndpoints.{u, v} :=
    IntervalCoefficient.jointEndpoints_cofibration
  have h : P (IntervalCoefficient.jointEndpoints ▷ X.toEnrichedFunctor.obj a) :=
    modelCofibration_whiskerRight_isClosedEmbedding IntervalCoefficient.jointEndpoints _
  exact (P.arrow_mk_iso_iff (jointMapComponentArrowIso X a)).mpr h

/-- The original first diagram coprojection is closed at each SAME actual level. -/
theorem coprod_inl_component_isClosedEmbedding
    (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component (coprod.inl : X ⟶ X ⨿ Y) a).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  have h : P (component (coprod.inl : X ⟶ X ⨿ Y) a ≫
      (evaluationCoprodIso X Y a).hom) := by
    rw [evaluationCoprodIso_inl_hom]
    exact coprod_inl_isClosedEmbedding _ _
  exact (P.cancel_right_of_respectsIso _ _).mp h

/-- The original second diagram coprojection is closed at each SAME actual level. -/
theorem coprod_inr_component_isClosedEmbedding
    (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component (coprod.inr : Y ⟶ X ⨿ Y) a).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  have h : P (component (coprod.inr : Y ⟶ X ⨿ Y) a ≫
      (evaluationCoprodIso X Y a).hom) := by
    rw [evaluationCoprodIso_inr_hom]
    exact coprod_inr_isClosedEmbedding _ _
  exact (P.cancel_right_of_respectsIso _ _).mp h

/-- Evaluation preserves the SAME entire original attachment square, including all FOUR maps. -/
theorem attachmentComponent_isPushout
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    IsPushout (component (jointMap f.left) a) (component (attachmentMap f) a)
      (component (intervalLeg f) a) (component (foldMap f) a) :=
  (attachment_isPushout f).map (evaluation a)

/-- The SAME whole original fold is level closed for arbitrary original source and target. -/
theorem foldMap_component_isClosedEmbedding
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component (foldMap f) a).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  exact MorphismProperty.of_isPushout (attachmentComponent_isPushout f a).flip
    (show P (component (jointMap f.left) a) from jointMap_component_isClosedEmbedding f.left a)

/-- The SAME original source factor is closed at every level, with no source/target Cof premise. -/
theorem source_component_isClosedEmbedding
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component (source f) a).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  have h : P (component (coprod.inl : f.left ⟶ f.left ⨿ f.right) a ≫
      component (foldMap f) a) :=
    P.comp_mem _ _ (coprod_inl_component_isClosedEmbedding _ _ a)
      (foldMap_component_isClosedEmbedding f a)
  rw [← component_comp, foldMap, coprod.inl_desc] at h
  exact h

/-- The SAME original target leg is closed at every level, for arbitrary original endpoints. -/
theorem targetLeg_component_isClosedEmbedding
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component (targetLeg f) a).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  have h : P (component (coprod.inr : f.right ⟶ f.left ⨿ f.right) a ≫
      component (foldMap f) a) :=
    P.comp_mem _ _ (coprod_inr_component_isClosedEmbedding _ _ a)
      (foldMap_component_isClosedEmbedding f a)
  rw [← component_comp, foldMap, coprod.inr_desc] at h
  exact h

end PointedCGWH.EnrichedIntervalMappingCylinderClosed

namespace PointedCGWH.SequentialSpectrum.MappingTelescope

private theorem pointedNatColimits : HasColimitsOfShape ℕ PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  infer_instance

attribute [local instance] pointedNatColimits

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

omit B in
/-- Every original next transition component is the SAME original mapping-cylinder source. -/
theorem nextTransition_app {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (nextTransition d).app X = PointedCGWH.EnrichedIntervalMappingCylinder.source
      (stageArrows d |>.obj X) :=
  by
    change 𝟙 _ ≫ PointedCGWH.EnrichedIntervalMappingCylinder.source
      (stageArrows d |>.obj X) = _
    exact Category.id_comp _

omit B in
/-- ALL original next transitions are level closed, retaining the original projection and unit. -/
theorem nextTransition_level_isClosedEmbedding {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    IsClosedEmbedding (ConcreteCategory.hom
      (PointedCGWH.SequentialSpectrum.levelMap ((nextTransition d).app X) m).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  let E := PointedCGWH.SequentialSpectrum.evaluation.{u, v} m
  have h : (P.inverseImage E) (PointedCGWH.EnrichedIntervalMappingCylinder.source
      (stageArrows d |>.obj X)) :=
    EnrichedIntervalMappingCylinderClosed.source_component_isClosedEmbedding _
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)
  exact (congrArg
    (fun g : d.functor.obj X ⟶ (nextStage d).functor.obj X => (P.inverseImage E) g)
    (nextTransition_app d X)).mpr h

omit B in
/-- EVERY original recursive successor transition is level closed on every original spectrum. -/
theorem transition_level_isClosedEmbedding (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    IsClosedEmbedding (ConcreteCategory.hom
      (PointedCGWH.SequentialSpectrum.levelMap ((transition n).app X) m).right) :=
  nextTransition_level_isClosedEmbedding (stage n) X m

omit B in
/-- Each entire original next-stage target section is closed at every actual original level. -/
theorem nextStageSection_level_isClosedEmbedding {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    IsClosedEmbedding (ConcreteCategory.hom
      (PointedCGWH.SequentialSpectrum.levelMap ((nextStageSection d).app X) m).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  let E := PointedCGWH.SequentialSpectrum.evaluation.{u, v} m
  have h : (P.inverseImage E) (PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg
      (stageArrows d |>.obj X)) :=
    EnrichedIntervalMappingCylinderClosed.targetLeg_component_isClosedEmbedding _
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)
  exact (congrArg
    (fun g : (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)).obj X ⟶
      (nextStage d).functor.obj X => (P.inverseImage E) g)
    (nextStageSection_app d X)).mpr h

omit B in
/-- ALL original recursive target sections are closed on every original level and input. -/
theorem stageSection_level_isClosedEmbedding (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    IsClosedEmbedding (ConcreteCategory.hom
      (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m).right) :=
  nextStageSection_level_isClosedEmbedding (stage n) X m

/-- The actual level diagram is evaluation of the SAME entire original chosen stage diagram. -/
def levelDiagram (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    ℕ ⥤ PointedCGWH.{u, v} := diagram X ⋙ PointedCGWH.SequentialSpectrum.evaluation m

omit B in
/-- Every original stage and level is retained by the complete evaluated diagram. -/
theorem levelDiagram_obj (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ) :
    (levelDiagram X m).obj n =
      PointedCGWH.SequentialSpectrum.level ((stage n).functor.obj X) m := rfl

omit B in
/-- Every entire original successor level map is retained by the actual evaluated diagram. -/
theorem levelDiagram_map_succ (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ) :
    (levelDiagram X m).map (homOfLE (Nat.le_succ n)) =
      PointedCGWH.SequentialSpectrum.levelMap ((transition n).app X) m := by
  change component ((diagram X).map (homOfLE (Nat.le_succ n))) ⟨m⟩ = _
  rw [diagram_map_succ]
  rfl

omit B in
/-- EVERY arbitrary original finite telescope transition is closed at EVERY actual level. -/
theorem levelDiagram_map_isClosedEmbedding (X : PointedCGWH.SequentialSpectrum.{u, v})
    (m : ℕ) {i j : ℕ} (φ : i ⟶ j) :
    IsClosedEmbedding (ConcreteCategory.hom ((levelDiagram X m).map φ).right) := by
  let P : MorphismProperty PointedCGWH.{u, v} :=
    TopCat.closedEmbeddings.inverseImage (pointedToCGWH ⋙ CGWH.cgwhToTop)
  let F := levelDiagram X m
  have hStep (n : ℕ) : P (F.map (homOfLE (Nat.le_succ n))) := by
    rw [show F = levelDiagram X m from rfl, levelDiagram_map_succ]
    exact transition_level_isClosedEmbedding n X m
  have hMaps (j : ℕ) (hij : i ≤ j) : P (F.map (homOfLE hij)) := by
    induction j, hij using Nat.le_induction with
    | base => simpa only [homOfLE_refl, F.map_id] using P.id_mem (F.obj i)
    | succ j hij ih =>
        rw [← homOfLE_comp hij (Nat.le_succ j), F.map_comp]
        exact P.comp_mem _ _ ih (hStep j)
  change P (F.map φ)
  rw [← homOfLE_leOfHom φ]
  exact hMaps j (leOfHom φ)

/-- The SAME original chosen telescope level is the actual chosen evaluated colimit. -/
def telescopeLevelIso (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    PointedCGWH.SequentialSpectrum.level (telescope X) m ≅ colimit (levelDiagram X m) :=
  preservesColimitIso (PointedCGWH.SequentialSpectrum.evaluation m) (diagram X)

omit B in
/-- Every original stage leg retains its exact entire evaluated colimit equation. -/
@[reassoc]
theorem telescopeLevelIso_leg_hom (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap (leg X n) m ≫ (telescopeLevelIso X m).hom =
      colimit.ι (levelDiagram X m) n :=
  ι_preservesColimitIso_hom (PointedCGWH.SequentialSpectrum.evaluation m) (diagram X) n

omit B in
/-- Every original evaluated colimit leg retains the exact inverse chosen comparison. -/
@[reassoc]
theorem telescopeLevelIso_leg_inv (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ) :
    colimit.ι (levelDiagram X m) n ≫ (telescopeLevelIso X m).inv =
      PointedCGWH.SequentialSpectrum.levelMap (leg X n) m :=
  ι_preservesColimitIso_inv (PointedCGWH.SequentialSpectrum.evaluation m) (diagram X) n

/-- The ENTIRE original telescope/evaluation functor has the actual chosen-colimit NatIso. -/
def telescopeEvaluationIso (m : ℕ) :
    telescopeFunctor.{u, v} ⋙ PointedCGWH.SequentialSpectrum.evaluation m ≅
      diagramFunctor ⋙
        (Functor.whiskeringRight ℕ PointedCGWH.SequentialSpectrum.{u, v}
          PointedCGWH.{u, v}).obj (PointedCGWH.SequentialSpectrum.evaluation m) ⋙ colim :=
  Functor.associator diagramFunctor colim (PointedCGWH.SequentialSpectrum.evaluation m) ≪≫
    Functor.isoWhiskerLeft diagramFunctor
      (preservesColimitNatIso (PointedCGWH.SequentialSpectrum.evaluation m)) ≪≫
      (Functor.associator diagramFunctor _ colim).symm

omit B in
/-- Every original whole comparison component is the SAME actual chosen level-colimit Iso. -/
theorem telescopeEvaluationIso_app (m : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeEvaluationIso m).app X = telescopeLevelIso X m := by
  apply Iso.ext
  change (𝟙 _ ≫ (telescopeLevelIso X m).hom) ≫ 𝟙 _ = (telescopeLevelIso X m).hom
  rw [Category.id_comp, Category.comp_id]

omit B in
/-- All original spectrum maps retain the complete evaluated chosen-colimit naturality square. -/
theorem telescopeLevelIso_naturality (m : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m ≫
        (telescopeLevelIso Y m).hom =
      (telescopeLevelIso X m).hom ≫ colim.map
        (Functor.whiskerRight (diagramMap f) (PointedCGWH.SequentialSpectrum.evaluation m)) := by
  exact (preservesColimitNatIso (PointedCGWH.SequentialSpectrum.evaluation m)).hom.naturality
    (diagramMap f)

end PointedCGWH.SequentialSpectrum.MappingTelescope
