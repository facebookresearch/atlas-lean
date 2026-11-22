/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IntervalContraction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinder
import MathlibExt.CategoryTheory.Enriched.ScalarLeibniz
import MathlibExt.CategoryTheory.NatTrans.PointwiseArrow
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope

/-!
# Explicit native deformation of the SAME original mapping cylinders and telescope stages

The actual original scalar time functor preserves colimits by its original
scalar/cotensor adjunction. The original mapping-cylinder pushout therefore
descends the computed original scalar contraction and the constant original
target action. All whole legs, zero/one/fixed equations, full Arrow input
maps and native natural transformations are retained. The same constructed
deformation and target section are applied to the SAME original recursive
mapping-telescope stages and projections. Ordinary homotopy/weak-equivalence
landing, based HEP, groups and stable recognition remain separate proofs.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.EnrichedIntervalContraction
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F G : C ⥤ D}

/--
The complete right-source section uses the SAME original whole Arrow functor and its exact
right functor equality.
-/
private def rightSectionImage (a : F ⟶ G) {H : Arrow D ⥤ D} (s : Arrow.rightFunc ⟶ H) :
    G ⟶ NatTrans.arrow a ⋙ H :=
  eqToHom (show NatTrans.arrow a ⋙ Arrow.rightFunc = G from rfl).symm ≫
    CategoryTheory.Functor.whiskerLeft (NatTrans.arrow a) s

/-- Every right-section component is the full original section of the same complete caller Arrow. -/
private theorem rightSectionImage_app (a : F ⟶ G) {H : Arrow D ⥤ D}
    (s : Arrow.rightFunc ⟶ H) (X : C) :
    (rightSectionImage a s).app X = s.app (Arrow.mk (a.app X)) := by
  change 𝟙 (G.obj X) ≫ s.app (Arrow.mk (a.app X)) = _
  exact Category.id_comp _

end PointedCGWH.SequentialSpectrum.MappingTelescope

namespace PointedCGWH.EnrichedIntervalMappingCylinderDeformation
open PointedCGWH.EnrichedIntervalMappingCylinder
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The entire actual time-functor object is the SAME original native scalar time object. -/
private theorem timeFunctor_original_obj (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeFunctor.obj X = timeObject X := rfl

/-- Every original whole time-functor map is the SAME complete native scalar map. -/
private theorem timeFunctor_original_map
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    timeFunctor.map f = tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} f := rfl

/--
BOTH complete actual time object and all-map functions retain the entire original scalar data.
-/
private theorem timeFunctor_original_fields :
    (fun X : EnrichedFunctorCat PointedCGWH.{u, v} I => timeFunctor.obj X) =
      (fun X => timeObject X) ∧
    HEq (fun (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (f : X ⟶ Y) => timeFunctor.map f)
      (fun (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (f : X ⟶ Y) =>
        tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} f) := ⟨rfl, HEq.rfl⟩

/-- The actual native time maps preserve the SAME whole original morphism composition. -/
private theorem timeMap_comp {X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} (f ≫ g) =
      tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} f ≫
        tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} g := by
  simpa only [timeFunctor_original_map, timeFunctor_original_obj] using
    (timeFunctor (I := I)).map_comp f g

/--
The SAME actual scalar time functor preserves native colimits by the original scalar/cotensor
adjunction.
-/
private theorem timePreservesColimits : PreservesColimits (timeFunctor (I := I)) :=
  (CategoryTheory.EnrichedFunctorCat.ScalarLeibniz.adjunction
    PointedCGWH.RealizedIntervalContraction.time.{u, v}).leftAdjoint_preservesColimits

attribute [local instance] timePreservesColimits
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

omit B in
/--
The full original interval and target legs retain the original first-endpoint pushout
equation.
-/
theorem attachment_condition (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    PointedCGWH.EnrichedIntervalCylinder.inclusion 0 f.left ≫ intervalLeg f =
      f.hom ≫ targetLeg f := pushout.condition

omit B in
/--
The SAME complete mapping-cylinder pushout remains a pushout under the actual full time
functor.
-/
theorem timePushout (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsPushout
      (tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v}
        (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 f.left))
      (tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} f.hom) (tensorLeftMap
        PointedCGWH.RealizedIntervalContraction.time.{u, v} (intervalLeg f))
      (tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} (targetLeg f)) := by
  simpa only [timeFunctor_original_map, timeFunctor_original_obj] using
    (IsPushout.of_hasPushout (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 f.left) f.hom).map
      (timeFunctor (I := I))

/--
The actual native mapping-cylinder deformation is the unique SAME time-pushout descent of
original scalar contraction and target constancy.
-/
def homotopy (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    timeObject (object f) ⟶ object f :=
  (timePushout f).desc (action f.left ≫ intervalLeg f)
    (timeProjection f.right ≫ targetLeg f) (by
      rw [← Category.assoc, action_fixed, Category.assoc, attachment_condition,
        ← Category.assoc, ← timeProjection_naturality, Category.assoc])

omit B in
/--
The full interval leg of the actual time-pushout descent is the SAME original scalar
contraction followed by its original leg.
-/
@[reassoc]
theorem timeIntervalLeg_homotopy (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} (intervalLeg f) ≫ homotopy
      f = action f.left ≫ intervalLeg f :=
  (timePushout f).inl_desc _ _ _

omit B in
/-- The full original target section is fixed throughout the entire actual native time action. -/
@[reassoc]
theorem timeTargetLeg_homotopy (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} (targetLeg f) ≫ homotopy f
      = timeProjection f.right ≫ targetLeg f :=
  (timePushout f).inr_desc _ _ _

omit B in
/--
At literal time zero the ENTIRE original native mapping cylinder is fixed by the actual
deformation.
-/
theorem homotopy_zero (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    timeInclusion 0 (object f) ≫ homotopy f = 𝟙 (object f) := by
  apply pushout.hom_ext
  · rw [← timeInclusion_naturality_assoc, timeIntervalLeg_homotopy,
      ← Category.assoc, action_zero, Category.id_comp, Category.comp_id]
  · rw [← timeInclusion_naturality_assoc, timeTargetLeg_homotopy,
      ← Category.assoc, timeInclusion_projection, Category.id_comp, Category.comp_id]

omit B in
/--
At literal time one the actual full deformation is the SAME original retraction followed by
its SAME original target section.
-/
theorem homotopy_one (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    timeInclusion 1 (object f) ≫ homotopy f = retraction f ≫ targetLeg f := by
  apply pushout.hom_ext
  · rw [← timeInclusion_naturality_assoc, timeIntervalLeg_homotopy,
      ← Category.assoc, action_one, Category.assoc, attachment_condition,
      intervalLeg_retraction_assoc]
  · rw [← timeInclusion_naturality_assoc, timeTargetLeg_homotopy,
      ← Category.assoc, timeInclusion_projection, Category.id_comp,
      targetLeg_retraction_assoc]

/--
All original target sections form a full natural transformation on the SAME entire Arrow
functor.
-/
def targetSectionNatTrans : Arrow.rightFunc ⟶ PointedCGWH.EnrichedIntervalMappingCylinder.functor
    (I := I) where
  app f := targetLeg f
  naturality _ _ h := (targetLeg_map h).symm

omit B in
/--
The SAME original target sections retract as an equality of whole original Arrow natural
transformations.
-/
theorem targetSection_retraction_natTrans :
    targetSectionNatTrans (I := I) ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.retractionNatTrans = 𝟙 Arrow.rightFunc := by
  apply NatTrans.ext
  funext f
  exact targetLeg_retraction f

omit B in
/--
The entire actual deformation is natural in EVERY full original left/right Arrow map and its
original commutative square.
-/
@[reassoc]
theorem homotopy_naturality
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (h : f ⟶ g) :
    tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v}
      (PointedCGWH.EnrichedIntervalMappingCylinder.map h) ≫ homotopy g =
      homotopy f ≫ PointedCGWH.EnrichedIntervalMappingCylinder.map h := by
  apply (timePushout f).hom_ext
  · rw [← Category.assoc, ← timeMap_comp, intervalLeg_map,
      timeMap_comp, Category.assoc, timeIntervalLeg_homotopy,
      ← Category.assoc, action_naturality, Category.assoc, ← intervalLeg_map,
      ← Category.assoc, timeIntervalLeg_homotopy_assoc]
    exact Category.assoc _ _ _
  · rw [← Category.assoc, ← timeMap_comp, targetLeg_map,
      timeMap_comp, Category.assoc, timeTargetLeg_homotopy,
      ← Category.assoc, timeProjection_naturality, Category.assoc, ← targetLeg_map,
      ← Category.assoc, timeTargetLeg_homotopy_assoc]
    exact Category.assoc _ _ _

/--
The actual original native mapping-cylinder deformation is a complete Arrow natural
transformation, with every original input map.
-/
def homotopyNatTrans : PointedCGWH.EnrichedIntervalMappingCylinder.functor (I := I) ⋙
    timeFunctor ⟶ PointedCGWH.EnrichedIntervalMappingCylinder.functor where
  app f := homotopy f
  naturality _ _ h := homotopy_naturality h

end PointedCGWH.EnrichedIntervalMappingCylinderDeformation

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/--
The whole next-stage deformation is the SAME actual original mapping-cylinder deformation on
its entire original stage Arrow functor.
-/
def nextStageDeformation {n : ℕ} (d : Stage.{u, v} n) :
    (nextStage d).functor ⋙ timeFunctor ⟶ (nextStage d).functor :=
  CategoryTheory.Functor.whiskerLeft (stageArrows d)
    PointedCGWH.EnrichedIntervalMappingCylinderDeformation.homotopyNatTrans

/--
The whole next-stage section uses its SAME original target iterate and complete original stage
Arrow functor.
-/
def nextStageSection {n : ℕ} (d : Stage.{u, v} n) :
    PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1) ⟶ (nextStage d).functor :=
  rightSectionImage (d.projection ≫ PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n)
    PointedCGWH.EnrichedIntervalMappingCylinderDeformation.targetSectionNatTrans

omit B in
/--
Every complete stage deformation component is the SAME original mapping-cylinder deformation
on its exact original projection/unit Arrow.
-/
theorem nextStageDeformation_app {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (nextStageDeformation d).app X =
      PointedCGWH.EnrichedIntervalMappingCylinderDeformation.homotopy
        (Arrow.mk ((d.projection ≫ PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app X))
          := rfl

omit B in
/--
Every complete stage section is the SAME original target leg of the exact original stage
projection/unit Arrow.
-/
theorem nextStageSection_app {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (nextStageSection d).app X = PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg
      (Arrow.mk ((d.projection ≫ PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app X))
    :=
  rightSectionImage_app _ _ X

omit B in
/--
The whole original next-stage projection component is the SAME original mapping-cylinder
retraction.
-/
theorem nextStageProjection_app {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (nextStage d).projection.app X = PointedCGWH.EnrichedIntervalMappingCylinder.retraction
      (Arrow.mk ((d.projection ≫ PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app X))
    :=
  by
    change PointedCGWH.EnrichedIntervalMappingCylinder.retraction
      (Arrow.mk ((d.projection ≫ PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app X)) ≫
        𝟙 _ = _
    exact Category.comp_id _

omit B in
/--
The entire original next-stage target section retracts through the SAME original full
projection natural transformation.
-/
theorem nextStageSection_projection {n : ℕ} (d : Stage.{u, v} n) :
    nextStageSection d ≫ (nextStage d).projection =
      𝟙 (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)) := by
  apply NatTrans.ext
  funext X
  rw [NatTrans.comp_app, nextStageSection_app, nextStageProjection_app]
  exact PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg_retraction _

omit B in
/--
Time zero of every original full next-stage deformation is the SAME original next-stage
identity.
-/
theorem nextStageDeformation_zero {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    timeInclusion 0 ((nextStage d).functor.obj X) ≫ (nextStageDeformation d).app X = 𝟙 _ := by
  rw [nextStageDeformation_app]
  exact PointedCGWH.EnrichedIntervalMappingCylinderDeformation.homotopy_zero _

omit B in
/--
Time one of every original next-stage deformation is its SAME original projection followed by
its SAME original target section.
-/
theorem nextStageDeformation_one {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    timeInclusion 1 ((nextStage d).functor.obj X) ≫ (nextStageDeformation d).app X =
      (nextStage d).projection.app X ≫ (nextStageSection d).app X := by
  rw [nextStageDeformation_app, nextStageProjection_app, nextStageSection_app]
  exact PointedCGWH.EnrichedIntervalMappingCylinderDeformation.homotopy_one _

omit B in
/--
Every full original next-stage target section is fixed by its SAME actual deformation
throughout the entire native time object.
-/
theorem nextStageDeformation_fixed {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} ((nextStageSection d).app
      X) ≫ (nextStageDeformation d).app X =
      timeProjection ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)).obj X) ≫
        (nextStageSection d).app X := by
  rw [nextStageDeformation_app, nextStageSection_app]
  exact PointedCGWH.EnrichedIntervalMappingCylinderDeformation.timeTargetLeg_homotopy _

/--
Every actual original telescope successor carries the entire SAME constructed original
mapping-cylinder deformation.
-/
def stageDeformation (n : ℕ) :
    (stage.{u, v} (n + 1)).functor ⋙ timeFunctor ⟶ (stage (n + 1)).functor :=
  nextStageDeformation (stage n)

/--
Every actual original telescope successor has the SAME original section from its original R
iterate.
-/
def stageSection (n : ℕ) : PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1) ⟶
    (stage.{u, v} (n + 1)).functor := nextStageSection (stage n)

omit B in
/--
ALL original whole telescope successor projections have their actual full original target
sections.
-/
theorem stageSection_projection (n : ℕ) : stageSection.{u, v} n ≫ projection (n + 1) =
    𝟙 (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)) :=
  nextStageSection_projection (stage n)

omit B in
/--
Every complete original telescope successor deformation starts at its SAME original whole
identity.
-/
theorem stageDeformation_zero (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    timeInclusion 0 ((stage (n + 1)).functor.obj X) ≫ (stageDeformation n).app X = 𝟙 _ :=
  nextStageDeformation_zero (stage n) X

omit B in
/--
Every original telescope successor deformation ends at its SAME original stage projection
followed by its original section.
-/
theorem stageDeformation_one (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    timeInclusion 1 ((stage (n + 1)).functor.obj X) ≫ (stageDeformation n).app X =
      (projection (n + 1)).app X ≫ (stageSection n).app X :=
  nextStageDeformation_one (stage n) X

omit B in
/--
Every complete original R target section is fixed throughout its SAME original telescope
successor deformation.
-/
theorem stageDeformation_fixed (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} ((stageSection n).app X) ≫
      (stageDeformation n).app X =
      timeProjection ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)).obj X) ≫
        (stageSection n).app X := nextStageDeformation_fixed (stage n) X

end PointedCGWH.SequentialSpectrum.MappingTelescope
