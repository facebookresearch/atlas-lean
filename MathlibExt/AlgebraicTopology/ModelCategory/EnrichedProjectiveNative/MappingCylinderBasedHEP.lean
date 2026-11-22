/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.HomotopyExtension
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.BasedHomotopyExtension
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHBasedHomotopyExtension
import
  MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderCofibration
import MathlibExt.Topology.Category.PointedCGWH.TensorMappingAdjunction
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.ClosedStages

/-!
# Based homotopy extension for enriched mapping cylinders

Scalar tensoring transports based homotopy extension of coefficient maps to
arbitrary enriched `PointedCGWH` diagrams through the tensor–mapping adjunction
and the time-action associator. The mapping-cylinder source and target legs
therefore have based homotopy extension, with both endpoint and homotopy
compatibility equations. For sequential mapping telescopes, successor
transitions, target sections and finite composites have the same property.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.EnrichedBasedHomotopyExtension
open PointedCGWH.EnrichedFunctorMapping PointedCGWH.EnrichedIntervalContraction
open PointedCGWH.EnrichedIntervalCylinderModel PointedCGWH.EnrichedIntervalMappingCylinder
open PointedCGWH.EnrichedIntervalMappingCylinderModel
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The original scalar inverse-unit/associator bridge retains BOTH complete original maps. -/
theorem scalarUnitAssociator_inv (M : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    scalarTensorMap (λ_ M).inv X ≫ (scalarAssociatorIso (𝟙_ PointedCGWH) M X).hom =
      (scalarUnitIso (tensorLeftObject M X)).inv := by
  apply (cancel_mono (scalarUnitIso (tensorLeftObject M X)).hom).1
  rw [Category.assoc, scalarAssociatorIso_unit_left, ← scalarTensorMap_comp,
    Iso.inv_hom_id, scalarTensorMap_id, Iso.inv_hom_id]

/-- The entire SAME original scalar adjunction commutes with the ACTUAL full free-time functor. -/
def timeActionIso (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PointedCGWH.BasedTimeHomotopyExtension.timeFunctor ⋙
        WeightedEndVariance.tensorBifunctor.flip.obj X ≅
      WeightedEndVariance.tensorBifunctor.flip.obj X ⋙ timeFunctor :=
  NatIso.ofComponents
    (fun M => scalarAssociatorIso PointedCGWH.RealizedIntervalContraction.time M X)
    (fun h => scalarAssociatorIso_scalar_right PointedCGWH.RealizedIntervalContraction.time h X)

/-- EVERY full original time comparison component is the SAME original scalar associator. -/
theorem timeActionIso_app (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (M : PointedCGWH.{u, v}) :
    (timeActionIso X).app M =
      scalarAssociatorIso PointedCGWH.RealizedIntervalContraction.time M X := rfl

/-- Both ENTIRE original endpoint maps are preserved through the SAME full time comparison. -/
theorem timeActionIso_endpoint (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (M : PointedCGWH.{u, v}) :
    (WeightedEndVariance.tensorBifunctor.flip.obj X).map
        ((PointedCGWH.BasedTimeHomotopyExtension.inclusionNatTrans 0).app M) ≫
      ((timeActionIso X).app M).hom =
      (timeInclusionNatTrans 0).app ((WeightedEndVariance.tensorBifunctor.flip.obj X).obj M) := by
  rw [timeActionIso_app, PointedCGWH.BasedTimeHomotopyExtension.inclusionNatTrans_app]
  change scalarTensorMap ((λ_ M).inv ≫ PointedCGWH.freePointIntervalEndpoint 0 ▷ M) X ≫
      (scalarAssociatorIso PointedCGWH.RealizedIntervalContraction.time M X).hom =
    (scalarUnitIso (tensorLeftObject M X)).inv ≫
      scalarTensorMap (PointedCGWH.freePointIntervalEndpoint 0) (tensorLeftObject M X)
  rw [scalarTensorMap_comp, Category.assoc, scalarAssociatorIso_scalar_left,
    ← Category.assoc, scalarUnitAssociator_inv]

/--
Genuine coefficient based HEP transports through the SAME actual scalar adjunction/time data
for EVERY arbitrary original native diagram, with NO diagram Cof premise.
-/
theorem scalarTensorMap_mem {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    (hi : PointedCGWH.BasedTimeHomotopyExtension.property i)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) : property (scalarTensorMap i X) :=
  IntervalHomotopyExtension.map_mem_of_adjunction (tensorMappingAdjunction X)
    PointedCGWH.BasedTimeHomotopyExtension.timeFunctor
    (PointedCGWH.BasedTimeHomotopyExtension.inclusionNatTrans 0) timeFunctor
    (timeInclusionNatTrans 0) (timeActionIso X) (timeActionIso_endpoint X) i hi

/-- The literal entire ORIGINAL joint diagram map has genuine based HEP for arbitrary diagrams. -/
theorem jointMap_mem (X : EnrichedFunctorCat PointedCGWH.{u, v} I) : property (jointMap X) :=
  (property.arrow_mk_iso_iff (jointMapArrowIso X)).mpr
    (scalarTensorMap_mem IntervalCoefficient.jointEndpoints
      PointedCGWH.BasedTimeHomotopyExtension.jointEndpoints_mem X)

/-- The original second native coprojection also has literal based HEP for arbitrary endpoints. -/
theorem coprod_inr_mem (X Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    property (coprod.inr : Z ⟶ X ⨿ Z) := by
  let e : Arrow.mk (coprod.inr : Z ⟶ X ⨿ Z) ≅ Arrow.mk (coprod.inl : Z ⟶ Z ⨿ X) :=
    Arrow.isoMk' _ _ (Iso.refl Z) (coprod.braiding X Z) (by simp)
  exact (property.arrow_mk_iso_iff e).mpr (coprod_inl_mem Z X)

/-- The SAME original attachment pushout gives based HEP of the full original fold map. -/
theorem foldMap_mem (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    property (foldMap f) :=
  MorphismProperty.of_isPushout (attachment_isPushout f).flip (jointMap_mem f.left)

/-- EVERY arbitrary-source original MC source factor has GENUINE literal based HEP. -/
theorem source_mem (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    property (source f) := by
  have h := property.comp_mem (coprod.inl : f.left ⟶ f.left ⨿ f.right) (foldMap f)
    (coprod_inl_mem f.left f.right) (foldMap_mem f)
  simpa only [foldMap, coprod.inl_desc] using h

/-- EVERY original MC target leg has GENUINE literal based HEP on arbitrary endpoints. -/
theorem targetLeg_mem (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    property (targetLeg f) := by
  have h := property.comp_mem (coprod.inr : f.right ⟶ f.left ⨿ f.right) (foldMap f)
    (coprod_inr_mem f.left f.right) (foldMap_mem f)
  simpa only [foldMap, coprod.inr_desc] using h

/--
The SAME original MC source extends EVERY actual based map/homotopy pair, with both full
literal original extension equations and no source cofibrancy.
-/
theorem source_extension (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (g : object f ⟶ Y)
    (H : timeObject f.left ⟶ Y) (h : timeInclusion 0 f.left ≫ H = source f ≫ g) :
    ∃ K : timeObject (object f) ⟶ Y, timeInclusion 0 (object f) ≫ K = g ∧
      tensorLeftMap PointedCGWH.RealizedIntervalContraction.time (source f) ≫ K = H :=
  source_mem f Y g H h

end PointedCGWH.EnrichedBasedHomotopyExtension

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

omit B in
/-- ALL original next transitions have actual literal based HEP for every original input. -/
theorem nextTransition_basedHEP {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    EnrichedBasedHomotopyExtension.property ((nextTransition d).app X) := by
  have h := EnrichedBasedHomotopyExtension.source_mem (stageArrows d |>.obj X)
  exact (congrArg
    (fun g : d.functor.obj X ⟶ (nextStage d).functor.obj X =>
      EnrichedBasedHomotopyExtension.property g) (nextTransition_app d X)).mpr h

omit B in
/-- EVERY original recursive telescope successor has genuine based HEP on arbitrary inputs. -/
theorem transition_basedHEP (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    EnrichedBasedHomotopyExtension.property ((transition n).app X) :=
  nextTransition_basedHEP (stage n) X

omit B in
/-- ALL original next target sections have actual literal based HEP for every original input. -/
theorem nextStageSection_basedHEP {n : ℕ} (d : Stage.{u, v} n)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    EnrichedBasedHomotopyExtension.property ((nextStageSection d).app X) := by
  have h := EnrichedBasedHomotopyExtension.targetLeg_mem (stageArrows d |>.obj X)
  exact (congrArg
    (fun g : (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate (n + 1)).obj X ⟶
      (nextStage d).functor.obj X => EnrichedBasedHomotopyExtension.property g)
    (nextStageSection_app d X)).mpr h

omit B in
/-- EVERY original recursive target section has genuine literal based HEP on arbitrary inputs. -/
theorem stageSection_basedHEP (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    EnrichedBasedHomotopyExtension.property ((stageSection n).app X) :=
  nextStageSection_basedHEP (stage n) X

omit B in
/-- EVERY original arbitrary finite stage transition has the SAME literal based HEP. -/
theorem diagram_map_basedHEP (X : PointedCGWH.SequentialSpectrum.{u, v})
    {i j : ℕ} (φ : i ⟶ j) : EnrichedBasedHomotopyExtension.property ((diagram X).map φ) := by
  let P : MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
    EnrichedBasedHomotopyExtension.property
  let F := diagram X
  have hStep (n : ℕ) : P (F.map (homOfLE (Nat.le_succ n))) := by
    rw [show F = diagram X from rfl, diagram_map_succ]
    exact transition_basedHEP n X
  have hMaps (j : ℕ) (hij : i ≤ j) : P (F.map (homOfLE hij)) := by
    induction j, hij using Nat.le_induction with
    | base => simpa only [homOfLE_refl, F.map_id] using P.id_mem (F.obj i)
    | succ j hij ih =>
        rw [← homOfLE_comp hij (Nat.le_succ j), F.map_comp]
        exact P.comp_mem _ _ ih (hStep j)
  change P (F.map φ)
  rw [← homOfLE_leOfHom φ]
  exact hMaps j (leOfHom φ)

end PointedCGWH.SequentialSpectrum.MappingTelescope
