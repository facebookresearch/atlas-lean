/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.HomotopyGroups
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHHomotopyGroupInvariance

/-!
# Mapping-cylinder stages and ordered-loop iteration homotopy colimits

Every original projection is weak in the original caller-B native level
model. Its literal piN and positive-group maps give actual diagram Isos
and the SAME chosen Type and genuine filtered Group colimit comparisons.
Both full inverse maps are identified with the original mapping-cylinder
target sections. All whole spectrum-map squares and every actual original
telescope leg are retained. No desired colimit Iso, stable-model law,
varying-degree claim or alternative stage/source/choice is an input.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.OrderedLoop (iterate iterationDiagram iterationDiagramFunctor)
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The WHOLE original projection diagram is natural in every original spectrum Arrow. -/
def projectionDiagramNatTrans : diagramFunctor.{u, v} ⟶ iterationDiagramFunctor where
  app := diagramProjection
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    exact (projection n).naturality f

omit B in
/-- Every complete component function is the SAME original stage projection. -/
theorem projectionDiagramNatTrans_app_app
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (projectionDiagramNatTrans.app X).app n = (projection n).app X := rfl

/-- The whole original R-iteration level diagram retains all finite maps and all input maps. -/
def levelIterationDiagramFunctor (m : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ PointedCGWH.{u, v}) :=
  iterationDiagramFunctor ⋙ (Functor.whiskeringRight ℕ PointedCGWH.SequentialSpectrum.{u, v}
    PointedCGWH.{u, v}).obj (PointedCGWH.SequentialSpectrum.evaluation m)

/-- The complete original R-iteration Type diagram uses the literal original homotopy degree. -/
def typeIterationDiagramFunctor (m k : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ Type v) :=
  levelIterationDiagramFunctor m ⋙
    (Functor.whiskeringRight ℕ PointedCGWH.{u, v} (Type v)).obj (piNFunctor k)

/-- The complete original R-iteration group diagram uses the SAME positive homotopy functor. -/
def groupIterationDiagramFunctor (m k : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ GrpCat.{v}) :=
  levelIterationDiagramFunctor m ⋙
    (Functor.whiskeringRight ℕ PointedCGWH.{u, v} GrpCat.{v}).obj (piNPositiveFunctor k)

/-- The entire evaluated original projection retains the actual original native component maps. -/
def levelDiagramProjectionNatTrans (m : ℕ) : levelDiagramFunctor.{u, v} m ⟶
    levelIterationDiagramFunctor m :=
  Functor.whiskerRight projectionDiagramNatTrans
    ((Functor.whiskeringRight ℕ PointedCGWH.SequentialSpectrum.{u, v}
      PointedCGWH.{u, v}).obj (PointedCGWH.SequentialSpectrum.evaluation m))

/-- The entire literal-degree original Type projection retains every original naturality. -/
def typeDiagramProjectionNatTrans (m k : ℕ) : typeHomotopyDiagramFunctor.{u, v} m k ⟶
    typeIterationDiagramFunctor m k :=
  Functor.whiskerRight (levelDiagramProjectionNatTrans m)
    ((Functor.whiskeringRight ℕ PointedCGWH.{u, v} (Type v)).obj (piNFunctor k))

/-- The entire positive-degree original group projection retains every original naturality. -/
def groupDiagramProjectionNatTrans (m k : ℕ) : groupHomotopyDiagramFunctor.{u, v} m k ⟶
    groupIterationDiagramFunctor m k :=
  Functor.whiskerRight (levelDiagramProjectionNatTrans m)
    ((Functor.whiskeringRight ℕ PointedCGWH.{u, v} GrpCat.{v}).obj (piNPositiveFunctor k))

omit B in
/-- The entire Type component function is the actual original piN projection map. -/
theorem typeDiagramProjectionNatTrans_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((typeDiagramProjectionNatTrans m k).app X).app n =
      (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m) :=
  rfl

omit B in
/-- The entire group component homomorphism is the actual original positive projection map. -/
theorem groupDiagramProjectionNatTrans_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((groupDiagramProjectionNatTrans m k).app X).app n =
      (piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m) := rfl

/-- Every SAME original projection level is weak in the original selected pointed model. -/
theorem projectionLevelWeakEquivalence (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m : ℕ) :
    WeakEquivalence (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m) := by
  have h := (HomotopicalAlgebra.weakEquivalence_iff _).mp (projection_weakEquivalence n X)
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq] at h
  have he := (EvaluationTransfer.evaluationProperty_iff
    (fun a : PointedCGWH.Spectra.Sequential.Index.{u, v} =>
      CategoryTheory.EnrichedFunctorCat.evaluation a)
    (weakEquivalences PointedCGWH.{u, v}) _).mp h
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    (he (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m))

/-- The full all-degree original stage projection Type Iso comes from its proved weakness. -/
def stageTypeIso (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (m k : ℕ) :
    piN k (PointedCGWH.SequentialSpectrum.level ((stage n).functor.obj X) m) ≅
      piN k (PointedCGWH.SequentialSpectrum.level ((iterate n).obj X) m) :=
  (piNEquivOfWeakEquivalence k
    (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m)
    (projectionLevelWeakEquivalence n X m)).toIso

/-- The full original positive group stage Iso comes from the SAME actual weak projection map. -/
def stageGroupIso (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (m k : ℕ) :
    (piNPositiveFunctor k).obj (PointedCGWH.SequentialSpectrum.level ((stage n).functor.obj X) m) ≅
      (piNPositiveFunctor k).obj (PointedCGWH.SequentialSpectrum.level ((iterate n).obj X) m) :=
  (piNPositiveMulEquivOfWeakEquivalence k
    (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m)
    (projectionLevelWeakEquivalence n X m)).toGrpIso

/-- The entire forward Type Iso function is precisely the original piN projection map. -/
theorem stageTypeIso_hom (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (m k : ℕ) :
    (stageTypeIso n X m k).hom =
      (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m) := by
  apply ConcreteCategory.hom_ext
  intro a
  exact piNEquivOfWeakEquivalence_apply k _ (projectionLevelWeakEquivalence n X m) a

/-- The entire forward group Iso function is precisely the original positive projection map. -/
theorem stageGroupIso_hom (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (m k : ℕ) :
    (stageGroupIso n X m k).hom = (piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m) := by
  apply GrpCat.hom_ext
  ext a
  exact piNPositiveMulEquivOfWeakEquivalence_apply k _ (projectionLevelWeakEquivalence n X m) a

/-- The entire actual Type inverse is the SAME original mapping-cylinder target-section map. -/
theorem stageTypeIso_inv_section (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m k : ℕ) :
    (stageTypeIso (n + 1) X m k).inv =
      (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m) := by
  let E := PointedCGWH.SequentialSpectrum.evaluation.{u, v} m
  let Q := piNFunctor.{u, v} k
  have h := congr_app (stageSection_projection n) X
  have he : E.map ((stageSection n).app X) ≫ E.map ((projection (n + 1)).app X) =
      𝟙 (E.obj ((iterate (n + 1)).obj X)) :=
    (E.map_comp _ _).symm.trans ((E.congr_map h).trans (E.map_id _))
  have hq : Q.map (E.map ((stageSection n).app X)) ≫
      Q.map (E.map ((projection (n + 1)).app X)) = 𝟙 _ :=
    (Q.map_comp _ _).symm.trans ((Q.congr_map he).trans (Q.map_id _))
  apply (cancel_mono (stageTypeIso (n + 1) X m k).hom).mp
  rw [Iso.inv_hom_id, stageTypeIso_hom]
  exact hq.symm

/-- The entire actual group inverse is the SAME original mapping-cylinder target-section map. -/
theorem stageGroupIso_inv_section (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (m k : ℕ) :
    (stageGroupIso (n + 1) X m k).inv = (piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m) := by
  let E := PointedCGWH.SequentialSpectrum.evaluation.{u, v} m
  let Q := piNPositiveFunctor.{u, v} k
  have h := congr_app (stageSection_projection n) X
  have he : E.map ((stageSection n).app X) ≫ E.map ((projection (n + 1)).app X) =
      𝟙 (E.obj ((iterate (n + 1)).obj X)) :=
    (E.map_comp _ _).symm.trans ((E.congr_map h).trans (E.map_id _))
  have hq : Q.map (E.map ((stageSection n).app X)) ≫
      Q.map (E.map ((projection (n + 1)).app X)) = 𝟙 _ :=
    (Q.map_comp _ _).symm.trans ((Q.congr_map he).trans (Q.map_id _))
  apply (cancel_mono (stageGroupIso (n + 1) X m k).hom).mp
  rw [Iso.inv_hom_id, stageGroupIso_hom]
  exact hq.symm

/-- The WHOLE Type diagram Iso has all original finite-map and input-map squares. -/
def typeDiagramProjectionIso (m k : ℕ) : typeHomotopyDiagramFunctor.{u, v} m k ≅
    typeIterationDiagramFunctor m k :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun n => stageTypeIso n X m k)
    (fun φ => by
      rw [stageTypeIso_hom, stageTypeIso_hom]
      exact ((typeDiagramProjectionNatTrans m k).app X).naturality φ))
    (fun f => by
      apply NatTrans.ext
      funext n
      change ((typeHomotopyDiagramFunctor m k).map f).app n ≫ (stageTypeIso n _ m k).hom =
        (stageTypeIso n _ m k).hom ≫ ((typeIterationDiagramFunctor m k).map f).app n
      rw [stageTypeIso_hom, stageTypeIso_hom]
      exact congr_app ((typeDiagramProjectionNatTrans m k).naturality f) n)

/-- The WHOLE group diagram Iso has all original finite-map and spectrum-map squares. -/
def groupDiagramProjectionIso (m k : ℕ) : groupHomotopyDiagramFunctor.{u, v} m k ≅
    groupIterationDiagramFunctor m k :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun n => stageGroupIso n X m k)
    (fun φ => by
      rw [stageGroupIso_hom, stageGroupIso_hom]
      exact ((groupDiagramProjectionNatTrans m k).app X).naturality φ))
    (fun f => by
      apply NatTrans.ext
      funext n
      change ((groupHomotopyDiagramFunctor m k).map f).app n ≫ (stageGroupIso n _ m k).hom =
        (stageGroupIso n _ m k).hom ≫ ((groupIterationDiagramFunctor m k).map f).app n
      rw [stageGroupIso_hom, stageGroupIso_hom]
      exact congr_app ((groupDiagramProjectionNatTrans m k).naturality f) n)

/-- The ENTIRE Type diagram-Iso hom is the SAME actual original projection NatTrans. -/
theorem typeDiagramProjectionIso_hom (m k : ℕ) :
    (typeDiagramProjectionIso.{u, v} m k).hom = typeDiagramProjectionNatTrans m k := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext n
  exact stageTypeIso_hom n X m k

/-- The ENTIRE group diagram-Iso hom is the SAME actual original projection NatTrans. -/
theorem groupDiagramProjectionIso_hom (m k : ℕ) :
    (groupDiagramProjectionIso.{u, v} m k).hom = groupDiagramProjectionNatTrans m k := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext n
  exact stageGroupIso_hom n X m k

/-- The entire Type diagram-Iso inverse keeps every actual original target-section function. -/
theorem typeDiagramProjectionIso_inv_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((typeDiagramProjectionIso m k).inv.app X).app (n + 1) =
      (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m) :=
  stageTypeIso_inv_section n X m k

/-- The entire group diagram-Iso inverse keeps every actual original target-section function. -/
theorem groupDiagramProjectionIso_inv_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((groupDiagramProjectionIso m k).inv.app X).app (n + 1) =
      (piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m) :=
  stageGroupIso_inv_section n X m k

/-- The full original Type colimit projection comes from the whole actual original diagram Iso. -/
def typeColimitProjectionNatIso (m k : ℕ) : typeHomotopyDiagramFunctor.{u, v} m k ⋙ colim ≅
    typeIterationDiagramFunctor m k ⋙ colim :=
  Functor.isoWhiskerRight (typeDiagramProjectionIso m k) colim

/-- The full original group comparison uses the SAME genuine filtered group colimit functor. -/
def groupColimitProjectionNatIso (m k : ℕ) : groupHomotopyDiagramFunctor.{u, v} m k ⋙
    GrpCat.FilteredColimits.colimitFunctor ≅ groupIterationDiagramFunctor m k ⋙
      GrpCat.FilteredColimits.colimitFunctor :=
  Functor.isoWhiskerRight (groupDiagramProjectionIso m k)
    GrpCat.FilteredColimits.colimitFunctor

/-- The WHOLE original telescope Type comparison has the same chosen original R colimit. -/
def telescopeTypeIterationColimitNatIso (m k : ℕ) :
    telescopeFunctor.{u, v} ⋙ PointedCGWH.SequentialSpectrum.evaluation m ⋙ piNFunctor k ≅
      typeIterationDiagramFunctor m k ⋙ colim :=
  (telescopeTypeHomotopyEvaluationIso m k).symm ≪≫ typeColimitProjectionNatIso m k

/-- The WHOLE original telescope group comparison has the same genuine original R colimit. -/
def telescopeGroupIterationColimitNatIso (m k : ℕ) :
    telescopeFunctor.{u, v} ⋙ PointedCGWH.SequentialSpectrum.evaluation m ⋙ piNPositiveFunctor k ≅
      groupIterationDiagramFunctor m k ⋙ GrpCat.FilteredColimits.colimitFunctor :=
  (telescopeGroupHomotopyEvaluationIso m k).symm ≪≫ groupColimitProjectionNatIso m k

/-- The entire Type comparison forward function retains both actual original maps. -/
theorem telescopeTypeIterationColimitNatIso_hom_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeTypeIterationColimitNatIso m k).hom.app X =
      (telescopeTypeHomotopyIso X m k).inv ≫
        colim.map ((typeDiagramProjectionNatTrans m k).app X) := by
  change (telescopeTypeHomotopyIso X m k).inv ≫
    colim.map ((typeDiagramProjectionIso m k).hom.app X) = _
  rw [typeDiagramProjectionIso_hom]

/-- The entire group comparison forward function retains both actual original maps. -/
theorem telescopeGroupIterationColimitNatIso_hom_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeGroupIterationColimitNatIso m k).hom.app X =
      (telescopeGroupHomotopyIso X m k).inv ≫
        GrpCat.FilteredColimits.colimitMap ((groupDiagramProjectionNatTrans m k).app X) := by
  change (telescopeGroupHomotopyIso X m k).inv ≫
    GrpCat.FilteredColimits.colimitMap ((groupDiagramProjectionIso m k).hom.app X) = _
  rw [groupDiagramProjectionIso_hom]

/-- The entire Type inverse comparison retains its original diagram inverse and telescope map. -/
theorem telescopeTypeIterationColimitNatIso_inv_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeTypeIterationColimitNatIso m k).inv.app X =
      colim.map ((typeDiagramProjectionIso m k).inv.app X) ≫
        (telescopeTypeHomotopyIso X m k).hom := rfl

/-- The entire group inverse retains the SAME genuine group map and original telescope map. -/
theorem telescopeGroupIterationColimitNatIso_inv_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeGroupIterationColimitNatIso m k).inv.app X =
      GrpCat.FilteredColimits.colimitMap ((groupDiagramProjectionIso m k).inv.app X) ≫
        (telescopeGroupHomotopyIso X m k).hom := rfl

/-- EVERY original Type telescope leg is the original projection followed by the original R leg. -/
theorem telescopeTypeIterationColimitNatIso_hom_leg (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap (leg X n) m) ≫
        (telescopeTypeIterationColimitNatIso m k).hom.app X =
      (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m) ≫
        colimit.ι ((typeIterationDiagramFunctor m k).obj X) n := by
  let a : levelDiagram X m ⋙ piNFunctor k ⟶ (typeIterationDiagramFunctor m k).obj X :=
    (typeDiagramProjectionNatTrans m k).app X
  have hwhole : (telescopeTypeIterationColimitNatIso m k).hom.app X =
      (telescopeTypeHomotopyIso X m k).inv ≫ colim.map a :=
    telescopeTypeIterationColimitNatIso_hom_app m k X
  have hleg := telescopeTypeHomotopyIso_inv_ι X m k n
  exact (congrArg (fun f => (piNFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap (leg X n) m) ≫ f) hwhole).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ colim.map a) hleg).trans (colimit.ι_map a n)))

/-- EVERY original group telescope leg is the original projection followed by the original R leg. -/
theorem telescopeGroupIterationColimitNatIso_hom_leg (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (piNPositiveFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap (leg X n) m) ≫
        (telescopeGroupIterationColimitNatIso m k).hom.app X =
      (piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m) ≫
        (GrpCat.FilteredColimits.colimitCocone
          ((groupIterationDiagramFunctor m k).obj X)).ι.app n := by
  let a : levelDiagram X m ⋙ piNPositiveFunctor k ⟶
      (groupIterationDiagramFunctor m k).obj X :=
    (groupDiagramProjectionNatTrans m k).app X
  have hwhole : (telescopeGroupIterationColimitNatIso m k).hom.app X =
      (telescopeGroupHomotopyIso X m k).inv ≫ GrpCat.FilteredColimits.colimitMap a :=
    telescopeGroupIterationColimitNatIso_hom_app m k X
  have hleg := telescopeGroupHomotopyIso_inv_ι X m k n
  exact (congrArg (fun f => (piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap (leg X n) m) ≫ f) hwhole).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ GrpCat.FilteredColimits.colimitMap a) hleg).trans
        (GrpCat.FilteredColimits.colimitMap_ι a n)))

/-- The complete original Type inverse retains every original R leg and actual target section. -/
theorem telescopeTypeIterationColimitNatIso_inv_section_leg (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    colimit.ι ((typeIterationDiagramFunctor m k).obj X) (n + 1) ≫
        (telescopeTypeIterationColimitNatIso m k).inv.app X =
      (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m) ≫
        (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap (leg X (n + 1)) m) := by
  let a : (typeIterationDiagramFunctor m k).obj X ⟶ levelDiagram X m ⋙ piNFunctor k :=
    (typeDiagramProjectionIso m k).inv.app X
  have hwhole : (telescopeTypeIterationColimitNatIso m k).inv.app X =
      colim.map a ≫ (telescopeTypeHomotopyIso X m k).hom :=
    telescopeTypeIterationColimitNatIso_inv_app m k X
  have hfac := colimit.ι_map a (n + 1)
  have hleg := telescopeTypeHomotopyIso_hom_ι X m k (n + 1)
  have hsection : a.app (n + 1) = (piNFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m) :=
    typeDiagramProjectionIso_inv_app_app m k X n
  exact (congrArg (fun f =>
      colimit.ι ((typeIterationDiagramFunctor m k).obj X) (n + 1) ≫ f) hwhole).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ (telescopeTypeHomotopyIso X m k).hom) hfac).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => a.app (n + 1) ≫ f) hleg).trans
            (congrArg (fun f => f ≫ (piNFunctor k).map
              (PointedCGWH.SequentialSpectrum.levelMap (leg X (n + 1)) m)) hsection)))))

/-- The complete original group inverse retains every original R leg and actual target section. -/
theorem telescopeGroupIterationColimitNatIso_inv_section_leg (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone
      ((groupIterationDiagramFunctor m k).obj X)).ι.app (n + 1) ≫
        (telescopeGroupIterationColimitNatIso m k).inv.app X =
      (piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m) ≫
          (piNPositiveFunctor k).map
            (PointedCGWH.SequentialSpectrum.levelMap (leg X (n + 1)) m) := by
  let a : (groupIterationDiagramFunctor m k).obj X ⟶ levelDiagram X m ⋙
      piNPositiveFunctor k := (groupDiagramProjectionIso m k).inv.app X
  have hwhole : (telescopeGroupIterationColimitNatIso m k).inv.app X =
      GrpCat.FilteredColimits.colimitMap a ≫ (telescopeGroupHomotopyIso X m k).hom :=
    telescopeGroupIterationColimitNatIso_inv_app m k X
  have hfac := GrpCat.FilteredColimits.colimitMap_ι a (n + 1)
  have hleg := telescopeGroupHomotopyIso_hom_ι X m k (n + 1)
  have hsection : a.app (n + 1) = (piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m) :=
    groupDiagramProjectionIso_inv_app_app m k X n
  exact (congrArg (fun f => (GrpCat.FilteredColimits.colimitCocone
      ((groupIterationDiagramFunctor m k).obj X)).ι.app (n + 1) ≫ f) hwhole).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ (telescopeGroupHomotopyIso X m k).hom) hfac).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => a.app (n + 1) ≫ f) hleg).trans
            (congrArg (fun f => f ≫ (piNPositiveFunctor k).map
              (PointedCGWH.SequentialSpectrum.levelMap (leg X (n + 1)) m)) hsection)))))

/-- Every original spectrum Arrow retains the entire forward Type telescope/R-colimit square. -/
theorem telescopeTypeIterationColimitNatIso_hom_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) ≫
        (telescopeTypeIterationColimitNatIso m k).hom.app Y =
      (telescopeTypeIterationColimitNatIso m k).hom.app X ≫
        colim.map ((typeIterationDiagramFunctor m k).map f) :=
  (telescopeTypeIterationColimitNatIso m k).hom.naturality f

/-- Every original spectrum Arrow retains the entire inverse Type telescope/R-colimit square. -/
theorem telescopeTypeIterationColimitNatIso_inv_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    colim.map ((typeIterationDiagramFunctor m k).map f) ≫
        (telescopeTypeIterationColimitNatIso m k).inv.app Y =
      (telescopeTypeIterationColimitNatIso m k).inv.app X ≫
        (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) :=
  (telescopeTypeIterationColimitNatIso m k).inv.naturality f

/-- Every original spectrum Arrow retains the entire forward group telescope/R-colimit square. -/
theorem telescopeGroupIterationColimitNatIso_hom_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) ≫
        (telescopeGroupIterationColimitNatIso m k).hom.app Y =
      (telescopeGroupIterationColimitNatIso m k).hom.app X ≫
        GrpCat.FilteredColimits.colimitMap ((groupIterationDiagramFunctor m k).map f) :=
  (telescopeGroupIterationColimitNatIso m k).hom.naturality f

/-- Every original spectrum Arrow retains the entire inverse group telescope/R-colimit square. -/
theorem telescopeGroupIterationColimitNatIso_inv_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    GrpCat.FilteredColimits.colimitMap ((groupIterationDiagramFunctor m k).map f) ≫
        (telescopeGroupIterationColimitNatIso m k).inv.app Y =
      (telescopeGroupIterationColimitNatIso m k).inv.app X ≫
        (piNPositiveFunctor k).map
          (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) :=
  (telescopeGroupIterationColimitNatIso m k).inv.naturality f

end PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
