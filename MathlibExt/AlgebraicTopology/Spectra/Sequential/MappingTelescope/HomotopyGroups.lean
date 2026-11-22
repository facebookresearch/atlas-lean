/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.CompactFactorization
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.ClosedSequentialColimit

/-!
# Homotopy groups of the actual mapping telescope

Apply the actual closed-stage and compact-cube constructions to the original
mapping telescope at every level and homotopy degree. Type comparisons
include degree zero; positive groups retain the actual filtered group
quotient. Both inverse functions, all stage legs, and every spectrum-map
naturality use the original maps and colimit choices.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra
open scoped unitInterval Topology.Homotopy

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialHomotopyColimit
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

omit B in
/-- The whole SAME original evaluated telescope cocone retains every original input-map square. -/
theorem levelCocone_naturality (m : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (j : ℕ) :
    (levelCocone X m).ι.app j ≫
      PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m =
        ((levelDiagramFunctor m).map f).app j ≫ (levelCocone Y m).ι.app j := by
  let E := PointedCGWH.SequentialSpectrum.evaluation.{u, v} m
  exact (E.map_comp _ _).symm.trans
    ((E.congr_map (leg_naturality f j)).trans (E.map_comp _ _))

/-- The SAME original level diagram with its original all-degree piNFunctor. -/
def typeHomotopyDiagramFunctor (m n : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ Type v) :=
  levelDiagramFunctor m ⋙ (Functor.whiskeringRight ℕ PointedCGWH.{u, v}
    (Type v)).obj (piNFunctor n)

/-- The SAME original level diagram with its actual original positive-group functor. -/
def groupHomotopyDiagramFunctor (m n : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ GrpCat.{v}) :=
  levelDiagramFunctor m ⋙ (Functor.whiskeringRight ℕ PointedCGWH.{u, v}
    GrpCat.{v}).obj (piNPositiveFunctor n)

/-- The whole original chosen Type colimit comparison at every actual degree and level. -/
def telescopeTypeHomotopyIso (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ) :
    colimit (levelDiagram X m ⋙ piNFunctor n) ≅
      piN n (PointedCGWH.SequentialSpectrum.level (telescope X) m) :=
  piNComparisonIso n (levelCocone X m) (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ)

/-- The whole SAME genuine filtered group comparison at every positive degree and original level. -/
def telescopeGroupHomotopyIso (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ) :
    GrpCat.FilteredColimits.colimit (levelDiagram X m ⋙ piNPositiveFunctor n) ≅
      (piNPositiveFunctor n).obj (PointedCGWH.SequentialSpectrum.level (telescope X) m) :=
  piNPositiveComparisonIso n (levelCocone X m) (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ)

omit B in
/-- The full original forward Type comparison retains every original piN stage-leg map. -/
theorem telescopeTypeHomotopyIso_hom_ι (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n j : ℕ) :
    colimit.ι (levelDiagram X m ⋙ piNFunctor n) j ≫ (telescopeTypeHomotopyIso X m n).hom =
      (piNFunctor n).map (PointedCGWH.SequentialSpectrum.levelMap (leg X j) m) :=
  piNComparisonIso_hom_ι n (levelCocone X m) (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ) j

omit B in
/-- The full original inverse Type comparison retains every original piN stage-leg map. -/
theorem telescopeTypeHomotopyIso_inv_ι (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n j : ℕ) :
    (piNFunctor n).map (PointedCGWH.SequentialSpectrum.levelMap (leg X j) m) ≫
      (telescopeTypeHomotopyIso X m n).inv = colimit.ι (levelDiagram X m ⋙ piNFunctor n) j :=
  piNComparisonIso_inv_ι n (levelCocone X m) (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ) j

omit B in
/-- The full original forward positive comparison retains every original group stage-leg map. -/
theorem telescopeGroupHomotopyIso_hom_ι (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n j : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (levelDiagram X m ⋙ piNPositiveFunctor n)).ι.app j ≫
      (telescopeGroupHomotopyIso X m n).hom =
        (piNPositiveFunctor n).map (PointedCGWH.SequentialSpectrum.levelMap (leg X j) m) := by
  rw [show (telescopeGroupHomotopyIso X m n).hom =
      piNPositiveComparison n (levelCocone X m) from
    piNPositiveComparisonIso_hom n (levelCocone X m) (levelCoconeIsColimit X m)
      (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ)]
  exact piNPositiveComparison_ι n (levelCocone X m) j

omit B in
/-- The whole original inverse group comparison retains every original group stage-leg map. -/
theorem telescopeGroupHomotopyIso_inv_ι (X : PointedCGWH.SequentialSpectrum.{u, v}) (m n j : ℕ) :
    (piNPositiveFunctor n).map (PointedCGWH.SequentialSpectrum.levelMap (leg X j) m) ≫
      (telescopeGroupHomotopyIso X m n).inv =
        (GrpCat.FilteredColimits.colimitCocone (levelDiagram X m ⋙ piNPositiveFunctor n)).ι.app j :=
  piNPositiveComparisonIso_inv_ι n (levelCocone X m) (levelCoconeIsColimit X m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ) j

omit B in
/-- Every actual original spectrum map preserves the complete all-degree Type comparison. -/
theorem telescopeTypeHomotopyIso_naturality (m n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    colim.map ((typeHomotopyDiagramFunctor m n).map f) ≫ (telescopeTypeHomotopyIso Y m n).hom =
      (telescopeTypeHomotopyIso X m n).hom ≫
        (piNFunctor n).map (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) :=
  piNComparisonIso_naturality n (levelCocone X m) (levelCocone Y m)
    (levelCoconeIsColimit X m) (levelCoconeIsColimit Y m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding Y m φ)
    ((levelDiagramFunctor m).map f)
    (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m)
    (levelCocone_naturality m f)

omit B in
/-- Every actual original spectrum map preserves the complete original positive group comparison. -/
theorem telescopeGroupHomotopyIso_naturality (m n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    GrpCat.FilteredColimits.colimitMap ((groupHomotopyDiagramFunctor m n).map f) ≫
      (telescopeGroupHomotopyIso Y m n).hom = (telescopeGroupHomotopyIso X m n).hom ≫
        (piNPositiveFunctor n).map
          (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) :=
  piNPositiveComparisonIso_naturality n (levelCocone X m) (levelCocone Y m)
    (levelCoconeIsColimit X m) (levelCoconeIsColimit Y m)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding X m φ)
    (fun _ _ φ => levelDiagram_map_isClosedEmbedding Y m φ)
    ((levelDiagramFunctor m).map f)
    (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m)
    (levelCocone_naturality m f)

/-- The ENTIRE actual original all-degree Type telescope/evaluation comparison is natural. -/
def telescopeTypeHomotopyEvaluationIso (m n : ℕ) : typeHomotopyDiagramFunctor.{u, v} m n ⋙
    colim ≅ telescopeFunctor ⋙ PointedCGWH.SequentialSpectrum.evaluation m ⋙ piNFunctor n :=
  NatIso.ofComponents (fun X => telescopeTypeHomotopyIso X m n)
    (fun f => telescopeTypeHomotopyIso_naturality m n f)

/-- The ENTIRE actual original positive-group comparison uses the same genuine colimit functor. -/
def telescopeGroupHomotopyEvaluationIso (m n : ℕ) : groupHomotopyDiagramFunctor.{u, v} m n ⋙
    GrpCat.FilteredColimits.colimitFunctor ≅
      telescopeFunctor ⋙ PointedCGWH.SequentialSpectrum.evaluation m ⋙ piNPositiveFunctor n :=
  NatIso.ofComponents (fun X => telescopeGroupHomotopyIso X m n)
    (fun f => telescopeGroupHomotopyIso_naturality m n f)

omit B in
/-- The complete Type component-Iso function is the original chosen comparison. -/
theorem telescopeTypeHomotopyEvaluationIso_app (m n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeTypeHomotopyEvaluationIso m n).app X = telescopeTypeHomotopyIso X m n := rfl

omit B in
/-- The complete group component-Iso function is the SAME original filtered comparison. -/
theorem telescopeGroupHomotopyEvaluationIso_app (m n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeGroupHomotopyEvaluationIso m n).app X = telescopeGroupHomotopyIso X m n := rfl

omit B in
/-- All original inverse Type comparison maps retain the same full naturality square. -/
theorem telescopeTypeHomotopyIso_inv_naturality (m n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (piNFunctor n).map (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) ≫
      (telescopeTypeHomotopyIso Y m n).inv = (telescopeTypeHomotopyIso X m n).inv ≫
        colim.map ((typeHomotopyDiagramFunctor m n).map f) :=
  (telescopeTypeHomotopyEvaluationIso m n).inv.naturality f

omit B in
/-- All original inverse group comparison maps retain the same full naturality square. -/
theorem telescopeGroupHomotopyIso_inv_naturality (m n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (piNPositiveFunctor n).map
      (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) ≫
        (telescopeGroupHomotopyIso Y m n).inv = (telescopeGroupHomotopyIso X m n).inv ≫
          GrpCat.FilteredColimits.colimitMap ((groupHomotopyDiagramFunctor m n).map f) :=
  (telescopeGroupHomotopyEvaluationIso m n).inv.naturality f

end PointedCGWH.SequentialSpectrum.MappingTelescope
