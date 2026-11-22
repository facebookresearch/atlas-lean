/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IterationHomotopy
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.GroupUnitCoherence

/-!
# The ONE actual original varying-degree diagonal homotopy diagram

The objects are the original positive homotopy groups of level m+n in
actual degree k+n+1. Each transition is the original group structure map
followed by the full original simultaneous level/degree index Iso. The
whole diagram is natural on every original spectrum Arrow. Geometry's
actual iterate-unit square gives its complete Iso with the SAME original
R iteration. The true original MC/telescope comparison then supplies both
complete diagonal colimit maps and every original stage leg. All integer
degree offsets are represented by genuine positive tails. Structure-map
compatibility, tail cofinality and original forward8.8 remain later proofs.
No second diagonal, alternative original map, desired stable law or
source/MC/model/factorization replacement is introduced.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop (iterationDiagram iterationDiagram_map_succ)
open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.GroupUnitCoherenceGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The SAME actual sigma map followed by BOTH original index maps is the entire transition. -/
def diagonalTransition (n m k : ℕ) : levelCubeGroupFunctor.{u, v} (m + n) (k + n) ⟶
    levelCubeGroupFunctor (m + (n + 1)) (k + (n + 1)) :=
  groupStructureNatTrans (m + n) (k + n) ≫ (groupUnitIndexNatIso n m k).hom

/-- Every whole transition component preserves both actual original source maps. -/
theorem diagonalTransition_app (n m k : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (diagonalTransition n m k).app X = (groupStructureNatTrans (m + n) (k + n)).app X ≫
      (groupUnitIndexNatIso n m k).hom.app X := rfl

/-- The entire positive diagonal function is the SAME original cube structure and index map. -/
theorem diagonalTransition_eq_cube (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (a : piN (k + n + 1) (X.level (m + n))) :
    ((diagonalTransition n m k).app X).hom a =
      ((groupUnitIndexNatIso n m k).hom.app X).hom
        ((cubeStructureNatTrans (m + n) (k + n + 1)).app X a) :=
  congrArg ((groupUnitIndexNatIso n m k).hom.app X).hom
    (groupStructureNatTrans_eq_cube (m + n) (k + n) X a)

/-- The WHOLE original changing-level/changing-degree diagram uses the actual source maps. -/
def diagonalDiagram (X : PointedCGWH.SequentialSpectrum.{u, v}) (m k : ℕ) : ℕ ⥤ GrpCat.{v} :=
  Functor.ofSequence (fun n => (diagonalTransition n m k).app X)

/-- Every actual diagonal object is the SAME original positive homotopy group. -/
theorem diagonalDiagram_obj (X : PointedCGWH.SequentialSpectrum.{u, v}) (m k n : ℕ) :
    (diagonalDiagram X m k).obj n = (piNPositiveFunctor (k + n)).obj (X.level (m + n)) := rfl

/-- Every actual original successive map is the full sigma-plus-index transition. -/
theorem diagonalDiagram_map_succ (X : PointedCGWH.SequentialSpectrum.{u, v}) (m k n : ℕ) :
    (diagonalDiagram X m k).map (homOfLE (Nat.le_succ n)) =
      (diagonalTransition n m k).app X :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- EVERY finite diagonal map is the actual full composite of the same original transitions. -/
theorem diagonalDiagram_map (X : PointedCGWH.SequentialSpectrum.{u, v}) (m k : ℕ)
    {i j : ℕ} (f : i ⟶ j) : (diagonalDiagram X m k).map f =
      Functor.OfSequence.map (fun n => (diagonalTransition n m k).app X) i j (leOfHom f) :=
  rfl

/-- Every original spectrum Arrow acts through all original changing degrees and levels. -/
def diagonalDiagramMap (m k : ℕ) {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    diagonalDiagram X m k ⟶ diagonalDiagram Y m k :=
  NatTrans.ofSequence (fun n => (levelCubeGroupFunctor (m + n) (k + n)).map f)
    (fun n => by
      rw [diagonalDiagram_map_succ, diagonalDiagram_map_succ]
      exact ((diagonalTransition n m k).naturality f).symm)

/-- The whole ONE original diagonal construction preserves every input identity and composition. -/
def diagonalDiagramFunctor (m k : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ GrpCat.{v}) where
  obj X := diagonalDiagram X m k
  map := diagonalDiagramMap m k
  map_id X := by
    apply NatTrans.ext
    funext n
    exact (levelCubeGroupFunctor (m + n) (k + n)).map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (levelCubeGroupFunctor (m + n) (k + n)).map_comp f g

/-- Every ENTIRE diagonal input component is the original positive group map. -/
theorem diagonalDiagramFunctor_map_app (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    ((diagonalDiagramFunctor m k).map f).app n =
      (piNPositiveFunctor (k + n)).map (PointedCGWH.SequentialSpectrum.levelMap f (m + n)) :=
  rfl

/-- Every ENTIRE diagonal input function is the original literal-degree Type map. -/
theorem diagonalDiagramFunctor_map_apply (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ)
    (a : piN (k + n + 1) (X.level (m + n))) :
    (((diagonalDiagramFunctor m k).map f).app n).hom a =
      piNMap (k + n + 1) (PointedCGWH.SequentialSpectrum.levelMap f (m + n)) a :=
  piNPositiveMap_apply (k + n) (PointedCGWH.SequentialSpectrum.levelMap f (m + n)) a

/-- The SAME original R-iteration successive group map retains its exact original unit. -/
theorem groupIterationDiagram_map_succ (X : PointedCGWH.SequentialSpectrum.{u, v})
    (m k n : ℕ) : ((groupIterationDiagramFunctor m k).obj X).map
      (homOfLE (Nat.le_succ n)) = (piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap
          ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app X) m) := by
  change (piNPositiveFunctor k).map
    (PointedCGWH.SequentialSpectrum.levelMap
      ((iterationDiagram X).map (homOfLE (Nat.le_succ n))) m) = _
  rw [iterationDiagram_map_succ]
  rfl

/-- The ENTIRE original R-unit/evaluation square is precisely the actual diagonal transition. -/
theorem iteration_diagonal_transition_whole (n m k : ℕ) :
    Functor.whiskerRight
        (Functor.whiskerRight (PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n)
          (PointedCGWH.SequentialSpectrum.evaluation m)) (piNPositiveFunctor k) ≫
            (iterationGroupEvaluationNatIso (n + 1) m k).hom =
      (iterationGroupEvaluationNatIso n m k).hom ≫ diagonalTransition.{u, v} n m k :=
  iterationGroupEvaluation_unit_transition_whole n m k

/-- The WHOLE original unit square constructs all finite-index diagonal comparison maps. -/
def iterationDiagonalNatTrans (m k : ℕ) : groupIterationDiagramFunctor.{u, v} m k ⟶
    diagonalDiagramFunctor m k where
  app X := NatTrans.ofSequence (fun n => (iterationGroupEvaluationNatIso n m k).hom.app X)
    (fun n => by
      have hu := groupIterationDiagram_map_succ X m k n
      have hd : ((diagonalDiagramFunctor m k).obj X).map (homOfLE (Nat.le_succ n)) =
          (diagonalTransition n m k).app X := diagonalDiagram_map_succ X m k n
      exact (congrArg (fun f => f ≫
          (iterationGroupEvaluationNatIso (n + 1) m k).hom.app X) hu).trans
        ((iterationGroupEvaluation_unit_transition_hom n m k X).trans
          (congrArg (fun f => (iterationGroupEvaluationNatIso n m k).hom.app X ≫ f) hd.symm)))
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    exact (iterationGroupEvaluationNatIso n m k).hom.naturality f

/-- The full diagram Iso uses the SAME original R iteration and every original group shift. -/
def iterationDiagonalNatIso (m k : ℕ) : groupIterationDiagramFunctor.{u, v} m k ≅
    diagonalDiagramFunctor m k :=
  NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun n => (iterationGroupEvaluationNatIso n m k).app X)
    (fun f => ((iterationDiagonalNatTrans m k).app X).naturality f))
    (fun f => by
      apply NatTrans.ext
      funext n
      exact (iterationGroupEvaluationNatIso n m k).hom.naturality f)

/-- The ENTIRE diagonal diagram-Iso hom is the same actual original unit-derived NatTrans. -/
theorem iterationDiagonalNatIso_hom (m k : ℕ) :
    (iterationDiagonalNatIso.{u, v} m k).hom = iterationDiagonalNatTrans m k := rfl

/-- The full component-Iso function is the SAME original evaluated iterate group comparison. -/
theorem iterationDiagonalNatIso_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((iterationDiagonalNatIso m k).app X).app n =
      (iterationGroupEvaluationNatIso n m k).app X := rfl

/-- All actual original finite maps retain the complete forward diagonal comparison square. -/
theorem iterationDiagonalNatIso_hom_index_naturality (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) {i j : ℕ} (f : i ⟶ j) :
    ((groupIterationDiagramFunctor m k).obj X).map f ≫
        (iterationGroupEvaluationNatIso j m k).hom.app X =
      (iterationGroupEvaluationNatIso i m k).hom.app X ≫ (diagonalDiagram X m k).map f :=
  ((iterationDiagonalNatIso m k).hom.app X).naturality f

/-- All actual original finite maps retain the complete inverse diagonal comparison square. -/
theorem iterationDiagonalNatIso_inv_index_naturality (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) {i j : ℕ} (f : i ⟶ j) :
    (diagonalDiagram X m k).map f ≫ (iterationGroupEvaluationNatIso j m k).inv.app X =
      (iterationGroupEvaluationNatIso i m k).inv.app X ≫
        ((groupIterationDiagramFunctor m k).obj X).map f :=
  ((iterationDiagonalNatIso m k).inv.app X).naturality f

/-- Every original spectrum Arrow retains the whole forward diagonal diagram naturality. -/
theorem iterationDiagonalNatIso_hom_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (groupIterationDiagramFunctor m k).map f ≫ (iterationDiagonalNatIso m k).hom.app Y =
      (iterationDiagonalNatIso m k).hom.app X ≫ (diagonalDiagramFunctor m k).map f :=
  (iterationDiagonalNatIso m k).hom.naturality f

/-- Every original spectrum Arrow retains the whole inverse diagonal diagram naturality. -/
theorem iterationDiagonalNatIso_inv_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (diagonalDiagramFunctor m k).map f ≫ (iterationDiagonalNatIso m k).inv.app Y =
      (iterationDiagonalNatIso m k).inv.app X ≫ (groupIterationDiagramFunctor m k).map f :=
  (iterationDiagonalNatIso m k).inv.naturality f

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The SAME original chosen telescope group is the genuine colimit of the ONE actual diagonal. -/
def telescopeDiagonalNatIso (m k : ℕ) : telescopeFunctor.{u, v} ⋙
    PointedCGWH.SequentialSpectrum.evaluation m ⋙ piNPositiveFunctor k ≅
      diagonalDiagramFunctor m k ⋙ GrpCat.FilteredColimits.colimitFunctor :=
  telescopeGroupIterationColimitNatIso m k ≪≫
    Functor.isoWhiskerRight (iterationDiagonalNatIso m k)
      GrpCat.FilteredColimits.colimitFunctor

/-- The entire diagonal comparison hom preserves both actual original component maps. -/
theorem telescopeDiagonalNatIso_hom_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeDiagonalNatIso m k).hom.app X =
      (telescopeGroupIterationColimitNatIso m k).hom.app X ≫
        GrpCat.FilteredColimits.colimitMap ((iterationDiagonalNatIso m k).hom.app X) := rfl

/-- The entire diagonal comparison inv preserves both actual original inverse maps. -/
theorem telescopeDiagonalNatIso_inv_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeDiagonalNatIso m k).inv.app X =
      GrpCat.FilteredColimits.colimitMap ((iterationDiagonalNatIso m k).inv.app X) ≫
        (telescopeGroupIterationColimitNatIso m k).inv.app X := rfl

/-- EVERY actual original MC leg retains its projection, group shift and genuine diagonal leg. -/
theorem telescopeDiagonalNatIso_hom_leg (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (piNPositiveFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap (leg X n) m) ≫
        (telescopeDiagonalNatIso m k).hom.app X =
      (piNPositiveFunctor k).map
          (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m) ≫
        (iterationGroupEvaluationNatIso n m k).hom.app X ≫
          (GrpCat.FilteredColimits.colimitCocone (diagonalDiagram X m k)).ι.app n := by
  let a : (groupIterationDiagramFunctor m k).obj X ⟶ diagonalDiagram X m k :=
    (iterationDiagonalNatIso m k).hom.app X
  have hw := telescopeDiagonalNatIso_hom_app m k X
  have hl := telescopeGroupIterationColimitNatIso_hom_leg m k X n
  have hf := GrpCat.FilteredColimits.colimitMap_ι a n
  exact (congrArg (fun f => (piNPositiveFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap (leg X n) m) ≫ f) hw).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ GrpCat.FilteredColimits.colimitMap a) hl).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun f => (piNPositiveFunctor k).map
            (PointedCGWH.SequentialSpectrum.levelMap ((projection n).app X) m) ≫ f) hf))))

/-- Every original inverse leg retains its group inverse, actual target section and chosen leg. -/
theorem telescopeDiagonalNatIso_inv_section_leg (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (diagonalDiagram X m k)).ι.app (n + 1) ≫
        (telescopeDiagonalNatIso m k).inv.app X =
      (iterationGroupEvaluationNatIso (n + 1) m k).inv.app X ≫
        (piNPositiveFunctor k).map
          (PointedCGWH.SequentialSpectrum.levelMap ((stageSection n).app X) m) ≫
            (piNPositiveFunctor k).map
              (PointedCGWH.SequentialSpectrum.levelMap (leg X (n + 1)) m) := by
  let a : diagonalDiagram X m k ⟶ (groupIterationDiagramFunctor m k).obj X :=
    (iterationDiagonalNatIso m k).inv.app X
  have hw := telescopeDiagonalNatIso_inv_app m k X
  have hf := GrpCat.FilteredColimits.colimitMap_ι a (n + 1)
  have hl := telescopeGroupIterationColimitNatIso_inv_section_leg m k X n
  exact (congrArg (fun f =>
      (GrpCat.FilteredColimits.colimitCocone (diagonalDiagram X m k)).ι.app (n + 1) ≫ f) hw).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ (telescopeGroupIterationColimitNatIso m k).inv.app X) hf).trans
        ((Category.assoc _ _ _).trans (congrArg (fun f => a.app (n + 1) ≫ f) hl))))

/-- Every original spectrum Arrow retains the complete forward telescope/diagonal square. -/
theorem telescopeDiagonalNatIso_hom_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) ≫
          (telescopeDiagonalNatIso m k).hom.app Y =
      (telescopeDiagonalNatIso m k).hom.app X ≫
        GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map f) :=
  (telescopeDiagonalNatIso m k).hom.naturality f

/-- Every original spectrum Arrow retains the complete inverse telescope/diagonal square. -/
theorem telescopeDiagonalNatIso_inv_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map f) ≫
        (telescopeDiagonalNatIso m k).inv.app Y =
      (telescopeDiagonalNatIso m k).inv.app X ≫ (piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) :=
  (telescopeDiagonalNatIso m k).inv.naturality f

/-- The actual positive-tail starting level for any original integer stable degree. -/
def integerTailLevel (q : ℤ) : ℕ := (1 - q).toNat

/-- The actual positive homotopy index for the same original integer degree. -/
def integerTailPositiveIndex (q : ℤ) : ℕ := (q - 1).toNat

omit B in
/-- EVERY original diagonal stage has the same actual integer homotopy-minus-level degree. -/
theorem integerTail_degree (q : ℤ) (n : ℕ) :
    ((integerTailPositiveIndex q + n + 1 : ℕ) : ℤ) -
      ((integerTailLevel q + n : ℕ) : ℤ) = q := by
  simp only [integerTailPositiveIndex, integerTailLevel]
  omega

/-- The SAME ONE diagonal family represents every integer through an actual positive tail. -/
def integerDiagonalDiagramFunctor (q : ℤ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ GrpCat.{v}) :=
  diagonalDiagramFunctor (integerTailLevel q) (integerTailPositiveIndex q)

/-- All original integer degrees retain the complete original telescope comparison maps. -/
def integerTelescopeDiagonalNatIso (q : ℤ) : telescopeFunctor.{u, v} ⋙
    PointedCGWH.SequentialSpectrum.evaluation (integerTailLevel q) ⋙
      piNPositiveFunctor (integerTailPositiveIndex q) ≅
        integerDiagonalDiagramFunctor q ⋙ GrpCat.FilteredColimits.colimitFunctor :=
  telescopeDiagonalNatIso (integerTailLevel q) (integerTailPositiveIndex q)

end PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
