/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.SerreSequence.Loop
import MathlibExt.AlgebraicTopology.Spectra.Sequential.HomotopyStructure

/-!
# The complete original level fibration sequence structure squares

The actual spectrum adjoint structure maps give a natural transformation
on the entire original spectrum Arrow category. Its components are both
literal adjoint structure maps and its square is the original spectrum
map naturality. Restriction to Arrows whose every actual level map is a
native pointed fibration retains every entire original spectrum square.
The same original native singular sequence functor then yields the actual
full sequence structure map at every level, with both singular maps and
both original point equations.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed Simplicial

namespace PointedCGWH.SequentialSpectrum.FibrationSequenceStructureGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

open PointedCGWH.SerreSequenceGeometry

/-- All complete original spectrum Arrows have their actual original level Arrow functor. -/
def originalLevelArrowFunctor (n : ℕ) :
    Arrow PointedCGWH.SequentialSpectrum.{u, v} ⥤ Arrow PointedCGWH.{u, v} :=
  (PointedCGWH.SequentialSpectrum.evaluation n).mapArrow

/-- All complete original successor level Arrows are followed by the actual native loop functor. -/
def originalLoopedLevelArrowFunctor (n : ℕ) :
    Arrow PointedCGWH.SequentialSpectrum.{u, v} ⥤ Arrow PointedCGWH.{u, v} :=
  originalLevelArrowFunctor (n + 1) ⋙ PointedCGWH.loop.mapArrow

/-- Every original spectrum Arrow has its literal total/base adjoint structure square. -/
def originalAdjointLevelArrow (n : ℕ) (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (originalLevelArrowFunctor n).obj F ⟶ (originalLoopedLevelArrowFunctor n).obj F :=
  Arrow.homMk (PointedCGWH.SequentialSpectrum.adjointStructureMap F.left n)
    (PointedCGWH.SequentialSpectrum.adjointStructureMap F.right n)
    (PointedCGWH.SequentialSpectrum.adjointStructureMap_naturality F.hom n).symm

/-- The complete total component is the SAME original spectrum adjoint structure map. -/
theorem originalAdjointLevelArrow_left (n : ℕ)
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (originalAdjointLevelArrow n F).left =
      PointedCGWH.SequentialSpectrum.adjointStructureMap F.left n := rfl

/-- The complete base component is the SAME original spectrum adjoint structure map. -/
theorem originalAdjointLevelArrow_right (n : ℕ)
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (originalAdjointLevelArrow n F).right =
      PointedCGWH.SequentialSpectrum.adjointStructureMap F.right n := rfl

/-- Every original structure square is the exact original map naturality on full components. -/
theorem originalAdjointLevelArrow_square (n : ℕ)
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (originalAdjointLevelArrow n F).left ≫
        PointedCGWH.loop.map (PointedCGWH.SequentialSpectrum.levelMap F.hom (n + 1)) =
      PointedCGWH.SequentialSpectrum.levelMap F.hom n ≫
        (originalAdjointLevelArrow n F).right :=
  (PointedCGWH.SequentialSpectrum.adjointStructureMap_naturality F.hom n).symm

/-- The whole original spectrum Arrow category retains every adjoint structure square. -/
def originalAdjointLevelArrowNatTrans (n : ℕ) :
    originalLevelArrowFunctor.{u, v} n ⟶ originalLoopedLevelArrowFunctor n where
  app := originalAdjointLevelArrow n
  naturality {F G} q := by
    apply Arrow.hom_ext _ _
    · exact PointedCGWH.SequentialSpectrum.adjointStructureMap_naturality q.left n
    · exact PointedCGWH.SequentialSpectrum.adjointStructureMap_naturality q.right n

/-- The original full property requires precisely native pointed fibrations at all actual levels. -/
def originalSpectrumLevelFibrationProperty :
    ObjectProperty (Arrow PointedCGWH.SequentialSpectrum.{u, v}) :=
  fun F => ∀ n : ℕ,
    fibrations PointedCGWH.{u, v} (PointedCGWH.SequentialSpectrum.levelMap F.hom n)

/-- All actual level fibration Arrows retain every whole original spectrum square. -/
abbrev OriginalSpectrumLevelFibrationArrow :=
  (originalSpectrumLevelFibrationProperty.{u, v}).FullSubcategory

/-- The full inclusion retains the same original spectrum Arrow and complete map. -/
def originalSpectrumArrowFunctor :
    OriginalSpectrumLevelFibrationArrow.{u, v} ⥤ Arrow PointedCGWH.SequentialSpectrum.{u, v} :=
  originalSpectrumLevelFibrationProperty.ι

/-- The original level evaluation lifts to the whole native pointed fibration Arrow category. -/
def originalLevelFibrationFunctor (n : ℕ) :
    OriginalSpectrumLevelFibrationArrow.{u, v} ⥤ FibrationArrow.{u, v} :=
  fibrationArrowProperty.lift (originalSpectrumArrowFunctor ⋙ originalLevelArrowFunctor n)
    (fun F => F.property n)

/-- Each full lifted level map is the literal original spectrum level map. -/
theorem originalLevelFibrationFunctor_obj_hom (n : ℕ)
    (F : OriginalSpectrumLevelFibrationArrow.{u, v}) :
    ((originalLevelFibrationFunctor n).obj F).obj.hom =
      PointedCGWH.SequentialSpectrum.levelMap F.obj.hom n := rfl

/-- Each lifted square retains the whole actual original evaluated spectrum Arrow. -/
theorem originalLevelFibrationFunctor_map (n : ℕ)
    {F G : OriginalSpectrumLevelFibrationArrow.{u, v}} (q : F ⟶ G) :
    ((originalLevelFibrationFunctor n).map q).hom =
      (originalLevelArrowFunctor n).map q.hom := rfl

/-- The original successor evaluation and actual loop fibration lift form the full looped
functor. -/
def originalLoopedLevelFibrationFunctor (n : ℕ) :
    OriginalSpectrumLevelFibrationArrow.{u, v} ⥤ FibrationArrow.{u, v} :=
  originalLevelFibrationFunctor (n + 1) ⋙ loopFibrationArrowFunctor

/-- The SAME whole adjoint Arrow transformation lifts using the actual original fibration proofs. -/
def originalAdjointLevelFibrationNatTrans (n : ℕ) :
    originalLevelFibrationFunctor.{u, v} n ⟶ originalLoopedLevelFibrationFunctor n where
  app F := ObjectProperty.homMk (originalAdjointLevelArrow n F.obj)
  naturality {F G} q := by
    apply ObjectProperty.hom_ext
    exact (originalAdjointLevelArrowNatTrans n).naturality q.hom

/-- Every full lifted structure square is the original unrestricted total/base structure square. -/
theorem originalAdjointLevelFibrationNatTrans_app_hom (n : ℕ)
    (F : OriginalSpectrumLevelFibrationArrow.{u, v}) :
    ((originalAdjointLevelFibrationNatTrans n).app F).hom =
      originalAdjointLevelArrow n F.obj := rfl

/-- The same original native sequence functor is applied to every original level fibration. -/
def originalLevelSequenceFunctor (n : ℕ) :
    OriginalSpectrumLevelFibrationArrow.{u, v} ⥤ SSet.FibrationSequence.{v} :=
  originalLevelFibrationFunctor n ⋙ sequenceFunctor

/-- The same original native sequence functor is applied to every actual looped successor map. -/
def originalLoopedLevelSequenceFunctor (n : ℕ) :
    OriginalSpectrumLevelFibrationArrow.{u, v} ⥤ SSet.FibrationSequence.{v} :=
  originalLoopedLevelFibrationFunctor n ⋙ sequenceFunctor

/-- Each actual original spectrum gives the full original sequence structure square. -/
def originalLevelSequenceStructureNatTrans (n : ℕ) :
    originalLevelSequenceFunctor.{u, v} n ⟶ originalLoopedLevelSequenceFunctor n :=
  Functor.whiskerRight (originalAdjointLevelFibrationNatTrans n) sequenceFunctor

/-- The whole original sequence structure square has its literal original total singular map. -/
theorem originalLevelSequenceStructureNatTrans_total (n : ℕ)
    (F : OriginalSpectrumLevelFibrationArrow.{u, v}) :
    ((originalLevelSequenceStructureNatTrans n).app F).totalMap =
      underlyingSingularFunctor.map
        (PointedCGWH.SequentialSpectrum.adjointStructureMap F.obj.left n).right := rfl

/-- The whole original sequence structure square has its literal original base singular map. -/
theorem originalLevelSequenceStructureNatTrans_base (n : ℕ)
    (F : OriginalSpectrumLevelFibrationArrow.{u, v}) :
    ((originalLevelSequenceStructureNatTrans n).app F).baseMap =
      underlyingSingularFunctor.map
        (PointedCGWH.SequentialSpectrum.adjointStructureMap F.obj.right n).right := rfl

/-- The full total singular structure map preserves the exact original chosen total point. -/
theorem originalLevelSequenceStructureNatTrans_total_point (n : ℕ)
    (F : OriginalSpectrumLevelFibrationArrow.{u, v}) :
    ((originalLevelSequenceStructureNatTrans n).app F).totalMap.app _
        ((originalLevelSequenceFunctor n).obj F).e =
      ((originalLoopedLevelSequenceFunctor n).obj F).e :=
  ((originalLevelSequenceStructureNatTrans n).app F).total_pt

/-- The full base singular structure map preserves the exact original chosen base point. -/
theorem originalLevelSequenceStructureNatTrans_base_point (n : ℕ)
    (F : OriginalSpectrumLevelFibrationArrow.{u, v}) :
    ((originalLevelSequenceStructureNatTrans n).app F).baseMap.app _
        ((originalLevelSequenceFunctor n).obj F).b =
      ((originalLoopedLevelSequenceFunctor n).obj F).b :=
  ((originalLevelSequenceStructureNatTrans n).app F).base_pt

/-- Every complete original spectrum square commutes with the entire sequence structure map. -/
theorem originalLevelSequenceStructureNatTrans_naturality (n : ℕ)
    {F G : OriginalSpectrumLevelFibrationArrow.{u, v}} (q : F ⟶ G) :
    (originalLevelSequenceFunctor n).map q ≫
        (originalLevelSequenceStructureNatTrans n).app G =
      (originalLevelSequenceStructureNatTrans n).app F ≫
        (originalLoopedLevelSequenceFunctor n).map q :=
  (originalLevelSequenceStructureNatTrans n).naturality q

/-- The actual entire induced fiber map retains the original singular total projection square. -/
theorem originalLevelSequenceStructureNatTrans_fiber_projection (n : ℕ)
    (F : OriginalSpectrumLevelFibrationArrow.{u, v}) :
    ((originalLevelSequenceStructureNatTrans n).app F).fiberMap ≫
        ((originalLoopedLevelSequenceFunctor n).obj F).fiberIncl =
      ((originalLevelSequenceFunctor n).obj F).fiberIncl ≫
        ((originalLevelSequenceStructureNatTrans n).app F).totalMap :=
  SSet.FibrationSequenceHom.fiberMap_ι ((originalLevelSequenceStructureNatTrans n).app F)

/-- The whole original induced fiber map preserves its exact original chosen singular fiber
point. -/
theorem originalLevelSequenceStructureNatTrans_fiber_point (n : ℕ)
    (F : OriginalSpectrumLevelFibrationArrow.{u, v}) :
    ((originalLevelSequenceStructureNatTrans n).app F).fiberMap.app _
        ((originalLevelSequenceFunctor n).obj F).fiberPoint =
      ((originalLoopedLevelSequenceFunctor n).obj F).fiberPoint :=
  SSet.FibrationSequenceHom.fiberMap_app_basePoint
    ((originalLevelSequenceStructureNatTrans n).app F)

end PointedCGWH.SequentialSpectrum.FibrationSequenceStructureGeometry
