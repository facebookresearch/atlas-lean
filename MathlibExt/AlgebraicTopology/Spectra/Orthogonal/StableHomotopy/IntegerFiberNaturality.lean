/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerFiberSequence

/-!
# Whole original orthogonal Arrow maps of the looped fiber sequences

Every complete original K-right Arrow square acts on each actual ordered
looped Serre sequence. Its two original components commute with the entire
iteration-unit diagram. The original group functors and their connecting
natural transformation retain the same full source maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.IntegerFiberNaturality

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
  OrthogonalIntegerHomotopy
open PointedCGWH.Spectra.Orthogonal.ChosenFiberTests
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedLevelSequences
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupComparison
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.CubeSingularGeometry
open SSet.FibrationSequence.Geometry
open PointedCGWH.SingularHomotopyGeometry (singularFunctor)

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev C := OrthogonalCarrier.{u, v}
private abbrev iterate (n : ℕ) := PointedCGWH.SequentialSpectrum.OrderedLoop.iterate.{u, v} n
private abbrev evaluation (m : ℕ) := PointedCGWH.SequentialSpectrum.evaluation.{u, v} m

variable {X Y X' Y' : C.{u, v}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
  (hp : (NativeK.generators orthogonalFamily).rlp p)
  (hp' : (NativeK.generators orthogonalFamily).rlp p')

private def evaluatedArrowMap (q : Arrow.mk p ⟶ Arrow.mk p') (n m : ℕ) :
    iterationLevelFibrationArrow (underlyingSequential.map p) (originalLevelFibrations p hp) n m ⟶
      iterationLevelFibrationArrow (underlyingSequential.map p')
        (originalLevelFibrations p' hp') n m := by
  let F : C.{u, v} ⥤ PointedCGWH.{u, v} :=
    underlyingSequential ⋙ iterate n ⋙ evaluation m
  let t : Arrow.mk (F.map p) ⟶ Arrow.mk (F.map p') :=
    Arrow.homMk (F.map q.left) (F.map q.right) (by
      exact (F.map_comp _ _).symm.trans
        ((F.congr_map q.w).trans (F.map_comp _ _)))
  exact ⟨t⟩

/-- Every actual original Arrow square gives its full evaluated-loop
singular Serre sequence square. -/
def sequenceMap (q : Arrow.mk p ⟶ Arrow.mk p') (n m : ℕ) :
    iterationLevelSerreSequence (underlyingSequential.map p) (originalLevelFibrations p hp) n m ⟶
      iterationLevelSerreSequence (underlyingSequential.map p')
        (originalLevelFibrations p' hp') n m :=
  PointedCGWH.SerreSequenceGeometry.sequenceMap (evaluatedArrowMap hp hp' q n m)

/-- The entire original total component retains its actual native source map. -/
theorem sequenceMap_total (q : Arrow.mk p ⟶ Arrow.mk p') (n m : ℕ) :
    (sequenceMap hp hp' q n m).totalMap =
      singularFunctor.map ((evaluation m).map
        ((iterate n).map (underlyingSequential.map q.left))) :=
  rfl

/-- The entire original base component retains its actual native source map. -/
theorem sequenceMap_base (q : Arrow.mk p ⟶ Arrow.mk p') (n m : ℕ) :
    (sequenceMap hp hp' q n m).baseMap =
      singularFunctor.map ((evaluation m).map
        ((iterate n).map (underlyingSequential.map q.right))) :=
  rfl

/-- Both complete original Arrow components commute with every actual
iteration-unit square before taking any homotopy group. -/
theorem sequenceMap_unit (q : Arrow.mk p ⟶ Arrow.mk p') (n m : ℕ) :
    sequenceMap hp hp' q n m ≫
        iterationLevelSerreUnit (underlyingSequential.map p') (originalLevelFibrations p' hp') n m =
      iterationLevelSerreUnit (underlyingSequential.map p) (originalLevelFibrations p hp) n m ≫
        sequenceMap hp hp' q (n + 1) m := by
  apply SSet.FibrationSequence.Geometry.hom_ext
  · change singularFunctor.map ((evaluation m).map ((iterate n).map
        (underlyingSequential.map q.left))) ≫
      singularFunctor.map ((evaluation m).map
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app
          (underlyingSequential.obj X'))) =
      singularFunctor.map ((evaluation m).map
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app
          (underlyingSequential.obj X))) ≫
      singularFunctor.map ((evaluation m).map ((iterate (n + 1)).map
        (underlyingSequential.map q.left)))
    have h := (evaluation m).congr_map
      (PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit_naturality n
        (underlyingSequential.map q.left))
    simp only [Functor.map_comp] at h
    exact (singularFunctor.map_comp _ _).symm.trans
      ((singularFunctor.congr_map h).trans (singularFunctor.map_comp _ _))
  · change singularFunctor.map ((evaluation m).map ((iterate n).map
        (underlyingSequential.map q.right))) ≫
      singularFunctor.map ((evaluation m).map
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app
          (underlyingSequential.obj Y'))) =
      singularFunctor.map ((evaluation m).map
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app
          (underlyingSequential.obj Y))) ≫
      singularFunctor.map ((evaluation m).map ((iterate (n + 1)).map
        (underlyingSequential.map q.right)))
    have h := (evaluation m).congr_map
      (PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit_naturality n
        (underlyingSequential.map q.right))
    simp only [Functor.map_comp] at h
    exact (singularFunctor.map_comp _ _).symm.trans
      ((singularFunctor.congr_map h).trans (singularFunctor.map_comp _ _))

/-- All actual evaluated-loop sequence maps form one whole natural
transformation on the same original unbounded iteration diagram. -/
def sequenceDiagramMap (q : Arrow.mk p ⟶ Arrow.mk p') (m : ℕ) :
    loopedSequenceDiagram (underlyingSequential.map p) (originalLevelFibrations p hp) m ⟶
      loopedSequenceDiagram (underlyingSequential.map p') (originalLevelFibrations p' hp') m :=
  NatTrans.ofSequence (fun n => sequenceMap hp hp' q n m)
    (fun n => by
      rw [loopedSequenceDiagram_map_succ, loopedSequenceDiagram_map_succ]
      exact (sequenceMap_unit hp hp' q n m).symm)

/-- Every entire original total-space group diagram map comes from the
original total component of that whole sequence transformation. -/
def totalGroupMap (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    loopedTotalGroupDiagram (underlyingSequential.map p) (originalLevelFibrations p hp) m k ⟶
      loopedTotalGroupDiagram (underlyingSequential.map p') (originalLevelFibrations p' hp') m k :=
  Functor.whiskerRight (sequenceDiagramMap hp hp' q m) (totalGroupFunctor k)

/-- Every entire original base-space group diagram map comes from its
unchanged original base component. -/
def baseGroupMap (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    loopedBaseGroupDiagram (underlyingSequential.map p) (originalLevelFibrations p hp) m k ⟶
      loopedBaseGroupDiagram (underlyingSequential.map p') (originalLevelFibrations p' hp') m k :=
  Functor.whiskerRight (sequenceDiagramMap hp hp' q m) (baseGroupFunctor k)

/-- Every entire original singular fiber-group map is that of the same
whole original source transformation. -/
def fiberGroupMap (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    loopedFiberGroupDiagram (underlyingSequential.map p) (originalLevelFibrations p hp) m k ⟶
      loopedFiberGroupDiagram (underlyingSequential.map p') (originalLevelFibrations p' hp') m k :=
  Functor.whiskerRight (sequenceDiagramMap hp hp' q m) (fiberGroupFunctor k)

/-- Every full original total component commutes with both complete
iteration/cube group comparison functions. -/
theorem totalGroupComparison_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    (groupIterationDiagramFunctor m k).map (underlyingSequential.map q.left) ≫
        (loopedTotalGroupNatIso (underlyingSequential.map p')
          (originalLevelFibrations p' hp') m k).hom =
      (loopedTotalGroupNatIso (underlyingSequential.map p)
        (originalLevelFibrations p hp) m k).hom ≫ totalGroupMap hp hp' q m k := by
  apply NatTrans.ext
  funext n
  exact (cubePositiveSingularNatIso k).hom.naturality
    ((evaluation m).map ((iterate n).map (underlyingSequential.map q.left)))

/-- Every original base component retains the same whole comparison
square before the connecting morphism is applied. -/
theorem baseGroupComparison_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    (groupIterationDiagramFunctor m k).map (underlyingSequential.map q.right) ≫
        (loopedBaseGroupNatIso (underlyingSequential.map p')
          (originalLevelFibrations p' hp') m k).hom =
      (loopedBaseGroupNatIso (underlyingSequential.map p)
        (originalLevelFibrations p hp) m k).hom ≫ baseGroupMap hp hp' q m k := by
  apply NatTrans.ext
  funext n
  exact (cubePositiveSingularNatIso k).hom.naturality
    ((evaluation m).map ((iterate n).map (underlyingSequential.map q.right)))

/-- All original connecting group functions are natural under every
whole original orthogonal Arrow square. -/
theorem connectingGroupMap_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    baseGroupMap hp hp' q m (k + 1) ≫
        loopedConnectingGroupMap (underlyingSequential.map p')
          (originalLevelFibrations p' hp') m k =
      loopedConnectingGroupMap (underlyingSequential.map p) (originalLevelFibrations p hp) m k ≫
        fiberGroupMap hp hp' q m k := by
  apply NatTrans.ext
  funext n
  exact (connectingGroupNatTrans k).naturality ((sequenceDiagramMap hp hp' q m).app n)

/-- The same original connecting quotient maps retain every complete
original Arrow square after taking the actual group colimit. -/
theorem connectingColimitMap_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    GrpCat.FilteredColimits.colimitMap (baseGroupMap hp hp' q m (k + 1)) ≫
        GrpCat.FilteredColimits.colimitMap
          (loopedConnectingGroupMap (underlyingSequential.map p')
            (originalLevelFibrations p' hp') m k) =
      GrpCat.FilteredColimits.colimitMap
          (loopedConnectingGroupMap (underlyingSequential.map p)
            (originalLevelFibrations p hp) m k) ≫
        GrpCat.FilteredColimits.colimitMap (fiberGroupMap hp hp' q m k) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  exact (Q.map_comp _ _).symm.trans
    ((Q.congr_map (connectingGroupMap_naturality hp hp' q m k)).trans (Q.map_comp _ _))

end PointedCGWH.Spectra.Orthogonal.IntegerFiberNaturality
