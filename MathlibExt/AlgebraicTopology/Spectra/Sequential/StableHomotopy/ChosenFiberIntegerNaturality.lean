/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ChosenFiberIntegerSequence
import MathlibExt.AlgebraicTopology.Spectra.Sequential.FiberSequence.LevelStructure

/-!
# Naturality of chosen-fiber integer connecting maps

For a square between level fibrations of sequential spectra and chosen limiting fibers, constructs the induced maps of looped fibration sequences and their homotopy-group diagrams. The integer connecting maps commute with both the base map and the chosen fiber map, and are compatible with changing the chosen limiting fiber.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory Simplicial

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerNaturality

open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedLevelSequences
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupSequence
open PointedCGWH.SequentialSpectrum.FibrationSequenceStructureGeometry
open PointedCGWH.SerreSequenceGeometry
open PointedCGWH.SingularHomotopyGeometry (singularFunctor singularPoint_naturality)

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {X Y X' Y' : PointedCGWH.SequentialSpectrum.{u, v}}
  (p : X ⟶ Y) (p' : X' ⟶ Y')
  (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r))
  (hp' : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p' r))
  (a : Arrow.mk p ⟶ Arrow.mk p')

/-- Every full original spectrum square gives both actual evaluated iteration maps. -/
def iterationArrow (n m : ℕ) :
    Arrow.mk (levelMap ((iterate n).map p) m) ⟶
      Arrow.mk (levelMap ((iterate n).map p') m) :=
  (evaluation m).mapArrow.map ((iterate n).mapArrow.map a)

/-- The actual native Serre functor retains the full original iteration square. -/
def iterationSequenceMap (n m : ℕ) :
    SSet.FibrationSequenceHom (iterationLevelSerreSequence p hp n m)
      (iterationLevelSerreSequence p' hp' n m) :=
  sequenceMap (ObjectProperty.homMk (iterationArrow p p' a n m))

/-- Its complete total function is the original evaluated iteration of the source component. -/
theorem iterationSequenceMap_total (n m : ℕ) :
    (iterationSequenceMap p p' hp hp' a n m).totalMap =
      singularFunctor.map (levelMap ((iterate n).map a.left) m) := rfl

/-- Its complete base function is the original evaluated iteration of the target component. -/
theorem iterationSequenceMap_base (n m : ℕ) :
    (iterationSequenceMap p p' hp hp' a n m).baseMap =
      singularFunctor.map (levelMap ((iterate n).map a.right) m) := rfl

/-- Both original iterate-unit functions commute with every complete sequence square. -/
theorem iterationSequenceMap_unit (n m : ℕ) :
    SSet.FibrationSequenceHom.comp (iterationLevelSerreUnit p hp n m)
        (iterationSequenceMap p p' hp hp' a (n + 1) m) =
      SSet.FibrationSequenceHom.comp (iterationSequenceMap p p' hp hp' a n m)
        (iterationLevelSerreUnit p' hp' n m) := by
  apply SSet.FibrationSequence.Geometry.hom_ext
  · change singularFunctor.map (levelMap ((iterateUnit n).app X) m) ≫
        singularFunctor.map (levelMap ((iterate (n + 1)).map a.left) m) =
      singularFunctor.map (levelMap ((iterate n).map a.left) m) ≫
        singularFunctor.map (levelMap ((iterateUnit n).app X') m)
    let E : PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.{u, v} := evaluation m
    have h : E.map ((iterateUnit n).app X) ≫ E.map ((iterate (n + 1)).map a.left) =
        E.map ((iterate n).map a.left) ≫ E.map ((iterateUnit n).app X') :=
      (E.map_comp _ _).symm.trans
        ((E.congr_map (iterateUnit_naturality n a.left).symm).trans (E.map_comp _ _))
    exact (singularFunctor.map_comp _ _).symm.trans
      ((singularFunctor.congr_map h).trans (singularFunctor.map_comp _ _))
  · change singularFunctor.map (levelMap ((iterateUnit n).app Y) m) ≫
        singularFunctor.map (levelMap ((iterate (n + 1)).map a.right) m) =
      singularFunctor.map (levelMap ((iterate n).map a.right) m) ≫
        singularFunctor.map (levelMap ((iterateUnit n).app Y') m)
    let E : PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.{u, v} := evaluation m
    have h : E.map ((iterateUnit n).app Y) ≫ E.map ((iterate (n + 1)).map a.right) =
        E.map ((iterate n).map a.right) ≫ E.map ((iterateUnit n).app Y') :=
      (E.map_comp _ _).symm.trans
        ((E.congr_map (iterateUnit_naturality n a.right).symm).trans (E.map_comp _ _))
    exact (singularFunctor.map_comp _ _).symm.trans
      ((singularFunctor.congr_map h).trans (singularFunctor.map_comp _ _))

/-- All nonadjacent iteration maps retain the same complete original spectrum square. -/
def sequenceDiagramMap (m : ℕ) : loopedSequenceDiagram p hp m ⟶
    loopedSequenceDiagram p' hp' m :=
  NatTrans.ofSequence (fun n => iterationSequenceMap p p' hp hp' a n m) (fun n => by
    rw [loopedSequenceDiagram_map_succ, loopedSequenceDiagram_map_succ]
    exact iterationSequenceMap_unit p p' hp hp' a n m)

/-- Every original source square has its same next-degree base group diagram map. -/
def baseGroupDiagramMap (m k : ℕ) : loopedBaseGroupDiagram p hp m k ⟶
    loopedBaseGroupDiagram p' hp' m k :=
  Functor.whiskerRight (sequenceDiagramMap p p' hp hp' a m)
    (SSet.FibrationSequence.Geometry.baseGroupFunctor k)

/-- Every original source square has its same chosen sequence fiber group diagram map. -/
def fiberGroupDiagramMap (m k : ℕ) : loopedFiberGroupDiagram p hp m k ⟶
    loopedFiberGroupDiagram p' hp' m k :=
  Functor.whiskerRight (sequenceDiagramMap p p' hp hp' a m)
    (SSet.FibrationSequence.Geometry.fiberGroupFunctor k)

/-- The full original connecting map is natural on every looped sequence and coefficient stage. -/
theorem connectingGroup_square (m k : ℕ) :
    baseGroupDiagramMap p p' hp hp' a m (k + 1) ≫ loopedConnectingGroupMap p' hp' m k =
      loopedConnectingGroupMap p hp m k ≫ fiberGroupDiagramMap p p' hp hp' a m k := by
  apply NatTrans.ext
  funext n
  exact (SSet.FibrationSequence.Geometry.connectingGroupNatTrans k).naturality
    (iterationSequenceMap p p' hp hp' a n m)

open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams (zeroTo)
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupComparison
open PointedCGWH.CubeSingularGeometry

variable (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
  (d : PullbackCone p' (zeroTo Y')) (hd : IsLimit d)

/-- Both complete chosen-fiber comparison functions preserve the whole original spectrum square. -/
theorem chosenLoopedFiberIso_naturality (n m : ℕ) :
    singularFunctor.map (levelMap ((iterate n).map (chosenFiberMap a c d hd)) m) ≫
        (chosenLoopedSequenceFiberIso p' hp' m d hd n).hom =
      (chosenLoopedSequenceFiberIso p hp m c hc n).hom ≫
        (iterationSequenceMap p p' hp hp' a n m).fiberMap := by
  let E : PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.{u, v} := evaluation m
  have h : E.map ((iterate n).map (chosenFiberMap a c d hd)) ≫
      E.map ((iterate n).map d.fst) =
    E.map ((iterate n).map c.fst) ≫ E.map ((iterate n).map a.left) :=
    (E.map_comp _ _).symm.trans
      ((E.congr_map ((iterate n).map_comp _ _).symm).trans
        ((E.congr_map ((iterate n).congr_map (chosenFiberMap_fst a c d hd))).trans
          ((E.congr_map ((iterate n).map_comp _ _)).trans (E.map_comp _ _))))
  apply (cancel_mono (iterationLevelSerreSequence p' hp' n m).fiberIncl).mp
  have hLeft :
      (singularFunctor.map (levelMap ((iterate n).map (chosenFiberMap a c d hd)) m) ≫
          (chosenLoopedSequenceFiberIso p' hp' m d hd n).hom) ≫
        (iterationLevelSerreSequence p' hp' n m).fiberIncl =
      singularFunctor.map (levelMap ((iterate n).map c.fst) m) ≫
        singularFunctor.map (levelMap ((iterate n).map a.left) m) := by
    rw [Category.assoc, chosenLoopedSequenceFiberIso_hom_projection p' hp' m d hd n]
    change singularFunctor.map (E.map ((iterate n).map (chosenFiberMap a c d hd))) ≫
        singularFunctor.map (E.map ((iterate n).map d.fst)) =
      singularFunctor.map (E.map ((iterate n).map c.fst)) ≫
        singularFunctor.map (E.map ((iterate n).map a.left))
    exact (singularFunctor.map_comp _ _).symm.trans
      ((singularFunctor.congr_map h).trans (singularFunctor.map_comp _ _))
  have hRight :
      ((chosenLoopedSequenceFiberIso p hp m c hc n).hom ≫
        (iterationSequenceMap p p' hp hp' a n m).fiberMap) ≫
          (iterationLevelSerreSequence p' hp' n m).fiberIncl =
      singularFunctor.map (levelMap ((iterate n).map c.fst) m) ≫
        singularFunctor.map (levelMap ((iterate n).map a.left) m) := by
    rw [Category.assoc, SSet.FibrationSequenceHom.fiberMap_ι, ← Category.assoc,
      chosenLoopedSequenceFiberIso_hom_projection p hp m c hc n,
      iterationSequenceMap_total]
  exact hLeft.trans hRight.symm

/-- The original positive cube comparison retains all caller-fiber and spectrum-map data. -/
theorem chosenLoopedFiberMulEquiv_naturality (m k n : ℕ)
    (x : PointedCGWH.piN (k + 1) (((iterate n).obj c.pt).level m)) :
    chosenLoopedFiberMulEquiv p' hp' m k d hd n
        (PointedCGWH.piNMap (k + 1)
          (levelMap ((iterate n).map (chosenFiberMap a c d hd)) m) x) =
      SSet.KanComplex.π.map (iterationSequenceMap p p' hp hp' a n m).fiberMap
        (iterationSequenceMap p p' hp hp' a n m).fiberMap_app_basePoint (k + 1)
          (chosenLoopedFiberMulEquiv p hp m k c hc n x) := by
  change SSet.KanComplex.π.map (chosenLoopedSequenceFiberIso p' hp' m d hd n).hom
      (chosenLoopedSequenceFiberIso_hom_point p' hp' m d hd n) (k + 1)
        (cubeSingularMulEquiv k (((iterate n).obj d.pt).level m)
          (PointedCGWH.piNMap (k + 1)
            (levelMap ((iterate n).map (chosenFiberMap a c d hd)) m) x)) = _
  rw [cubeSingularMulEquiv_naturality]
  exact SSet.KanComplex.π.map_square
    (chosenLoopedSequenceFiberIso p hp m c hc n).hom
    (chosenLoopedSequenceFiberIso p' hp' m d hd n).hom
    (singularFunctor.map (levelMap ((iterate n).map (chosenFiberMap a c d hd)) m))
    (iterationSequenceMap p p' hp hp' a n m).fiberMap
    (chosenLoopedFiberIso_naturality p p' hp hp' a c hc d hd n m)
    (chosenLoopedSequenceFiberIso_hom_point p hp m c hc n)
    (chosenLoopedSequenceFiberIso_hom_point p' hp' m d hd n)
    (singularPoint_naturality (levelMap ((iterate n).map (chosenFiberMap a c d hd)) m))
    (iterationSequenceMap p p' hp hp' a n m).fiberMap_app_basePoint (k + 1)
    (cubeSingularMulEquiv k (((iterate n).obj c.pt).level m) x)

open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.DiagonalFiberSequence

/-- The complete original looped fiber comparison is natural in every caller's fiber square. -/
theorem loopedFiberGroupNatIso_naturality (m k : ℕ) :
    (groupIterationDiagramFunctor m k).map (chosenFiberMap a c d hd) ≫
        (loopedFiberGroupNatIso p' hp' m k d hd).hom =
      (loopedFiberGroupNatIso p hp m k c hc).hom ≫
        fiberGroupDiagramMap p p' hp hp' a m k := by
  apply NatTrans.ext
  funext n
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  change chosenLoopedFiberMulEquiv p' hp' m k d hd n
      ((PointedCGWH.piNPositiveMap k
        (levelMap ((iterate n).map (chosenFiberMap a c d hd)) m)).hom x) =
    SSet.KanComplex.π.map (iterationSequenceMap p p' hp hp' a n m).fiberMap
      (iterationSequenceMap p p' hp hp' a n m).fiberMap_app_basePoint (k + 1)
        (chosenLoopedFiberMulEquiv p hp m k c hc n x)
  rw [PointedCGWH.piNPositiveMap_apply]
  exact chosenLoopedFiberMulEquiv_naturality p p' hp hp' a c hc d hd m k n x

/-- The complete original looped base comparison retains the full original target component. -/
theorem loopedBaseGroupNatIso_naturality (m k : ℕ) :
    (groupIterationDiagramFunctor m k).map a.right ≫ (loopedBaseGroupNatIso p' hp' m k).hom =
      (loopedBaseGroupNatIso p hp m k).hom ≫ baseGroupDiagramMap p p' hp hp' a m k := by
  apply NatTrans.ext
  funext n
  exact (cubePositiveSingularNatIso k).hom.naturality (levelMap ((iterate n).map a.right) m)

/-- Both original diagonal fiber functions preserve every source square and selected fiber. -/
theorem diagonalFiberGroupNatIso_naturality (m k : ℕ) :
    (diagonalDiagramFunctor m k).map (chosenFiberMap a c d hd) ≫
        (diagonalFiberGroupNatIso p' d hd hp' m k).hom =
      (diagonalFiberGroupNatIso p c hc hp m k).hom ≫
        fiberGroupDiagramMap p p' hp hp' a m k := by
  change (diagonalDiagramFunctor m k).map (chosenFiberMap a c d hd) ≫
      ((iterationDiagonalNatIso m k).inv.app d.pt ≫
        (loopedFiberGroupNatIso p' hp' m k d hd).hom) =
    ((iterationDiagonalNatIso m k).inv.app c.pt ≫
      (loopedFiberGroupNatIso p hp m k c hc).hom) ≫ _
  rw [← Category.assoc, (iterationDiagonalNatIso m k).inv.naturality,
    Category.assoc, loopedFiberGroupNatIso_naturality p p' hp hp' a c hc d hd m k,
    ← Category.assoc]

/-- Both full original diagonal base functions preserve every original target component. -/
theorem diagonalBaseGroupNatIso_naturality (m k : ℕ) :
    (diagonalDiagramFunctor m k).map a.right ≫ (diagonalBaseGroupNatIso p' hp' m k).hom =
      (diagonalBaseGroupNatIso p hp m k).hom ≫ baseGroupDiagramMap p p' hp hp' a m k := by
  change (diagonalDiagramFunctor m k).map a.right ≫
      ((iterationDiagonalNatIso m k).inv.app Y' ≫ (loopedBaseGroupNatIso p' hp' m k).hom) =
    ((iterationDiagonalNatIso m k).inv.app Y ≫ (loopedBaseGroupNatIso p hp m k).hom) ≫ _
  let i := (iterationDiagonalNatIso m k).inv.app Y
  let j := (iterationDiagonalNatIso m k).inv.app Y'
  let f := (diagonalDiagramFunctor m k).map a.right
  let g := (groupIterationDiagramFunctor m k).map a.right
  let e := (loopedBaseGroupNatIso p hp m k).hom
  let e' := (loopedBaseGroupNatIso p' hp' m k).hom
  let b := baseGroupDiagramMap p p' hp hp' a m k
  have hi : f ≫ j = i ≫ g := (iterationDiagonalNatIso m k).inv.naturality a.right
  have he : g ≫ e' = e ≫ b := loopedBaseGroupNatIso_naturality p p' hp hp' a m k
  change f ≫ (j ≫ e') = (i ≫ e) ≫ b
  calc
    _ = (f ≫ j) ≫ e' := (Category.assoc f j e').symm
    _ = (i ≫ g) ≫ e' := congrArg (fun z => z ≫ e') hi
    _ = i ≫ (g ≫ e') := Category.assoc i g e'
    _ = i ≫ (e ≫ b) := congrArg (fun z => i ≫ z) he
    _ = (i ≫ e) ≫ b := (Category.assoc i e b).symm

/-- The original chosen fiber quotient comparison preserves the same whole original square. -/
theorem diagonalFiberColimitIso_naturality (m k : ℕ) :
    GrpCat.FilteredColimits.colimitMap
        ((diagonalDiagramFunctor m k).map (chosenFiberMap a c d hd)) ≫
      (diagonalFiberColimitIso p' d hd hp' m k).hom =
    (diagonalFiberColimitIso p c hc hp m k).hom ≫
      GrpCat.FilteredColimits.colimitMap (fiberGroupDiagramMap p p' hp hp' a m k) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  exact (Q.map_comp _ _).symm.trans
    ((Q.congr_map (diagonalFiberGroupNatIso_naturality p p' hp hp' a c hc d hd m k)).trans
      (Q.map_comp _ _))

/-- The original target quotient comparison retains the full original target component. -/
theorem diagonalBaseColimitIso_naturality (m k : ℕ) :
    GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map a.right) ≫
        (diagonalBaseColimitIso p' hp' m k).hom =
      (diagonalBaseColimitIso p hp m k).hom ≫
        GrpCat.FilteredColimits.colimitMap (baseGroupDiagramMap p p' hp hp' a m k) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  exact (Q.map_comp _ _).symm.trans
    ((Q.congr_map (diagonalBaseGroupNatIso_naturality p p' hp hp' a m k)).trans
      (Q.map_comp _ _))

/-- The same complete original diagonal connecting map is natural in every caller-fiber square. -/
theorem diagonalConnectingMap_naturality (m k : ℕ) :
    GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m (k + 1)).map a.right) ≫
        diagonalConnectingMap p' d hd hp' m k =
      diagonalConnectingMap p c hc hp m k ≫ GrpCat.FilteredColimits.colimitMap
        ((diagonalDiagramFunctor m k).map (chosenFiberMap a c d hd)) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  let eb := diagonalBaseColimitIso p hp m (k + 1)
  let eb' := diagonalBaseColimitIso p' hp' m (k + 1)
  let ef := diagonalFiberColimitIso p c hc hp m k
  let ef' := diagonalFiberColimitIso p' d hd hp' m k
  let b := Q.map ((diagonalDiagramFunctor m (k + 1)).map a.right)
  let f := Q.map ((diagonalDiagramFunctor m k).map (chosenFiberMap a c d hd))
  let lb := Q.map (baseGroupDiagramMap p p' hp hp' a m (k + 1))
  let lf := Q.map (fiberGroupDiagramMap p p' hp hp' a m k)
  let delta := diagonalConnectingMap p c hc hp m k
  let delta' := diagonalConnectingMap p' d hd hp' m k
  let lc := Q.map (loopedConnectingGroupMap p hp m k)
  let lc' := Q.map (loopedConnectingGroupMap p' hp' m k)
  have hb : b ≫ eb'.hom = eb.hom ≫ lb :=
    diagonalBaseColimitIso_naturality p p' hp hp' a m (k + 1)
  have hf : f ≫ ef'.hom = ef.hom ≫ lf :=
    diagonalFiberColimitIso_naturality p p' hp hp' a c hc d hd m k
  have hdelta : delta ≫ ef.hom = eb.hom ≫ lc :=
    diagonalConnectingMap_reconstruction p c hc hp m k
  have hdelta' : delta' ≫ ef'.hom = eb'.hom ≫ lc' :=
    diagonalConnectingMap_reconstruction p' d hd hp' m k
  have hl : lb ≫ lc' = lc ≫ lf :=
    (Q.map_comp _ _).symm.trans
      ((Q.congr_map (connectingGroup_square p p' hp hp' a m k)).trans (Q.map_comp _ _))
  apply (cancel_mono ef'.hom).mp
  change (b ≫ delta') ≫ ef'.hom = (delta ≫ f) ≫ ef'.hom
  calc
    _ = b ≫ (delta' ≫ ef'.hom) := Category.assoc b delta' ef'.hom
    _ = b ≫ (eb'.hom ≫ lc') := congrArg (fun z => b ≫ z) hdelta'
    _ = (b ≫ eb'.hom) ≫ lc' := (Category.assoc b eb'.hom lc').symm
    _ = (eb.hom ≫ lb) ≫ lc' := congrArg (fun z => z ≫ lc') hb
    _ = eb.hom ≫ (lb ≫ lc') := Category.assoc eb.hom lb lc'
    _ = eb.hom ≫ (lc ≫ lf) := congrArg (fun z => eb.hom ≫ z) hl
    _ = (eb.hom ≫ lc) ≫ lf := (Category.assoc eb.hom lc lf).symm
    _ = (delta ≫ ef.hom) ≫ lf := congrArg (fun z => z ≫ lf) hdelta.symm
    _ = delta ≫ (ef.hom ≫ lf) := Category.assoc delta ef.hom lf
    _ = delta ≫ (f ≫ ef'.hom) := congrArg (fun z => delta ≫ z) hf.symm
    _ = (delta ≫ f) ≫ ef'.hom := (Category.assoc delta f ef'.hom).symm

open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
open PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerSequence
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry

/-- The original normalized connection preserves every full source and chosen-fiber square. -/
theorem normalizedConnecting_naturality (m k : ℕ) :
    (integerStablePiFunctor (integerDegree m k + 1)).map a.right ≫
        normalizedConnecting p' d hd hp' m k =
      normalizedConnecting p c hc hp m k ≫
        (integerStablePiFunctor (integerDegree m k)).map (chosenFiberMap a c d hd) := by
  let b := (integerStablePiFunctor (integerDegree m k + 1)).map a.right
  let f := (integerStablePiFunctor (integerDegree m k)).map (chosenFiberMap a c d hd)
  let bd := (diagonalColimitFunctor m (k + 1)).map a.right
  let fd := (diagonalColimitFunctor m k).map (chosenFiberMap a c d hd)
  let u := (sourceNormalization m k).inv.app Y
  let v := (sourceNormalization m k).inv.app Y'
  let e := (integerColimitNatIso m k).hom.app c.pt
  let e' := (integerColimitNatIso m k).hom.app d.pt
  let delta := diagonalConnectingMap p c hc hp m k
  let delta' := diagonalConnectingMap p' d hd hp' m k
  have hb : b ≫ v = u ≫ bd := (sourceNormalization m k).inv.naturality a.right
  have hdelta : bd ≫ delta' = delta ≫ fd :=
    diagonalConnectingMap_naturality p p' hp hp' a c hc d hd m k
  have hf : fd ≫ e' = e ≫ f := (integerColimitNatIso m k).hom.naturality (chosenFiberMap a c d hd)
  change b ≫ (v ≫ delta' ≫ e') = (u ≫ delta ≫ e) ≫ f
  calc
    _ = (b ≫ v) ≫ (delta' ≫ e') := (Category.assoc b v (delta' ≫ e')).symm
    _ = (u ≫ bd) ≫ (delta' ≫ e') := congrArg (fun z => z ≫ (delta' ≫ e')) hb
    _ = u ≫ ((bd ≫ delta') ≫ e') :=
      (Category.assoc u bd (delta' ≫ e')).trans
        (congrArg (fun z => u ≫ z) (Category.assoc bd delta' e').symm)
    _ = u ≫ ((delta ≫ fd) ≫ e') := congrArg (fun z => u ≫ (z ≫ e')) hdelta
    _ = u ≫ (delta ≫ (fd ≫ e')) := congrArg (fun z => u ≫ z) (Category.assoc delta fd e')
    _ = u ≫ (delta ≫ (e ≫ f)) := congrArg (fun z => u ≫ (delta ≫ z)) hf
    _ = (u ≫ delta ≫ e) ≫ f :=
      (congrArg (fun z => u ≫ z) (Category.assoc delta e f).symm).trans
        (Category.assoc u (delta ≫ e) f).symm

/-- Every actual integer successor connection is natural on full original spectrum squares. -/
theorem connectingPlusOne_naturality (q : ℤ) :
    (integerStablePiFunctor (q + 1)).map a.right ≫ connectingPlusOne p' d hd hp' q =
      connectingPlusOne p c hc hp q ≫
        (integerStablePiFunctor q).map (chosenFiberMap a c d hd) := by
  let m := integerTailLevel q
  let k := integerTailPositiveIndex q
  let b := (integerStablePiFunctor (q + 1)).map a.right
  let f := (integerStablePiFunctor q).map (chosenFiberMap a c d hd)
  let bd := (integerStablePiFunctor (integerDegree m k + 1)).map a.right
  let fd := (integerStablePiFunctor (integerDegree m k)).map (chosenFiberMap a c d hd)
  let u := (sourceDegreeIso q).inv.app Y
  let v := (sourceDegreeIso q).inv.app Y'
  let e := (targetDegreeIso q).hom.app c.pt
  let e' := (targetDegreeIso q).hom.app d.pt
  let delta := normalizedConnecting p c hc hp m k
  let delta' := normalizedConnecting p' d hd hp' m k
  have hb : b ≫ v = u ≫ bd := (sourceDegreeIso q).inv.naturality a.right
  have hn : bd ≫ delta' = delta ≫ fd :=
    normalizedConnecting_naturality p p' hp hp' a c hc d hd m k
  have hf : fd ≫ e' = e ≫ f := (targetDegreeIso q).hom.naturality (chosenFiberMap a c d hd)
  change b ≫ (v ≫ delta' ≫ e') = (u ≫ delta ≫ e) ≫ f
  calc
    _ = (b ≫ v) ≫ (delta' ≫ e') := (Category.assoc b v (delta' ≫ e')).symm
    _ = (u ≫ bd) ≫ (delta' ≫ e') := congrArg (fun z => z ≫ (delta' ≫ e')) hb
    _ = u ≫ ((bd ≫ delta') ≫ e') :=
      (Category.assoc u bd (delta' ≫ e')).trans
        (congrArg (fun z => u ≫ z) (Category.assoc bd delta' e').symm)
    _ = u ≫ ((delta ≫ fd) ≫ e') := congrArg (fun z => u ≫ (z ≫ e')) hn
    _ = u ≫ (delta ≫ (fd ≫ e')) := congrArg (fun z => u ≫ z) (Category.assoc delta fd e')
    _ = u ≫ (delta ≫ (e ≫ f)) := congrArg (fun z => u ≫ (delta ≫ z)) hf
    _ = (u ≫ delta ≫ e) ≫ f :=
      (congrArg (fun z => u ≫ z) (Category.assoc delta e f).symm).trans
        (Category.assoc u (delta ≫ e) f).symm

/-- All integer q-to-q-1 maps retain the same original full source and chosen-fiber naturality. -/
theorem connecting_naturality (q : ℤ) :
    (integerStablePiFunctor q).map a.right ≫ connecting p' d hd hp' q =
      connecting p c hc hp q ≫
        (integerStablePiFunctor (q - 1)).map (chosenFiberMap a c d hd) := by
  let e : integerStablePiFunctor ((q - 1) + 1) ≅ integerStablePiFunctor q :=
    eqToIso (congrArg integerStablePiFunctor (show (q - 1) + 1 = q by omega))
  let delta := connectingPlusOne p c hc hp (q - 1)
  let delta' := connectingPlusOne p' d hd hp' (q - 1)
  have hn := connectingPlusOne_naturality p p' hp hp' a c hc d hd (q - 1)
  change (integerStablePiFunctor q).map a.right ≫ (e.inv.app Y' ≫ delta') =
    (e.inv.app Y ≫ delta) ≫
      (integerStablePiFunctor (q - 1)).map (chosenFiberMap a c d hd)
  let b := (integerStablePiFunctor q).map a.right
  let bd := (integerStablePiFunctor ((q - 1) + 1)).map a.right
  let f := (integerStablePiFunctor (q - 1)).map (chosenFiberMap a c d hd)
  have hcast : b ≫ e.inv.app Y' = e.inv.app Y ≫ bd := e.inv.naturality a.right
  change b ≫ (e.inv.app Y' ≫ delta') = (e.inv.app Y ≫ delta) ≫ f
  calc
    _ = (b ≫ e.inv.app Y') ≫ delta' := (Category.assoc b (e.inv.app Y') delta').symm
    _ = (e.inv.app Y ≫ bd) ≫ delta' := congrArg (fun z => z ≫ delta') hcast
    _ = e.inv.app Y ≫ (bd ≫ delta') := Category.assoc (e.inv.app Y) bd delta'
    _ = e.inv.app Y ≫ (delta ≫ f) := congrArg (fun z => e.inv.app Y ≫ z) hn
    _ = (e.inv.app Y ≫ delta) ≫ f := (Category.assoc (e.inv.app Y) delta f).symm

/-- The same original integer connection is independent of the caller's full fiber choice. -/
theorem connecting_choice (e : PullbackCone p (zeroTo Y)) (he : IsLimit e) (q : ℤ) :
    connecting p e he hp q = connecting p c hc hp q ≫
      (integerStablePiFunctor (q - 1)).map (chosenFiberMap (𝟙 (Arrow.mk p)) c e he) := by
  have h := connecting_naturality p p hp hp (𝟙 (Arrow.mk p)) c hc e he q
  change (integerStablePiFunctor q).map (𝟙 Y) ≫ connecting p e he hp q =
    connecting p c hc hp q ≫
      (integerStablePiFunctor (q - 1)).map (chosenFiberMap (𝟙 (Arrow.mk p)) c e he) at h
  have hi : (integerStablePiFunctor q).map (𝟙 Y) = 𝟙 _ :=
    (integerStablePiFunctor q).map_id Y
  exact (Category.id_comp (connecting p e he hp q)).symm.trans
    ((congrArg (fun z => z ≫ connecting p e he hp q) hi.symm).trans h)

/-- The inverse choice direction retains the same original integer connecting map. -/
theorem connecting_choice_inverse (e : PullbackCone p (zeroTo Y)) (he : IsLimit e) (q : ℤ) :
    connecting p c hc hp q = connecting p e he hp q ≫
      (integerStablePiFunctor (q - 1)).map (chosenFiberMap (𝟙 (Arrow.mk p)) e c hc) :=
  connecting_choice p hp e he c hc q

end PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerNaturality
