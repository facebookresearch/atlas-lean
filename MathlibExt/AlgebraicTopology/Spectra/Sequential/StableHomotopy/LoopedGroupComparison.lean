/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.LoopedGroupSequence
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.DiagonalHomotopy
import MathlibExt.Topology.Category.PointedCGWH.Singular.CubeHomotopyComparison

/-!
# The original cube-group comparisons of the looped Serre diagrams

The actual original cube/singular natural group isomorphism compares the
total and base diagrams with the existing ordered iteration group diagrams.
The original projection maps and every original iteration unit are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupComparison

open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedLevelSequences
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupSequence
open PointedCGWH.CubeSingularGeometry
open PointedCGWH.SerreSequenceGeometry
open PointedCGWH.SingularHomotopyGeometry
  (singularFunctor singularPoint singularPoint_naturality)
open SSet.FibrationSequence.Geometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
  (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r)) (m k : ℕ)

/-- Both actual total-group comparison functions are the original cube/singular functions. -/
def loopedTotalGroupNatIso :
    (groupIterationDiagramFunctor m k).obj X ≅ loopedTotalGroupDiagram p hp m k := by
  let e : ∀ n, ((groupIterationDiagramFunctor m k).obj X).obj n ≅
      (loopedTotalGroupDiagram p hp m k).obj n :=
    fun n => (cubeSingularMulEquiv k (((iterate n).obj X).level m)).toGrpIso
  let t : (groupIterationDiagramFunctor m k).obj X ⟶ loopedTotalGroupDiagram p hp m k :=
    NatTrans.ofSequence (fun n => (e n).hom) (fun n => by
      rw [groupIterationDiagram_map_succ]
      rw [show (loopedTotalGroupDiagram p hp m k).map (homOfLE (Nat.le_succ n)) =
          (totalGroupFunctor k).map (iterationLevelSerreUnit p hp n m) from
        (totalGroupFunctor k).congr_map (loopedSequenceDiagram_map_succ p hp m n)]
      change (PointedCGWH.piNPositiveFunctor k).map (levelMap ((iterateUnit n).app X) m) ≫
          (e (n + 1)).hom =
        (e n).hom ≫ (totalGroupFunctor k).map (iterationLevelSerreUnit p hp n m)
      exact (cubePositiveSingularNatIso k).hom.naturality
        (levelMap ((iterateUnit n).app X) m))
  exact NatIso.ofComponents e (fun f => t.naturality f)

/-- Both actual base-group comparison functions are the original cube/singular functions. -/
def loopedBaseGroupNatIso :
    (groupIterationDiagramFunctor m k).obj Y ≅ loopedBaseGroupDiagram p hp m k := by
  let e : ∀ n, ((groupIterationDiagramFunctor m k).obj Y).obj n ≅
      (loopedBaseGroupDiagram p hp m k).obj n :=
    fun n => (cubeSingularMulEquiv k (((iterate n).obj Y).level m)).toGrpIso
  let t : (groupIterationDiagramFunctor m k).obj Y ⟶ loopedBaseGroupDiagram p hp m k :=
    NatTrans.ofSequence (fun n => (e n).hom) (fun n => by
      rw [groupIterationDiagram_map_succ]
      rw [show (loopedBaseGroupDiagram p hp m k).map (homOfLE (Nat.le_succ n)) =
          (baseGroupFunctor k).map (iterationLevelSerreUnit p hp n m) from
        (baseGroupFunctor k).congr_map (loopedSequenceDiagram_map_succ p hp m n)]
      change (PointedCGWH.piNPositiveFunctor k).map (levelMap ((iterateUnit n).app Y) m) ≫
          (e (n + 1)).hom =
        (e n).hom ≫ (baseGroupFunctor k).map (iterationLevelSerreUnit p hp n m)
      exact (cubePositiveSingularNatIso k).hom.naturality
        (levelMap ((iterateUnit n).app Y) m))
  exact NatIso.ofComponents e (fun f => t.naturality f)

/-- The whole original projection diagram map commutes with both full group comparison maps. -/
theorem loopedProjectionGroup_square :
    (groupIterationDiagramFunctor m k).map p ≫ (loopedBaseGroupNatIso p hp m k).hom =
      (loopedTotalGroupNatIso p hp m k).hom ≫ loopedProjectionGroupMap p hp m k := by
  apply NatTrans.ext
  funext n
  exact (cubePositiveSingularNatIso k).hom.naturality (levelMap ((iterate n).map p) m)

variable (c : PullbackCone p (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroTo Y))
  (hc : IsLimit c)

/-- Both actual singular fiber functions retain the original chosen evaluated loop fiber. -/
def chosenLoopedSequenceFiberIso (n : ℕ) :
    singularFunctor.obj (((iterate n).obj c.pt).level m) ≅
      (iterationLevelSerreSequence p hp n m).fiber :=
  singularFunctor.mapIso (chosenIterationLevelFiberIso p c hc n m) ≪≫
    nativeFiberSingularIso (iterationLevelFibrationArrow p hp n m)

/-- The full forward comparison retains the original selected fiber point. -/
theorem chosenLoopedSequenceFiberIso_hom_point (n : ℕ) :
    (chosenLoopedSequenceFiberIso p hp m c hc n).hom.app _
        (singularPoint (((iterate n).obj c.pt).level m)) =
      (iterationLevelSerreSequence p hp n m).fiberPoint :=
  (congrArg ((nativeFiberSingularIso (iterationLevelFibrationArrow p hp n m)).hom.app _)
    (singularPoint_naturality (chosenIterationLevelFiberIso p c hc n m).hom)).trans
      (nativeFiberSingularIso_hom_point (iterationLevelFibrationArrow p hp n m))

/-- The full inverse comparison retains that same original fiber point. -/
theorem chosenLoopedSequenceFiberIso_inv_point (n : ℕ) :
    (chosenLoopedSequenceFiberIso p hp m c hc n).inv.app _
        (iterationLevelSerreSequence p hp n m).fiberPoint =
      singularPoint (((iterate n).obj c.pt).level m) := by
  rw [← chosenLoopedSequenceFiberIso_hom_point p hp m c hc n]
  exact ConcreteCategory.congr_hom
    (congr_app (chosenLoopedSequenceFiberIso p hp m c hc n).hom_inv_id _) _

/-- The complete singular comparison preserves the original iterated total projection. -/
theorem chosenLoopedSequenceFiberIso_hom_projection (n : ℕ) :
    (chosenLoopedSequenceFiberIso p hp m c hc n).hom ≫
        (iterationLevelSerreSequence p hp n m).fiberIncl =
      singularFunctor.map (levelMap ((iterate n).map c.fst) m) := by
  let F := iterationLevelFibrationArrow p hp n m
  let d := (chosenIterationLevelFiberIso p c hc n m).hom
  let g : singularFunctor.obj (PointedCGWH.StrictFiberGeometry.fiber
        (levelMap ((iterate n).map p) m)) ⟶ (iterationLevelSerreSequence p hp n m).fiber :=
    (nativeFiberSingularIso F).hom
  have hNative : g ≫ (iterationLevelSerreSequence p hp n m).fiberIncl =
      singularFunctor.map (PointedCGWH.StrictFiberGeometry.fiberToTotal
        (levelMap ((iterate n).map p) m)) := nativeFiberSingularIso_hom_projection F
  change (singularFunctor.map d ≫ g) ≫ _ = _
  rw [Category.assoc, hNative, ← singularFunctor.map_comp]
  exact singularFunctor.congr_map (chosenIterationLevelFiberIso_hom_fst p c hc n m)

/-- Every original unit square is retained before applying any homotopy group shift. -/
theorem chosenLoopedSequenceFiberIso_unit (n : ℕ) :
    singularFunctor.map (levelMap ((iterateUnit n).app c.pt) m) ≫
        (chosenLoopedSequenceFiberIso p hp m c hc (n + 1)).hom =
      (chosenLoopedSequenceFiberIso p hp m c hc n).hom ≫
        (iterationLevelSerreUnit p hp n m).fiberMap := by
  let E : PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.{u, v} := evaluation m
  have h : levelMap ((iterateUnit n).app c.pt) m ≫
      levelMap ((iterate (n + 1)).map c.fst) m =
      levelMap ((iterate n).map c.fst) m ≫ levelMap ((iterateUnit n).app X) m :=
    (E.map_comp _ _).symm.trans
      ((E.congr_map (iterateUnit_naturality n c.fst).symm).trans (E.map_comp _ _))
  apply (cancel_mono (iterationLevelSerreSequence p hp (n + 1) m).fiberIncl).mp
  have hLeft :
      (singularFunctor.map (levelMap ((iterateUnit n).app c.pt) m) ≫
        (chosenLoopedSequenceFiberIso p hp m c hc (n + 1)).hom) ≫
          (iterationLevelSerreSequence p hp (n + 1) m).fiberIncl =
      singularFunctor.map (levelMap ((iterate n).map c.fst) m) ≫
        singularFunctor.map (levelMap ((iterateUnit n).app X) m) := by
    rw [Category.assoc, chosenLoopedSequenceFiberIso_hom_projection p hp m c hc (n + 1),
      ← singularFunctor.map_comp, h, singularFunctor.map_comp]
  have hRight :
      ((chosenLoopedSequenceFiberIso p hp m c hc n).hom ≫
        (iterationLevelSerreUnit p hp n m).fiberMap) ≫
          (iterationLevelSerreSequence p hp (n + 1) m).fiberIncl =
      singularFunctor.map (levelMap ((iterate n).map c.fst) m) ≫
        (iterationLevelSerreUnit p hp n m).totalMap := by
    rw [Category.assoc, SSet.FibrationSequenceHom.fiberMap_ι, ← Category.assoc,
      chosenLoopedSequenceFiberIso_hom_projection p hp m c hc n]
  exact hLeft.trans hRight.symm

/-- Every original positive cube fiber group has both actual looped
sequence comparison functions. -/
def chosenLoopedFiberMulEquiv (n : ℕ) :
    PointedCGWH.piN (k + 1) (((iterate n).obj c.pt).level m) ≃*
      SSet.KanComplex.π (k + 1) (iterationLevelSerreSequence p hp n m).fiber
        (iterationLevelSerreSequence p hp n m).fiberPoint :=
  (cubeSingularMulEquiv k (((iterate n).obj c.pt).level m)).trans
    { toEquiv := SSet.KanComplex.π.equivOfIso (chosenLoopedSequenceFiberIso p hp m c hc n)
        (chosenLoopedSequenceFiberIso_hom_point p hp m c hc n) (k + 1)
      map_mul' := SSet.KanComplex.π.map_mul (chosenLoopedSequenceFiberIso p hp m c hc n).hom
        (chosenLoopedSequenceFiberIso_hom_point p hp m c hc n) k }

/-- The full cube comparison retains the original singular unit square at every iteration. -/
theorem chosenLoopedFiberMulEquiv_unit (n : ℕ)
    (x : PointedCGWH.piN (k + 1) (((iterate n).obj c.pt).level m)) :
    chosenLoopedFiberMulEquiv p hp m k c hc (n + 1)
        (PointedCGWH.piNMap (k + 1) (levelMap ((iterateUnit n).app c.pt) m) x) =
      SSet.KanComplex.π.map (iterationLevelSerreUnit p hp n m).fiberMap
        (iterationLevelSerreUnit p hp n m).fiberMap_app_basePoint (k + 1)
          (chosenLoopedFiberMulEquiv p hp m k c hc n x) :=
  (congrArg (SSet.KanComplex.π.map
      (chosenLoopedSequenceFiberIso p hp m c hc (n + 1)).hom
      (chosenLoopedSequenceFiberIso_hom_point p hp m c hc (n + 1)) (k + 1))
    (cubeSingularMulEquiv_naturality k (levelMap ((iterateUnit n).app c.pt) m) x)).trans
    (SSet.KanComplex.π.map_square
      (chosenLoopedSequenceFiberIso p hp m c hc n).hom
      (chosenLoopedSequenceFiberIso p hp m c hc (n + 1)).hom
      (singularFunctor.map (levelMap ((iterateUnit n).app c.pt) m))
      (iterationLevelSerreUnit p hp n m).fiberMap
      (chosenLoopedSequenceFiberIso_unit p hp m c hc n)
      (chosenLoopedSequenceFiberIso_hom_point p hp m c hc n)
      (chosenLoopedSequenceFiberIso_hom_point p hp m c hc (n + 1))
      (singularPoint_naturality (levelMap ((iterateUnit n).app c.pt) m))
      (iterationLevelSerreUnit p hp n m).fiberMap_app_basePoint (k + 1) _)

/-- The entire chosen-fiber cube comparison preserves the original iterated inclusion map. -/
theorem chosenLoopedFiberMulEquiv_inclusion (n : ℕ)
    (x : PointedCGWH.piN (k + 1) (((iterate n).obj c.pt).level m)) :
    SSet.KanComplex.π.map (iterationLevelSerreSequence p hp n m).fiberIncl rfl (k + 1)
        (chosenLoopedFiberMulEquiv p hp m k c hc n x) =
      cubeSingularMulEquiv k (((iterate n).obj X).level m)
        (PointedCGWH.piNMap (k + 1) (levelMap ((iterate n).map c.fst) m) x) := by
  have hPoint :
      ((chosenLoopedSequenceFiberIso p hp m c hc n).hom ≫
        (iterationLevelSerreSequence p hp n m).fiberIncl).app _
          (singularPoint (((iterate n).obj c.pt).level m)) =
      (iterationLevelSerreSequence p hp n m).e :=
    congrArg ((iterationLevelSerreSequence p hp n m).fiberIncl.app _)
      (chosenLoopedSequenceFiberIso_hom_point p hp m c hc n)
  have h := SSet.KanComplex.π.map_comp_apply
    (chosenLoopedSequenceFiberIso p hp m c hc n).hom
    (iterationLevelSerreSequence p hp n m).fiberIncl
    (chosenLoopedSequenceFiberIso_hom_point p hp m c hc n) rfl hPoint
    (cubeSingularMulEquiv k (((iterate n).obj c.pt).level m) x)
  exact h.symm.trans ((congrFun (SSet.KanComplex.π.map_congr
    (chosenLoopedSequenceFiberIso_hom_projection p hp m c hc n) _ _ (k + 1)) _).trans
      (cubeSingularMulEquiv_naturality k (levelMap ((iterate n).map c.fst) m) x).symm)

/-- Both full chosen-fiber diagram maps are natural in every original loop iteration. -/
def loopedFiberGroupNatIso :
    (groupIterationDiagramFunctor m k).obj c.pt ≅ loopedFiberGroupDiagram p hp m k := by
  let e : ∀ n, ((groupIterationDiagramFunctor m k).obj c.pt).obj n ≅
      (loopedFiberGroupDiagram p hp m k).obj n :=
    fun n => (chosenLoopedFiberMulEquiv p hp m k c hc n).toGrpIso
  let t : (groupIterationDiagramFunctor m k).obj c.pt ⟶ loopedFiberGroupDiagram p hp m k :=
    NatTrans.ofSequence (fun n => (e n).hom) (fun n => by
      rw [groupIterationDiagram_map_succ]
      rw [show (loopedFiberGroupDiagram p hp m k).map (homOfLE (Nat.le_succ n)) =
          (fiberGroupFunctor k).map (iterationLevelSerreUnit p hp n m) from
        (fiberGroupFunctor k).congr_map (loopedSequenceDiagram_map_succ p hp m n)]
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      change chosenLoopedFiberMulEquiv p hp m k c hc (n + 1)
          ((PointedCGWH.piNPositiveMap k (levelMap ((iterateUnit n).app c.pt) m)).hom x) =
        SSet.KanComplex.π.map (iterationLevelSerreUnit p hp n m).fiberMap
          (iterationLevelSerreUnit p hp n m).fiberMap_app_basePoint (k + 1)
            (chosenLoopedFiberMulEquiv p hp m k c hc n x)
      rw [PointedCGWH.piNPositiveMap_apply]
      exact chosenLoopedFiberMulEquiv_unit p hp m k c hc n x)
  exact NatIso.ofComponents e (fun f => t.naturality f)

/-- The complete original iterated fiber inclusion keeps both full comparison functions. -/
theorem loopedInclusionGroup_square :
    (groupIterationDiagramFunctor m k).map c.fst ≫ (loopedTotalGroupNatIso p hp m k).hom =
      (loopedFiberGroupNatIso p hp m k c hc).hom ≫ loopedInclusionGroupMap p hp m k := by
  apply NatTrans.ext
  funext n
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  change cubeSingularMulEquiv k (((iterate n).obj X).level m)
      ((PointedCGWH.piNPositiveMap k (levelMap ((iterate n).map c.fst) m)).hom x) =
    SSet.KanComplex.π.map (iterationLevelSerreSequence p hp n m).fiberIncl rfl (k + 1)
      (chosenLoopedFiberMulEquiv p hp m k c hc n x)
  rw [PointedCGWH.piNPositiveMap_apply]
  exact (chosenLoopedFiberMulEquiv_inclusion p hp m k c hc n x).symm

end PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupComparison
