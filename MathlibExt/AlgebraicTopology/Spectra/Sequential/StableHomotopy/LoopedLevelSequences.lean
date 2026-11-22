/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.LoopPowerFiber
import MathlibExt.AlgebraicTopology.Spectra.Sequential.FiberSequence.LevelStructure
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FiberEvaluation

/-!
# Original chosen fibers of every evaluated ordered-loop iteration

The original evaluated-iteration isomorphism, original chosen fiber
evaluation and original loop-power fiber comparison give both maps of the
same chosen fiber at every iteration and level. The original total and zero
projections and whole original iteration-unit squares are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.StrictFiberGeometry (pointObject pointObjectIsTerminal)
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams (zeroTo zeroDiagram)
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
  (chosenFiberComponentIso chosenFiberComponentIso_hom_fst zeroComponentPointIso)
open PointedCGWH.SingularHomotopyGeometry
  (singularFunctor singularPoint_naturality)
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedLevelSequences

open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedFiber
open CategoryTheory.SequentialSpectrum.EnrichedIndex (degree)

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Both original evaluated-iteration maps compare the entire original level arrows. -/
def iterationLevelArrowIso (n m : ℕ) (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Arrow.mk (levelMap ((iterate n).map F.hom) m) ≅
      Arrow.mk ((loopPower n).map (levelMap F.hom (m + n))) :=
  Arrow.isoMk (iterationEvaluationIsoComponent n m F.left)
    (iterationEvaluationIsoComponent n m F.right)
    (iterationEvaluationIso_naturality n m F.hom).symm

/-- The original zero diagram at the actual iterate has its original evaluated point comparison. -/
def iterationZeroPointIso (n m : ℕ) :
    ((iterate.{u, v} n).obj zeroDiagram).level m ≅ pointObject :=
  iterationEvaluationIsoComponent n m zeroDiagram ≪≫
    (loopPower n).mapIso (zeroComponentPointIso (degree PointedCGWH.sphereOne (m + n))) ≪≫
      loopPowerPointIso n

variable {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
  (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)

/-- The full original chosen-fiber comparison uses all four original comparison isomorphisms. -/
def chosenIterationLevelFiberIso (n m : ℕ) :
    ((iterate n).obj c.pt).level m ≅
      PointedCGWH.StrictFiberGeometry.fiber (levelMap ((iterate n).map p) m) :=
  iterationEvaluationIsoComponent n m c.pt ≪≫
    (loopPower n).mapIso (chosenFiberComponentIso
      (degree PointedCGWH.sphereOne (m + n)) p c hc) ≪≫
    loopPowerFiberIso n (Arrow.mk (levelMap p (m + n))) ≪≫
    (PointedCGWH.StrictFiberGeometry.fiberFunctor.mapIso
      (iterationLevelArrowIso n m (Arrow.mk p))).symm

/-- Every entire chosen-iteration comparison preserves the original total projection. -/
theorem chosenIterationLevelFiberIso_hom_fst (n m : ℕ) :
    (chosenIterationLevelFiberIso p c hc n m).hom ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal (levelMap ((iterate n).map p) m) =
      levelMap ((iterate n).map c.fst) m := by
  let a := iterationEvaluationIsoComponent n m c.pt
  let b := chosenFiberComponentIso (degree PointedCGWH.sphereOne (m + n)) p c hc
  let d := loopPowerFiberIso n (Arrow.mk (levelMap p (m + n)))
  let e := iterationLevelArrowIso n m (Arrow.mk p)
  have he : (PointedCGWH.StrictFiberGeometry.fiberFunctor.map e.inv) ≫
      PointedCGWH.StrictFiberGeometry.fiberToTotal (levelMap ((iterate n).map p) m) =
      PointedCGWH.StrictFiberGeometry.fiberToTotal ((loopPower n).map (levelMap p (m + n))) ≫
        (iterationEvaluationIsoComponent n m X).inv :=
    PointedCGWH.StrictFiberGeometry.fiberMap_fst e.inv
  have hd : d.hom ≫
      PointedCGWH.StrictFiberGeometry.fiberToTotal ((loopPower n).map (levelMap p (m + n))) =
      (loopPower n).map (PointedCGWH.StrictFiberGeometry.fiberToTotal (levelMap p (m + n))) :=
    loopPowerFiberIso_hom_fst n (Arrow.mk (levelMap p (m + n)))
  have hb : b.hom ≫ PointedCGWH.StrictFiberGeometry.fiberToTotal (levelMap p (m + n)) =
      levelMap c.fst (m + n) :=
    chosenFiberComponentIso_hom_fst (degree PointedCGWH.sphereOne (m + n)) p c hc
  change (a.hom ≫ (loopPower n).map b.hom ≫ d.hom ≫
    PointedCGWH.StrictFiberGeometry.fiberFunctor.map e.inv) ≫ _ = _
  rw [Category.assoc, Category.assoc, Category.assoc, he,
    ← Category.assoc d.hom, hd, ← Category.assoc ((loopPower n).map b.hom),
    ← (loopPower n).map_comp, hb]
  have ha := iterationEvaluationIso_naturality n m c.fst
  change a.hom ≫ (loopPower n).map (levelMap c.fst (m + n)) ≫
    (iterationEvaluationIsoComponent n m X).inv = _
  rw [← Category.assoc, ← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inverse keeps the same original iterated total projection. -/
theorem chosenIterationLevelFiberIso_inv_fst (n m : ℕ) :
    (chosenIterationLevelFiberIso p c hc n m).inv ≫ levelMap ((iterate n).map c.fst) m =
      PointedCGWH.StrictFiberGeometry.fiberToTotal (levelMap ((iterate n).map p) m) := by
  rw [← chosenIterationLevelFiberIso_hom_fst p c hc n m, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The complete original zero projection is retained through the actual iterated zero-point Iso. -/
theorem chosenIterationLevelFiberIso_hom_snd (n m : ℕ) :
    (chosenIterationLevelFiberIso p c hc n m).hom ≫
        PointedCGWH.StrictFiberGeometry.fiberToPoint (levelMap ((iterate n).map p) m) =
      levelMap ((iterate n).map c.snd) m ≫ (iterationZeroPointIso n m).hom :=
  pointObjectIsTerminal.hom_ext _ _

/-- The entire inverse comparison retains the original zero projection as well. -/
theorem chosenIterationLevelFiberIso_inv_snd (n m : ℕ) :
    (chosenIterationLevelFiberIso p c hc n m).inv ≫
        levelMap ((iterate n).map c.snd) m =
      PointedCGWH.StrictFiberGeometry.fiberToPoint (levelMap ((iterate n).map p) m) ≫
        (iterationZeroPointIso n m).inv := by
  apply (cancel_epi (chosenIterationLevelFiberIso p c hc n m).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
    chosenIterationLevelFiberIso_hom_snd p c hc n m, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Both original iterate units form the actual original total/base level Arrow square. -/
def iterationUnitLevelArrow (n m : ℕ) :
    Arrow.mk (levelMap ((iterate n).map p) m) ⟶
      Arrow.mk (levelMap ((iterate (n + 1)).map p) m) :=
  Arrow.homMk (levelMap ((iterateUnit n).app X) m) (levelMap ((iterateUnit n).app Y) m) (by
    let E : PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.{u, v} := evaluation m
    exact (E.map_comp _ _).symm.trans
      ((E.congr_map (iterateUnit_naturality n p).symm).trans (E.map_comp _ _)))

/-- Every original iteration unit commutes with the complete chosen-fiber comparison. -/
theorem chosenIterationLevelFiberIso_unit (n m : ℕ) :
    levelMap ((iterateUnit n).app c.pt) m ≫
        (chosenIterationLevelFiberIso p c hc (n + 1) m).hom =
      (chosenIterationLevelFiberIso p c hc n m).hom ≫
        PointedCGWH.StrictFiberGeometry.fiberMap (iterationUnitLevelArrow p n m) := by
  apply PullbackCone.IsLimit.hom_ext
    (PointedCGWH.StrictFiberGeometry.fiberConeIsLimit (levelMap ((iterate (n + 1)).map p) m))
  · let d : PointedCGWH.StrictFiberGeometry.fiber (levelMap ((iterate n).map p) m) ⟶
        PointedCGWH.StrictFiberGeometry.fiber (levelMap ((iterate (n + 1)).map p) m) :=
      PointedCGWH.StrictFiberGeometry.fiberMap (iterationUnitLevelArrow p n m)
    have hd : d ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal (levelMap ((iterate (n + 1)).map p) m) =
        PointedCGWH.StrictFiberGeometry.fiberToTotal (levelMap ((iterate n).map p) m) ≫
          levelMap ((iterateUnit n).app X) m :=
      PointedCGWH.StrictFiberGeometry.fiberMap_fst (iterationUnitLevelArrow p n m)
    change (levelMap ((iterateUnit n).app c.pt) m ≫
        (chosenIterationLevelFiberIso p c hc (n + 1) m).hom) ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal (levelMap ((iterate (n + 1)).map p) m) =
      ((chosenIterationLevelFiberIso p c hc n m).hom ≫ d) ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal (levelMap ((iterate (n + 1)).map p) m)
    rw [Category.assoc, chosenIterationLevelFiberIso_hom_fst p c hc (n + 1) m,
      Category.assoc, hd, ← Category.assoc, chosenIterationLevelFiberIso_hom_fst p c hc n m]
    let E : PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.{u, v} := evaluation m
    exact (E.map_comp _ _).symm.trans
      ((E.congr_map (iterateUnit_naturality n c.fst).symm).trans (E.map_comp _ _))
  · exact pointObjectIsTerminal.hom_ext _ _

/-- Every original evaluated loop iterate has the original Serre fibration membership. -/
def iterationLevelFibrationArrow
    (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r)) (n m : ℕ) :
    PointedCGWH.SerreSequenceGeometry.FibrationArrow.{u, v} :=
  ⟨Arrow.mk (levelMap ((iterate n).map p) m),
    ((fibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
      (iterationLevelArrowIso n m (Arrow.mk p))).mpr
        (loopPower_map_fibration n (levelMap p (m + n)) (hp (m + n)))⟩

/-- The original native Serre construction is applied to every actual evaluated loop iterate. -/
def iterationLevelSerreSequence
    (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r)) (n m : ℕ) :
    SSet.FibrationSequence.{v} :=
  PointedCGWH.SerreSequenceGeometry.sequence (iterationLevelFibrationArrow p hp n m)

/-- Both entire original iterate-unit components form the actual singular Serre sequence square. -/
def iterationLevelSerreUnit
    (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r)) (n m : ℕ) :
    SSet.FibrationSequenceHom (iterationLevelSerreSequence p hp n m)
      (iterationLevelSerreSequence p hp (n + 1) m) where
  totalMap := singularFunctor.map (levelMap ((iterateUnit n).app X) m)
  baseMap := singularFunctor.map (levelMap ((iterateUnit n).app Y) m)
  comm := by
    have h := (iterationUnitLevelArrow p n m).w
    exact (singularFunctor.map_comp _ _).symm.trans
      ((singularFunctor.congr_map h).trans (singularFunctor.map_comp _ _))
  total_pt := singularPoint_naturality (levelMap ((iterateUnit n).app X) m)
  base_pt := singularPoint_naturality (levelMap ((iterateUnit n).app Y) m)

/-- The full natural sequence diagram uses the original actual iterate-unit Arrow squares. -/
def loopedSequenceDiagram
    (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r)) (m : ℕ) :
    ℕ ⥤ SSet.FibrationSequence.{v} :=
  Functor.ofSequence (fun n => iterationLevelSerreUnit p hp n m)

/-- Every actual sequence-diagram object is its original evaluated-loop Serre sequence. -/
theorem loopedSequenceDiagram_obj
    (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r)) (m n : ℕ) :
    (loopedSequenceDiagram p hp m).obj n = iterationLevelSerreSequence p hp n m := rfl

/-- Each original successive map is the actual full Serre sequence unit square. -/
theorem loopedSequenceDiagram_map_succ
    (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r)) (m n : ℕ) :
    (loopedSequenceDiagram p hp m).map (homOfLE (Nat.le_succ n)) =
      iterationLevelSerreUnit p hp n m :=
  Functor.ofSequence_map_homOfLE_succ _ n

end PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedLevelSequences
