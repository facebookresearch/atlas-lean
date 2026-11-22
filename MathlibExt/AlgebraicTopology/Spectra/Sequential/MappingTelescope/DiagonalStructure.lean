/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredColimits.Successor
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.GroupEvaluationTail
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.HomotopyStructureSquares

/-!
# ENTIRE original diagonal tail diagrams and actual sigma structure squares

The SAME original R units commute with the actual ordered R functor.
Native group loop-shift naturality therefore constructs the full finite-
index one-loop diagram Iso. The whole original G successor/tail identity
identifies the complete diagonal successor-index Iso with BOTH literal
original arithmetic maps. The actual original diagonal sigma transition
then gives a full structure diagram, identified on EVERY original stage.
Its genuine Group colimit map preserves BOTH original telescope structure
comparison directions. No desired finite-index or sigma/colimit law,
alternative diagonal, source/model/Arrow or coefficient replacement is data.
Weakness/Omega and original forward8.8 remain later proof obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

private theorem originalCancelTailWord
    {C : Type uC} [Category.{vC} C] {A B D E : C}
    (s : A ≅ B) (e : B ≅ D) (g : A ⟶ E) (t : D ⟶ E)
    (h : g = s.hom ≫ e.hom ≫ t) : e.inv ≫ s.inv ≫ g = t := by
  rw [h, ← Category.assoc s.inv s.hom (e.hom ≫ t), Iso.inv_hom_id,
    Category.id_comp, ← Category.assoc e.inv e.hom t, Iso.inv_hom_id, Category.id_comp]

private theorem originalRightIndexSquare
    {C : Type uC} [Category.{vC} C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ E) (d : E ⟶ F) (i : D ≅ F)
    (h : a ≫ b ≫ i.hom = c ≫ d) : a ≫ b = c ≫ (d ≫ i.inv) := by
  apply (cancel_mono i.hom).mp
  rw [Category.assoc, h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem originalInverseStructureSquare
    {C : Type uC} [Category.{vC} C] {A B D E : C}
    (e : A ≅ D) (f : B ≅ E) (a : A ⟶ B) (b : D ⟶ E)
    (h : a ≫ f.hom = e.hom ≫ b) : b ≫ f.inv = e.inv ≫ a := by
  apply (cancel_mono f.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, h,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalStructureGeometry
open GrpCat.FilteredColimits.Successor
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.HomotopyStructureColimitGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.GroupEvaluationTailGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The SAME original R units are actual loop maps at EVERY original level. -/
theorem iterateUnit_successor_loop_levelMap (n m : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit (n + 1)).app X) m =
      PointedCGWH.loop.map
        (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) (m + 1)) := by
  have h : (iterateUnit (n + 1)).app X = functor.map ((iterateUnit n).app X) :=
    (iterateUnit_app (n + 1) X).trans
      ((functor_map_unit ((iterate n).obj X)).symm.trans
        (congrArg functor.map (iterateUnit_app n X).symm))
  exact (congrArg (fun f => PointedCGWH.SequentialSpectrum.levelMap f m) h).trans
    (functor_map_levelMap ((iterateUnit n).app X) m)

/-- The full original R iteration shifted by one keeps the SAME full original group diagram. -/
def shiftedGroupIterationDiagramFunctor (m k : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ GrpCat.{v}) := groupIterationDiagramFunctor m k ⋙ successorDiagramFunctor

/-- Every complete shifted original R step is the actual original next iterate unit. -/
theorem shiftedGroupIterationDiagram_map_succ (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((shiftedGroupIterationDiagramFunctor m k).obj X).map (homOfLE (Nat.le_succ n)) =
      (piNPositiveFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit (n + 1)).app X) m) :=
  groupIterationDiagram_map_succ X m k (n + 1)

/-- Genuine loop-shift naturality constructs the ENTIRE original one-loop diagram comparison. -/
def loopShiftDiagramNatTrans (m k : ℕ) : shiftedGroupIterationDiagramFunctor.{u, v} m k ⟶
    groupIterationDiagramFunctor (m + 1) (k + 1) where
  app X := NatTrans.ofSequence (fun n => (iterationNativeGroupShiftNatIso n m k).hom.app X)
    (fun n => by
      have hu := (piNPositiveFunctor k).congr_map
        (iterateUnit_successor_loop_levelMap n m X)
      let g := PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) (m + 1)
      have hs := (nativeLoopGroupShiftNatIso k).hom.naturality g
      have hnext := iterationNativeGroupShiftNatIso_hom_app (n + 1) m k X
      have hcur := iterationNativeGroupShiftNatIso_hom_app n m k X
      have h := (congrArg₂ (fun f j => f ≫ j) hu hnext).trans
        (hs.trans (congrArg (fun f => f ≫ (piNPositiveFunctor (k + 1)).map g) hcur.symm))
      have hf := shiftedGroupIterationDiagram_map_succ m k X n
      have ht := groupIterationDiagram_map_succ X (m + 1) (k + 1) n
      exact (congrArg (fun f => f ≫
          (iterationNativeGroupShiftNatIso (n + 1) m k).hom.app X) hf).trans
        (h.trans (congrArg (fun f => (iterationNativeGroupShiftNatIso n m k).hom.app X ≫ f)
          ht.symm)))
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    exact (iterationNativeGroupShiftNatIso n m k).hom.naturality f

/-- The WHOLE original one-loop diagram is naturally isomorphic with BOTH original maps. -/
def loopShiftDiagramNatIso (m k : ℕ) : shiftedGroupIterationDiagramFunctor.{u, v} m k ≅
    groupIterationDiagramFunctor (m + 1) (k + 1) :=
  NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun n => (iterationNativeGroupShiftNatIso n m k).app X)
    (fun f => ((loopShiftDiagramNatTrans m k).app X).naturality f))
    (fun f => by
      apply NatTrans.ext
      funext n
      exact (iterationNativeGroupShiftNatIso n m k).hom.naturality f)

/-- The ENTIRE one-loop diagram hom is the SAME actual unit-derived comparison NatTrans. -/
theorem loopShiftDiagramNatIso_hom (m k : ℕ) :
    (loopShiftDiagramNatIso.{u, v} m k).hom = loopShiftDiagramNatTrans m k := rfl

/-- The full original diagonal index comparison is assembled from the SAME original full Isos. -/
def diagonalSuccessorIndexNatIso (m k : ℕ) : diagonalDiagramFunctor.{u, v} (m + 1) (k + 1) ≅
    diagonalDiagramFunctor m k ⋙ successorDiagramFunctor :=
  (iterationDiagonalNatIso (m + 1) (k + 1)).symm ≪≫ (loopShiftDiagramNatIso m k).symm ≪≫
    Functor.isoWhiskerRight (iterationDiagonalNatIso m k) successorDiagramFunctor

/-- EVERY ENTIRE diagonal index hom is ACTUALLY both original level/degree arithmetic maps. -/
theorem diagonalSuccessorIndexNatIso_hom_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((diagonalSuccessorIndexNatIso m k).hom.app X).app n =
      (groupTailIndexNatIso n m k).hom.app X := by
  have h := congr_app (iterationGroupEvaluation_succ_tail_whole n m k) X
  exact originalCancelTailWord ((iterationNativeGroupShiftNatIso n m k).app X)
    ((iterationGroupEvaluationNatIso n (m + 1) (k + 1)).app X)
    ((iterationGroupEvaluationNatIso (n + 1) m k).hom.app X)
    ((groupTailIndexNatIso n m k).hom.app X) h

/-- The ENTIRE component-Iso function is the SAME actual original target index comparison. -/
theorem diagonalSuccessorIndexNatIso_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((diagonalSuccessorIndexNatIso m k).app X).app n =
      (groupTailIndexNatIso n m k).app X :=
  Iso.ext (diagonalSuccessorIndexNatIso_hom_app_app m k X n)

/-- EVERY ENTIRE diagonal inverse index function keeps BOTH actual original inverse maps. -/
theorem diagonalSuccessorIndexNatIso_inv_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((diagonalSuccessorIndexNatIso m k).inv.app X).app n =
      (groupTailIndexNatIso n m k).inv.app X :=
  congrArg (fun i => i.inv) (diagonalSuccessorIndexNatIso_app_app m k X n)

/-- The WHOLE actual original diagonal structure retains the original sigma and index maps. -/
def diagonalStructureNatTrans (m k : ℕ) : diagonalDiagramFunctor.{u, v} m k ⟶
    diagonalDiagramFunctor (m + 1) (k + 1) :=
  Functor.whiskerLeft (diagonalDiagramFunctor m k) successorTransitionNatTrans ≫
    (diagonalSuccessorIndexNatIso m k).inv

/-- EVERY full diagonal structure component is ACTUALLY original sigma then original index. -/
theorem diagonalStructureNatTrans_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((diagonalStructureNatTrans m k).app X).app n =
      (diagonalTransition n m k).app X ≫ (groupTailIndexNatIso n m k).inv.app X := by
  have h := (successorTransitionNatTrans_app_app (diagonalDiagram X m k) n).trans
    (diagonalDiagram_map_succ X m k n)
  exact congrArg₂ (fun f g => f ≫ g) h (diagonalSuccessorIndexNatIso_inv_app_app m k X n)

/-- The ENTIRE original R/diagonal structure square follows from the actual sigma/index maps. -/
theorem iterationDiagonal_structure_whole (m k : ℕ) :
    iterationGroupStructureNatTrans.{u, v} m k ≫
        (iterationDiagonalNatIso (m + 1) (k + 1)).hom =
      (iterationDiagonalNatIso m k).hom ≫ diagonalStructureNatTrans m k := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext n
  have h := originalRightIndexSquare
    ((groupStructureNatTrans m k).app ((iterate n).obj X))
    ((iterationGroupEvaluationNatIso n (m + 1) (k + 1)).hom.app X)
    ((iterationGroupEvaluationNatIso n m k).hom.app X) ((diagonalTransition n m k).app X)
    ((groupTailIndexNatIso n m k).app X)
    (iteration_group_structure_diagonal_index_square n m k X)
  exact h.trans (congrArg (fun f => (iterationGroupEvaluationNatIso n m k).hom.app X ≫ f)
    (diagonalStructureNatTrans_app_app m k X n).symm)

/-- The entire actual diagonal structure colimit uses the SAME genuine original Group functor. -/
def diagonalColimitStructureNatTrans (m k : ℕ) : diagonalDiagramFunctor.{u, v} m k ⋙
    GrpCat.FilteredColimits.colimitFunctor ⟶
      diagonalDiagramFunctor (m + 1) (k + 1) ⋙ GrpCat.FilteredColimits.colimitFunctor :=
  Functor.whiskerRight (diagonalStructureNatTrans m k)
    GrpCat.FilteredColimits.colimitFunctor

/-- EVERY actual original Group colimit retains the entire R/diagonal structure square. -/
theorem iterationDiagonal_colimit_structure_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    GrpCat.FilteredColimits.colimitMap ((iterationGroupStructureNatTrans m k).app X) ≫
        GrpCat.FilteredColimits.colimitMap ((iterationDiagonalNatIso (m + 1) (k + 1)).hom.app X) =
      GrpCat.FilteredColimits.colimitMap ((iterationDiagonalNatIso m k).hom.app X) ≫
        GrpCat.FilteredColimits.colimitMap ((diagonalStructureNatTrans m k).app X) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  have h := congr_app (iterationDiagonal_structure_whole m k) X
  exact (Q.map_comp _ _).symm.trans ((Q.congr_map h).trans (Q.map_comp _ _))

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- ALL full original telescope structure maps retain their ACTUAL original diagonal square. -/
theorem telescopeDiagonal_structure_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (groupStructureNatTrans m k).app (telescope X) ≫
        (telescopeDiagonalNatIso (m + 1) (k + 1)).hom.app X =
      (telescopeDiagonalNatIso m k).hom.app X ≫
        GrpCat.FilteredColimits.colimitMap ((diagonalStructureNatTrans m k).app X) := by
  let a := (groupStructureNatTrans m k).app (telescope X)
  let b := (telescopeGroupIterationColimitNatIso (m + 1) (k + 1)).hom.app X
  let c := (telescopeGroupIterationColimitNatIso m k).hom.app X
  let d := GrpCat.FilteredColimits.colimitMap ((iterationGroupStructureNatTrans m k).app X)
  let e := GrpCat.FilteredColimits.colimitMap
    ((iterationDiagonalNatIso (m + 1) (k + 1)).hom.app X)
  let f := GrpCat.FilteredColimits.colimitMap ((iterationDiagonalNatIso m k).hom.app X)
  let g := GrpCat.FilteredColimits.colimitMap ((diagonalStructureNatTrans m k).app X)
  have h₁ : a ≫ b = c ≫ d := telescopeGroupIteration_structure_hom m k X
  have h₂ : d ≫ e = f ≫ g := iterationDiagonal_colimit_structure_hom m k X
  have h : a ≫ (b ≫ e) = (c ≫ f) ≫ g :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun x => x ≫ e) h₁).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun x => c ≫ x) h₂).trans (Category.assoc _ _ _).symm)))
  exact (congrArg (fun x => a ≫ x)
      (telescopeDiagonalNatIso_hom_app (m + 1) (k + 1) X)).trans
    (h.trans (congrArg (fun x => x ≫ g) (telescopeDiagonalNatIso_hom_app m k X).symm))

/-- The WHOLE original telescope/diagonal comparison preserves EVERY actual sigma component. -/
theorem telescopeDiagonal_structure_whole (m k : ℕ) :
    Functor.whiskerLeft telescopeFunctor (groupStructureNatTrans m k) ≫
        (telescopeDiagonalNatIso (m + 1) (k + 1)).hom =
      (telescopeDiagonalNatIso m k).hom ≫ diagonalColimitStructureNatTrans.{u, v} m k := by
  apply NatTrans.ext
  funext X
  exact telescopeDiagonal_structure_hom m k X

/-- The ENTIRE inverse original telescope/diagonal comparison keeps the full sigma square. -/
theorem telescopeDiagonal_structure_inv_whole (m k : ℕ) :
    diagonalColimitStructureNatTrans.{u, v} m k ≫
        (telescopeDiagonalNatIso (m + 1) (k + 1)).inv =
      (telescopeDiagonalNatIso m k).inv ≫
        Functor.whiskerLeft telescopeFunctor (groupStructureNatTrans m k) := by
  exact originalInverseStructureSquare (telescopeDiagonalNatIso m k)
    (telescopeDiagonalNatIso (m + 1) (k + 1))
    (Functor.whiskerLeft telescopeFunctor (groupStructureNatTrans m k))
    (diagonalColimitStructureNatTrans m k) (telescopeDiagonal_structure_whole m k)

end PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalStructureGeometry
