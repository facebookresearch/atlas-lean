/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.TypeSuccessor
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.PositiveStructure

/-!
# The ENTIRE original all-degree R-unit and one-loop Type structure diagram

Every original R iterate, native level, selected point, finite index map
and input-spectrum Arrow is retained. The SAME actual native loop Type
shift includes degree zero. Its naturality constructs BOTH full maps of
the shifted original R diagram. The actual original unit identifies the
whole structure diagram with the original successor transition followed
by this genuine native shift. No incoming unit, structure, detector or
replacement diagram law is assumed; arbitrary underlying weakness remains
separate from these all-degree Type comparison maps.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.TypeLoopStructureGeometry
open GrpCat.FilteredColimits.Successor
open CategoryTheory.Spectra.Sequential (evaluation)
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.HomotopyStructureColimitGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.TypeSuccessorGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The full original one-loop Type Iso uses the SAME native evaluation and all-degree shift. -/
def iterationNativeTypeShiftNatIso (n m k : ℕ) :
    iterate.{u, v} (n + 1) ⋙ CategoryTheory.Spectra.Sequential.evaluation sphereOne m ⋙
      piNFunctor k ≅
      iterate n ⋙ CategoryTheory.Spectra.Sequential.evaluation sphereOne (m + 1) ⋙
        piNFunctor (k + 1) :=
  Functor.associator (iterate n) functor
    (CategoryTheory.Spectra.Sequential.evaluation sphereOne m ⋙ piNFunctor k) ≪≫
    Functor.isoWhiskerLeft (iterate n)
      ((Functor.associator functor
        (CategoryTheory.Spectra.Sequential.evaluation sphereOne m) (piNFunctor k)).symm ≪≫
        Functor.isoWhiskerRight (levelEvaluationIso m) (piNFunctor k) ≪≫
          Functor.associator
            (CategoryTheory.Spectra.Sequential.evaluation sphereOne (m + 1)) PointedCGWH.loop
            (piNFunctor k) ≪≫
          Functor.isoWhiskerLeft
            (CategoryTheory.Spectra.Sequential.evaluation sphereOne (m + 1))
              (nativeLoopPiShiftNatIso k))

/-- The ENTIRE original Type hom is the actual native loop shift, including literal degree zero. -/
theorem iterationNativeTypeShiftNatIso_hom_app (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationNativeTypeShiftNatIso n m k).hom.app X =
      (nativeLoopPiShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1)) := by
  change 𝟙 _ ≫ (𝟙 _ ≫ (piNFunctor k).map (𝟙 _) ≫ 𝟙 _ ≫
    (nativeLoopPiShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1))) = _
  simp only [Category.id_comp]
  have h := (piNFunctor.{u, v} k).map_id
    (PointedCGWH.loop.obj (((iterate n).obj X).level (m + 1)))
  exact (congrArg (fun f => f ≫
    (nativeLoopPiShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1))) h).trans
      (Category.id_comp _)

/-- BOTH original all-degree one-loop component functions are the SAME native shift Iso. -/
theorem iterationNativeTypeShiftNatIso_app (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationNativeTypeShiftNatIso n m k).app X =
      (nativeLoopPiShiftNatIso k).app (((iterate n).obj X).level (m + 1)) :=
  Iso.ext (iterationNativeTypeShiftNatIso_hom_app n m k X)

/-- The ENTIRE original inverse component is the SAME actual native inverse shift function. -/
theorem iterationNativeTypeShiftNatIso_inv_app (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationNativeTypeShiftNatIso n m k).inv.app X =
      (nativeLoopPiShiftNatIso k).inv.app (((iterate n).obj X).level (m + 1)) :=
  congrArg (fun e => e.inv) (iterationNativeTypeShiftNatIso_app n m k X)

/-- Every actual original Type iteration successor is the SAME original unit map. -/
theorem typeIterationDiagram_map_succ (X : PointedCGWH.SequentialSpectrum.{u, v})
    (m k n : ℕ) : ((typeIterationDiagramFunctor m k).obj X).map
      (homOfLE (Nat.le_succ n)) = (piNFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m) := by
  change (piNFunctor k).map
    (PointedCGWH.SequentialSpectrum.levelMap
      ((iterationDiagram X).map (homOfLE (Nat.le_succ n))) m) = _
  rw [iterationDiagram_map_succ]
  rfl

/-- The whole original shifted Type diagram retains the SAME full original R iteration. -/
def shiftedTypeIterationDiagramFunctor (m k : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ Type v) :=
  typeIterationDiagramFunctor m k ⋙ (Functor.whiskeringLeft ℕ ℕ (Type v)).obj successorFunctor

/-- Each complete original shifted step is the SAME actual next original iterate unit. -/
theorem shiftedTypeIterationDiagram_map_succ (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((shiftedTypeIterationDiagramFunctor m k).obj X).map (homOfLE (Nat.le_succ n)) =
      (piNFunctor k).map
        (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit (n + 1)).app X) m) :=
  typeIterationDiagram_map_succ X m k (n + 1)

/-- Genuine native Type loop-shift naturality constructs every original finite-index map square. -/
def loopShiftTypeDiagramNatTrans (m k : ℕ) : shiftedTypeIterationDiagramFunctor.{u, v} m k ⟶
    typeIterationDiagramFunctor (m + 1) (k + 1) where
  app X := NatTrans.ofSequence (fun n => (iterationNativeTypeShiftNatIso n m k).hom.app X)
    (fun n => by
      have hu := (piNFunctor k).congr_map (iterateUnit_successor_loop_levelMap n m X)
      let g := PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) (m + 1)
      have hs := (nativeLoopPiShiftNatIso k).hom.naturality g
      have hnext := iterationNativeTypeShiftNatIso_hom_app (n + 1) m k X
      have hcur := iterationNativeTypeShiftNatIso_hom_app n m k X
      have h := (congrArg₂ (fun f j => f ≫ j) hu hnext).trans
        (hs.trans (congrArg (fun f => f ≫ (piNFunctor (k + 1)).map g) hcur.symm))
      have hf := shiftedTypeIterationDiagram_map_succ m k X n
      have ht := typeIterationDiagram_map_succ X (m + 1) (k + 1) n
      exact (congrArg (fun f => f ≫
          (iterationNativeTypeShiftNatIso (n + 1) m k).hom.app X) hf).trans
        (h.trans (congrArg (fun f => (iterationNativeTypeShiftNatIso n m k).hom.app X ≫ f)
          ht.symm)))
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    exact (iterationNativeTypeShiftNatIso n m k).hom.naturality f

/-- The WHOLE original one-loop Type diagram Iso retains BOTH full original comparison maps. -/
def loopShiftTypeDiagramNatIso (m k : ℕ) : shiftedTypeIterationDiagramFunctor.{u, v} m k ≅
    typeIterationDiagramFunctor (m + 1) (k + 1) :=
  NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun n => (iterationNativeTypeShiftNatIso n m k).app X)
    (fun f => ((loopShiftTypeDiagramNatTrans m k).app X).naturality f))
    (fun f => by
      apply NatTrans.ext
      funext n
      exact (iterationNativeTypeShiftNatIso n m k).hom.naturality f)

/-- The ENTIRE original Type diagram hom is the actual complete native-shift transformation. -/
theorem loopShiftTypeDiagramNatIso_hom (m k : ℕ) :
    (loopShiftTypeDiagramNatIso.{u, v} m k).hom = loopShiftTypeDiagramNatTrans m k := rfl

/-- EVERY entire original forward diagram component is the SAME all-degree native shift. -/
theorem loopShiftTypeDiagramNatIso_hom_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((loopShiftTypeDiagramNatIso m k).hom.app X).app n =
      (nativeLoopPiShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1)) :=
  iterationNativeTypeShiftNatIso_hom_app n m k X

/-- EVERY entire original inverse diagram component is the SAME all-degree native inverse shift. -/
theorem loopShiftTypeDiagramNatIso_inv_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((loopShiftTypeDiagramNatIso m k).inv.app X).app n =
      (nativeLoopPiShiftNatIso k).inv.app (((iterate n).obj X).level (m + 1)) :=
  iterationNativeTypeShiftNatIso_inv_app n m k X

/-- ALL finite original indices preserve the entire original forward Type comparison square. -/
theorem loopShiftTypeDiagramNatIso_hom_index_naturality (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) {i j : ℕ} (f : i ⟶ j) :
    ((shiftedTypeIterationDiagramFunctor m k).obj X).map f ≫
        ((loopShiftTypeDiagramNatIso m k).hom.app X).app j =
      ((loopShiftTypeDiagramNatIso m k).hom.app X).app i ≫
        ((typeIterationDiagramFunctor (m + 1) (k + 1)).obj X).map f :=
  ((loopShiftTypeDiagramNatIso m k).hom.app X).naturality f

/-- ALL finite original indices preserve the entire original inverse Type comparison square. -/
theorem loopShiftTypeDiagramNatIso_inv_index_naturality (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) {i j : ℕ} (f : i ⟶ j) :
    ((typeIterationDiagramFunctor (m + 1) (k + 1)).obj X).map f ≫
        ((loopShiftTypeDiagramNatIso m k).inv.app X).app j =
      ((loopShiftTypeDiagramNatIso m k).inv.app X).app i ≫
        ((shiftedTypeIterationDiagramFunctor m k).obj X).map f :=
  ((loopShiftTypeDiagramNatIso m k).inv.app X).naturality f

/-- EVERY original spectrum Arrow preserves the entire forward Type diagram map square. -/
theorem loopShiftTypeDiagramNatIso_hom_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (shiftedTypeIterationDiagramFunctor m k).map f ≫ (loopShiftTypeDiagramNatIso m k).hom.app Y =
      (loopShiftTypeDiagramNatIso m k).hom.app X ≫
        (typeIterationDiagramFunctor (m + 1) (k + 1)).map f :=
  (loopShiftTypeDiagramNatIso m k).hom.naturality f

/-- EVERY original spectrum Arrow preserves the entire inverse Type diagram map square. -/
theorem loopShiftTypeDiagramNatIso_inv_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (typeIterationDiagramFunctor (m + 1) (k + 1)).map f ≫
        (loopShiftTypeDiagramNatIso m k).inv.app Y =
      (loopShiftTypeDiagramNatIso m k).inv.app X ≫ (shiftedTypeIterationDiagramFunctor m k).map f :=
  (loopShiftTypeDiagramNatIso m k).inv.naturality f

/-- The actual original Type successor transition retains EVERY whole R unit and input map. -/
def typeIterationTransitionNatTrans (m k : ℕ) : typeIterationDiagramFunctor.{u, v} m k ⟶
    shiftedTypeIterationDiagramFunctor m k :=
  Functor.whiskerLeft (typeIterationDiagramFunctor m k) typeSuccessorTransitionNatTrans

/-- EVERY entire original transition component is the literal-degree original piN unit map. -/
theorem typeIterationTransitionNatTrans_app_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    ((typeIterationTransitionNatTrans m k).app X).app n = (piNFunctor k).map
      (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m) :=
  (typeSuccessorTransitionNatTrans_app_app ((typeIterationDiagramFunctor m k).obj X) n).trans
    (typeIterationDiagram_map_succ X m k n)

/-- The SAME original Type structure map is the actual original unit followed by native shift. -/
theorem iterateUnitTypeMap_then_shift (n m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (cubeStructureNatTrans m k).app ((iterate n).obj X) =
      (piNFunctor k).map
          (PointedCGWH.SequentialSpectrum.levelMap ((iterateUnit n).app X) m) ≫
        (nativeLoopPiShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1)) :=
  (congrArg (fun f => (piNFunctor k).map f ≫
    (nativeLoopPiShiftNatIso k).hom.app (((iterate n).obj X).level (m + 1)))
      (iterateUnit_levelMap n X m)).symm

/-- The WHOLE original all-degree Type structure is actual successor then actual native shift. -/
theorem iterationTypeStructure_factorization_whole (m k : ℕ) :
    iterationTypeStructureNatTrans.{u, v} m k =
      typeIterationTransitionNatTrans m k ≫ (loopShiftTypeDiagramNatIso m k).hom := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext n
  exact (iterateUnitTypeMap_then_shift n m k X).trans
    (congrArg₂ (fun f g => f ≫ g)
      (typeIterationTransitionNatTrans_app_app m k X n).symm
      (loopShiftTypeDiagramNatIso_hom_app_app m k X n).symm)

/-- The ENTIRE original unit transition is actual structure followed by the native inverse shift. -/
theorem typeIterationTransition_structure_inverse_whole (m k : ℕ) :
    typeIterationTransitionNatTrans.{u, v} m k =
      iterationTypeStructureNatTrans m k ≫ (loopShiftTypeDiagramNatIso m k).inv := by
  rw [iterationTypeStructure_factorization_whole, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end PointedCGWH.SequentialSpectrum.MappingTelescope.TypeLoopStructureGeometry
