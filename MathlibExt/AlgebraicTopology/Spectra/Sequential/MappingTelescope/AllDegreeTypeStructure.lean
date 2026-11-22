/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.TypeLoopStructure

/-!
# ACTUAL original telescope adjoint Type Isos in ALL literal degrees

The SAME original Type colimits, R units, MC projections, telescope and
native loop shift are used throughout. The proved WHOLE original unit
factorization and genuine successor finality construct the actual Type
structure colimit Iso. The original telescope/R structure square proves
BOTH entire telescope structure comparison functions. Its adjoint Iso's
ENTIRE hom is the SAME actual original piNMap in every degree, including
literal zero, with all original spectrum-map naturalities. No desired
unit, structure, weak detector or stable-model law is an input. Arbitrary
underlying-point weakness remains a separate theorem obligation.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.AllDegreeTypeStructureGeometry
open GrpCat.FilteredColimits.Successor
attribute [local instance] GrpCat.FilteredColimits.Successor.successorFunctor_final
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.HomotopyStructureColimitGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.TypeSuccessorGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.TypeLoopStructureGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- BOTH full original Type structure colimit maps use actual finality and actual native shift. -/
def iterationTypeStructureColimitIso (m k : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    colimit ((typeIterationDiagramFunctor m k).obj X) ≅
      colimit ((typeIterationDiagramFunctor (m + 1) (k + 1)).obj X) :=
  (Functor.Final.colimitIso successorFunctor ((typeIterationDiagramFunctor m k).obj X)).symm ≪≫
    colim.mapIso ((loopShiftTypeDiagramNatIso m k).app X)

/-- The ENTIRE original structure-Iso hom is the SAME actual Type colimit structure map. -/
theorem iterationTypeStructureColimitIso_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationTypeStructureColimitIso m k X).hom =
      colim.map ((iterationTypeStructureNatTrans m k).app X) := by
  let D := (typeIterationDiagramFunctor m k).obj X
  have h : (iterationTypeStructureNatTrans m k).app X =
      typeSuccessorTransitionNatTrans.app D ≫ (loopShiftTypeDiagramNatIso m k).hom.app X :=
    congr_app (iterationTypeStructure_factorization_whole m k) X
  have hm := (colim.congr_map h).trans (colim.map_comp _ _)
  change (Functor.Final.colimitIso successorFunctor D).inv ≫
    colim.map ((loopShiftTypeDiagramNatIso m k).hom.app X) = _
  exact (congrArg (fun f => f ≫ colim.map ((loopShiftTypeDiagramNatIso m k).hom.app X))
    (typeSuccessorTransition_colimit_eq_inv D).symm).trans hm.symm

/-- The ENTIRE original inverse structure map retains native inverse and true Type descent. -/
theorem iterationTypeStructureColimitIso_inv (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterationTypeStructureColimitIso m k X).inv =
      colim.map ((loopShiftTypeDiagramNatIso m k).inv.app X) ≫
        (Functor.Final.colimitIso successorFunctor ((typeIterationDiagramFunctor m k).obj X)).hom :=
  rfl

/-- EVERY original Type colimit leg preserves the actual complete original structure function. -/
theorem iterationTypeStructureColimitIso_hom_ι (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    colimit.ι ((typeIterationDiagramFunctor m k).obj X) n ≫
        (iterationTypeStructureColimitIso m k X).hom =
      (cubeStructureNatTrans m k).app ((iterate n).obj X) ≫
        colimit.ι ((typeIterationDiagramFunctor (m + 1) (k + 1)).obj X) n := by
  rw [iterationTypeStructureColimitIso_hom]
  exact colimit.ι_map ((iterationTypeStructureNatTrans m k).app X) n

/-- EVERY inverse structure leg retains the actual native inverse and original next-stage leg. -/
theorem iterationTypeStructureColimitIso_inv_ι (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    colimit.ι ((typeIterationDiagramFunctor (m + 1) (k + 1)).obj X) n ≫
        (iterationTypeStructureColimitIso m k X).inv =
      (nativeLoopPiShiftNatIso k).inv.app (((iterate n).obj X).level (m + 1)) ≫
        colimit.ι ((typeIterationDiagramFunctor m k).obj X) (n + 1) := by
  let D := (typeIterationDiagramFunctor m k).obj X
  let a := (loopShiftTypeDiagramNatIso m k).inv.app X
  have hf := colimit.ι_map a n
  have he := Functor.Final.ι_colimitIso_hom successorFunctor D n
  have hi := loopShiftTypeDiagramNatIso_inv_app_app m k X n
  change colimit.ι ((typeIterationDiagramFunctor (m + 1) (k + 1)).obj X) n ≫
    (colim.map a ≫ (Functor.Final.colimitIso successorFunctor D).hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (Functor.Final.colimitIso successorFunctor D).hom) hf).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => a.app n ≫ f) he).trans
          (congrArg (fun f => f ≫ colimit.ι D (n + 1)) hi))))

/-- The WHOLE original all-degree Type structure colimit Iso retains every input-spectrum map. -/
def iterationTypeStructureColimitNatIso (m k : ℕ) : typeIterationDiagramFunctor.{u, v} m k ⋙
    colim ≅ typeIterationDiagramFunctor (m + 1) (k + 1) ⋙ colim :=
  NatIso.ofComponents (iterationTypeStructureColimitIso m k) (fun f => by
    rw [iterationTypeStructureColimitIso_hom, iterationTypeStructureColimitIso_hom]
    exact (iterationTypeColimitStructureNatTrans m k).naturality f)

/-- The ENTIRE whole Type structure-Iso hom is the SAME original complete structure NatTrans. -/
theorem iterationTypeStructureColimitNatIso_hom (m k : ℕ) :
    (iterationTypeStructureColimitNatIso.{u, v} m k).hom =
      iterationTypeColimitStructureNatTrans m k := by
  apply NatTrans.ext
  funext X
  exact iterationTypeStructureColimitIso_hom m k X

/-- EVERY original spectrum Arrow preserves both complete forward structure comparison maps. -/
theorem iterationTypeStructureColimitNatIso_hom_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    colim.map ((typeIterationDiagramFunctor m k).map f) ≫
        (iterationTypeStructureColimitNatIso m k).hom.app Y =
      (iterationTypeStructureColimitNatIso m k).hom.app X ≫
        colim.map ((typeIterationDiagramFunctor (m + 1) (k + 1)).map f) :=
  (iterationTypeStructureColimitNatIso m k).hom.naturality f

/-- EVERY original spectrum Arrow preserves both complete inverse structure comparison maps. -/
theorem iterationTypeStructureColimitNatIso_inv_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    colim.map ((typeIterationDiagramFunctor (m + 1) (k + 1)).map f) ≫
        (iterationTypeStructureColimitNatIso m k).inv.app Y =
      (iterationTypeStructureColimitNatIso m k).inv.app X ≫
        colim.map ((typeIterationDiagramFunctor m k).map f) :=
  (iterationTypeStructureColimitNatIso m k).inv.naturality f

/-- The WHOLE actual original telescope adjoint Type transformation retains its original maps. -/
def telescopeAdjointTypeNatTrans (m k : ℕ) :
    telescopeFunctor.{u, v} ⋙ PointedCGWH.SequentialSpectrum.evaluation m ⋙ piNFunctor k ⟶
      telescopeFunctor ⋙ PointedCGWH.SequentialSpectrum.evaluation (m + 1) ⋙ PointedCGWH.loop ⋙
        piNFunctor k :=
  Functor.whiskerLeft telescopeFunctor
    (Functor.whiskerRight (adjointStructureNatTrans m) (piNFunctor k))

/-- EVERY entire actual adjoint component is the literal-degree original piN map. -/
theorem telescopeAdjointTypeNatTrans_app (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeAdjointTypeNatTrans m k).app X = (piNFunctor k).map
      (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) m) := rfl

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- BOTH entire original all-degree telescope structure functions use actual comparison maps. -/
def telescopeTypeStructureIso (m k : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    piN k ((telescope X).level m) ≅ piN (k + 1) ((telescope X).level (m + 1)) :=
  (telescopeTypeIterationColimitNatIso m k).app X ≪≫
    iterationTypeStructureColimitIso m k X ≪≫
      ((telescopeTypeIterationColimitNatIso (m + 1) (k + 1)).app X).symm

/-- The ENTIRE original telescope structure-Iso hom is the SAME actual original Type structure. -/
theorem telescopeTypeStructureIso_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeTypeStructureIso m k X).hom = (cubeStructureNatTrans m k).app (telescope X) := by
  let e := (telescopeTypeIterationColimitNatIso m k).app X
  let f := (telescopeTypeIterationColimitNatIso (m + 1) (k + 1)).app X
  let b := iterationTypeStructureColimitIso m k X
  have hb := iterationTypeStructureColimitIso_hom m k X
  have h : (cubeStructureNatTrans m k).app (telescope X) ≫ f.hom = e.hom ≫ b.hom :=
    (telescopeTypeIteration_structure_hom m k X).trans
      (congrArg (fun g => e.hom ≫ g) hb.symm)
  exact (Category.assoc e.hom b.hom f.inv).symm.trans ((Iso.comp_inv_eq f).mpr h.symm)

/-- The ENTIRE original telescope structure inverse preserves each actual original inverse map. -/
theorem telescopeTypeStructureIso_inv (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeTypeStructureIso m k X).inv =
      (telescopeTypeIterationColimitNatIso (m + 1) (k + 1)).hom.app X ≫
        (iterationTypeStructureColimitIso m k X).inv ≫
          (telescopeTypeIterationColimitNatIso m k).inv.app X := rfl

/-- The WHOLE original telescope Type structure Iso preserves every original input naturality. -/
def telescopeTypeStructureNatIso (m k : ℕ) : telescopeFunctor.{u, v} ⋙
    PointedCGWH.SequentialSpectrum.evaluation m ⋙ piNFunctor k ≅
      telescopeFunctor ⋙ PointedCGWH.SequentialSpectrum.evaluation (m + 1) ⋙ piNFunctor (k + 1) :=
  NatIso.ofComponents (telescopeTypeStructureIso m k) (fun f => by
    rw [telescopeTypeStructureIso_hom, telescopeTypeStructureIso_hom]
    exact (Functor.whiskerLeft telescopeFunctor (cubeStructureNatTrans m k)).naturality f)

/-- The ENTIRE whole telescope Type structure-Iso hom is the actual original structure family. -/
theorem telescopeTypeStructureNatIso_hom (m k : ℕ) :
    (telescopeTypeStructureNatIso.{u, v} m k).hom =
      Functor.whiskerLeft telescopeFunctor (cubeStructureNatTrans m k) := by
  apply NatTrans.ext
  funext X
  exact telescopeTypeStructureIso_hom m k X

/-- BOTH entire actual telescope adjoint Type Iso functions retain original native maps. -/
def telescopeAdjointTypeIso (m k : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    piN k ((telescope X).level m) ≅ piN k (PointedCGWH.loop.obj ((telescope X).level (m + 1))) :=
  telescopeTypeStructureIso m k X ≪≫
    ((nativeLoopPiShiftNatIso k).app ((telescope X).level (m + 1))).symm

/-- The ENTIRE telescope adjoint-Iso hom is the SAME original piNMap in EVERY actual degree. -/
theorem telescopeAdjointTypeIso_hom (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeAdjointTypeIso m k X).hom = (piNFunctor k).map
      (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) m) := by
  exact (Iso.comp_inv_eq
    ((nativeLoopPiShiftNatIso k).app ((telescope X).level (m + 1)))).mpr
      (telescopeTypeStructureIso_hom m k X)

/-- The ENTIRE telescope adjoint inverse uses the original native shift and structure inverse. -/
theorem telescopeAdjointTypeIso_inv (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeAdjointTypeIso m k X).inv =
      (nativeLoopPiShiftNatIso k).hom.app ((telescope X).level (m + 1)) ≫
        (telescopeTypeStructureIso m k X).inv := rfl

/-- EVERY original telescope adjoint piNMap is an Iso, including literal degree zero. -/
theorem telescopeAdjointTypeMap_isIso (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    IsIso ((piNFunctor k).map
      (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) m)) :=
  (telescopeAdjointTypeIso_hom m k X) ▸ (telescopeAdjointTypeIso m k X).isIso_hom

/-- The WHOLE actual all-degree original adjoint Type Iso retains both input naturalities. -/
def telescopeAdjointTypeNatIso (m k : ℕ) : telescopeFunctor.{u, v} ⋙
    PointedCGWH.SequentialSpectrum.evaluation m ⋙ piNFunctor k ≅
      telescopeFunctor ⋙ PointedCGWH.SequentialSpectrum.evaluation (m + 1) ⋙ PointedCGWH.loop ⋙
        piNFunctor k :=
  NatIso.ofComponents (telescopeAdjointTypeIso m k) (fun f => by
    rw [telescopeAdjointTypeIso_hom, telescopeAdjointTypeIso_hom]
    exact (telescopeAdjointTypeNatTrans m k).naturality f)

/-- The ENTIRE whole adjoint Type-Iso hom is the SAME original map family in EVERY degree. -/
theorem telescopeAdjointTypeNatIso_hom (m k : ℕ) :
    (telescopeAdjointTypeNatIso.{u, v} m k).hom = telescopeAdjointTypeNatTrans m k := by
  apply NatTrans.ext
  funext X
  exact telescopeAdjointTypeIso_hom m k X

/-- EVERY original spectrum Arrow retains the full actual forward adjoint homotopy map square. -/
theorem telescopeAdjointTypeNatIso_hom_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) ≫
        (telescopeAdjointTypeNatIso m k).hom.app Y =
      (telescopeAdjointTypeNatIso m k).hom.app X ≫ (piNFunctor k).map (PointedCGWH.loop.map
        (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) (m + 1))) :=
  (telescopeAdjointTypeNatIso m k).hom.naturality f

/-- EVERY original spectrum Arrow retains the full actual inverse adjoint homotopy map square. -/
theorem telescopeAdjointTypeNatIso_inv_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (piNFunctor k).map (PointedCGWH.loop.map
      (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) (m + 1))) ≫
        (telescopeAdjointTypeNatIso m k).inv.app Y =
      (telescopeAdjointTypeNatIso m k).inv.app X ≫
        (piNFunctor k).map (PointedCGWH.SequentialSpectrum.levelMap (telescopeFunctor.map f) m) :=
  (telescopeAdjointTypeNatIso m k).inv.naturality f

/-- EVERY actual original adjoint literal-degree map is bijective on the SAME homotopy type. -/
theorem telescopeAdjointPiNMap_bijective (m k : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.Bijective (piNMap k
      (PointedCGWH.SequentialSpectrum.adjointStructureMap (telescope X) m)) :=
  (CategoryTheory.isIso_iff_bijective _).mp (telescopeAdjointTypeMap_isIso m k X)

end PointedCGWH.SequentialSpectrum.MappingTelescope.AllDegreeTypeStructureGeometry
