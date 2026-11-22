/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionStageInterleaving
import MathlibExt.Algebra.Category.Grp.FilteredInterleaving

/-!
# Original suspension isomorphisms of the complete diagonal group quotients

The two proved native stage equations instantiate the original filtered
group interleaving theorem. The forward map is the actual scalar unit
followed by the signed scalar-loop comparison. Every inverse quotient leg
uses the original spectrum structure map into the next original stage.
Both complete spectrum-map naturalities and all original stage legs are
retained, for every starting level and positive group index.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionDiagonalGeometry

open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStageGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The whole original diagonal suspension transformation is induced by the actual scalar unit. -/
def suspensionDiagonalNatTrans (m k : ℕ) : diagonalDiagramFunctor.{u, v} m k ⟶
    SuspensionGeometry.suspension ⋙ diagonalDiagramFunctor m (k + 1) :=
  Functor.whiskerRight SuspensionGeometry.unit (diagonalDiagramFunctor m k) ≫
    (Functor.associator SuspensionGeometry.suspension SuspensionGeometry.loop
      (diagonalDiagramFunctor m k)).hom ≫
        Functor.whiskerLeft SuspensionGeometry.suspension (scalarLoopDiagonalNatIso m k).hom

/-- Its complete component retains both original diagonal maps in their actual order. -/
theorem suspensionDiagonalNatTrans_app (m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (suspensionDiagonalNatTrans m k).app X =
      (diagonalDiagramFunctor m k).map (SuspensionGeometry.unit.app X) ≫
        (scalarLoopDiagonalNatIso m k).hom.app (SuspensionGeometry.suspension.obj X) := by
  change _ ≫ 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- Every original stage is the entire actual signed scalar-unit suspension map. -/
theorem suspensionDiagonalNatTrans_app_app (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    ((suspensionDiagonalNatTrans m k).app X).app n = (stageForward n m k).app X := by
  rw [suspensionDiagonalNatTrans_app, NatTrans.comp_app]
  change (levelCubeGroupFunctor (m + n) (k + n)).map (SuspensionGeometry.unit.app X) ≫
    (signedStageShiftNatIso n m k).hom.app (SuspensionGeometry.suspension.obj X) = _
  exact (stageForward_app n m k X).symm

/-- Both actual native stage equations construct the complete original quotient isomorphism. -/
def suspensionDiagonalIso (m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    GrpCat.FilteredColimits.colimit ((diagonalDiagramFunctor m k).obj X) ≅
      GrpCat.FilteredColimits.colimit
        ((diagonalDiagramFunctor m (k + 1)).obj (SuspensionGeometry.suspension.obj X)) :=
  GrpCat.FilteredInterleaving.colimitIso _ _
    (fun n => (stageForward n m k).app X) (fun n => (stageBackward n m k).app X)
    (fun n => stageForward_comp_backward_step n m k X)
    (fun n => stageBackward_forward_next_step n m k X)

/-- The full quotient hom is the induced map of the same original unit-derived transformation. -/
theorem suspensionDiagonalIso_hom (m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (suspensionDiagonalIso m k X).hom =
      GrpCat.FilteredColimits.colimitMap ((suspensionDiagonalNatTrans m k).app X) :=
  GrpCat.FilteredInterleaving.colimitIso_hom_eq_colimitMap _ _ _ _ _ _ _
    (suspensionDiagonalNatTrans_app_app m k X)

/-- The original quotient isomorphism is natural in every complete original spectrum map. -/
def suspensionColimitNatIso (m k : ℕ) : diagonalColimitFunctor.{u, v} m k ≅
    SuspensionGeometry.suspension ⋙ diagonalColimitFunctor m (k + 1) :=
  NatIso.ofComponents (suspensionDiagonalIso m k) (fun f => by
    rw [suspensionDiagonalIso_hom, suspensionDiagonalIso_hom]
    change GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map f) ≫
        GrpCat.FilteredColimits.colimitMap ((suspensionDiagonalNatTrans m k).app _) =
      GrpCat.FilteredColimits.colimitMap ((suspensionDiagonalNatTrans m k).app _) ≫
        GrpCat.FilteredColimits.colimitMap
          ((diagonalDiagramFunctor m (k + 1)).map (SuspensionGeometry.suspension.map f))
    rw [← GrpCat.FilteredColimits.colimitMap_comp, ← GrpCat.FilteredColimits.colimitMap_comp]
    exact congrArg GrpCat.FilteredColimits.colimitMap
      ((suspensionDiagonalNatTrans m k).naturality f))

/-- The full forward quotient map is the original unit map followed by the
actual loop comparison. -/
theorem suspensionColimitNatIso_hom_app (m k : ℕ) (X : SequentialSpectrum.{u, v}) :
    (suspensionColimitNatIso m k).hom.app X =
      (diagonalColimitFunctor m k).map (SuspensionGeometry.unit.app X) ≫
        (scalarLoopColimitNatIso m k).hom.app (SuspensionGeometry.suspension.obj X) := by
  change (suspensionDiagonalIso m k X).hom = _
  rw [suspensionDiagonalIso_hom, suspensionDiagonalNatTrans_app,
    GrpCat.FilteredColimits.colimitMap_comp, scalarLoopColimitNatIso_hom_app]
  rfl

/-- Every entire original forward leg keeps the complete actual signed scalar suspension map. -/
theorem suspensionColimitNatIso_hom_leg (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    diagonalLeg m k X n ≫ (suspensionColimitNatIso m k).hom.app X =
      (stageForward n m k).app X ≫
        diagonalLeg m (k + 1) (SuspensionGeometry.suspension.obj X) n :=
  GrpCat.FilteredInterleaving.colimitIso_hom_ι _ _ _ _ _ _ n

/-- Every entire original inverse leg uses the actual structure map and next
original quotient leg. -/
theorem suspensionColimitNatIso_inv_leg (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    diagonalLeg m (k + 1) (SuspensionGeometry.suspension.obj X) n ≫
        (suspensionDiagonalIso m k X).inv =
      (stageBackward n m k).app X ≫ diagonalLeg m k X (n + 1) := by
  exact GrpCat.FilteredInterleaving.colimitIso_inv_ι
    ((diagonalDiagramFunctor m k).obj X)
    ((diagonalDiagramFunctor m (k + 1)).obj (SuspensionGeometry.suspension.obj X))
    (fun i => (stageForward i m k).app X) (fun i => (stageBackward i m k).app X)
    (fun i => stageForward_comp_backward_step i m k X)
    (fun i => stageBackward_forward_next_step i m k X) n

/-- The complete inverse quotient function keeps the same original signed structure-map stage. -/
theorem suspensionColimitNatIso_inv_leg_apply (m k : ℕ) (X : SequentialSpectrum.{u, v}) (n : ℕ)
    (a : ((diagonalDiagramFunctor m (k + 1)).obj (SuspensionGeometry.suspension.obj X)).obj n) :
    (suspensionDiagonalIso m k X).inv.hom
        ((diagonalLeg m (k + 1) (SuspensionGeometry.suspension.obj X) n).hom a) =
      (diagonalLeg m k X (n + 1)).hom (((stageBackward n m k).app X).hom a) :=
  congrArg (fun f => f.hom a) (suspensionColimitNatIso_inv_leg m k X n)

end PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionDiagonalGeometry
