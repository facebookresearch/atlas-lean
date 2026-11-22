/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ScalarCofiberStageLift
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionStablePi

/-!
# Original integer preimages from signed scalar stage lifts

The full actual suspension isomorphism transports a signed stage preimage
back to the original integer quotient, retaining the same original leg.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift

open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStageGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private theorem diagonalLeg_naturality (m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    diagonalLeg m k X n ≫ (diagonalColimitFunctor m k).map f =
      (levelCubeGroupFunctor (m + n) (k + n)).map f ≫ diagonalLeg m k Y n :=
  GrpCat.FilteredColimits.colimitMap_ι ((diagonalDiagramFunctor m k).map f) n

private theorem image_of_natIso {C : Type u} [Category C] {F G : C ⥤ GrpCat.{v}}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y) (b : G.obj X) (x : F.obj Y)
    (hb : (G.map f).hom b = (e.hom.app Y).hom x) :
    ∃ y : F.obj X, (F.map f).hom y = x := by
  have hn := congrArg (fun g => g.hom b) (e.inv.naturality f)
  refine ⟨(e.inv.app X).hom b, ?_⟩
  calc
    _ = (e.inv.app Y).hom ((G.map f).hom b) := hn.symm
    _ = (e.inv.app Y).hom ((e.hom.app Y).hom x) := congrArg (e.inv.app Y).hom hb
    _ = x := congrArg (fun g => g.hom x) (e.hom_inv_id_app Y)

/-- A signed stage preimage gives a preimage of the same original integer quotient leg. -/
theorem integerPiMap_image_of_signed_stage (q : ℤ) (n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (a : (levelCubeGroupFunctor (integerTailLevel q + n)
      (integerTailPositiveIndex q + n)).obj Y)
    (c : (levelCubeGroupFunctor (integerTailLevel q + n)
      ((integerTailPositiveIndex q + 1) + n)).obj (SuspensionGeometry.suspension.obj X))
    (hc : ((levelCubeGroupFunctor (integerTailLevel q + n)
      ((integerTailPositiveIndex q + 1) + n)).map
        (SuspensionGeometry.suspension.map f)).hom c =
      ((stageForward n (integerTailLevel q) (integerTailPositiveIndex q)).app Y).hom a) :
    ∃ y : (integerStablePiFunctor q).obj X,
      ((integerStablePiFunctor q).map f).hom y = (integerStablePiLeg q Y n).hom a := by
  let m := integerTailLevel q
  let k := integerTailPositiveIndex q
  let e := integerSuspensionPiNatIso q
  let L (Z : PointedCGWH.SequentialSpectrum.{u, v}) :=
    diagonalLeg m (k + 1) (SuspensionGeometry.suspension.obj Z) n ≫
      (suspensionNormalizationNatIso q).hom.app (SuspensionGeometry.suspension.obj Z)
  have hL : (levelCubeGroupFunctor (m + n) ((k + 1) + n)).map
      (SuspensionGeometry.suspension.map f) ≫ L Y =
    L X ≫ (integerStablePiFunctor (q + 1)).map (SuspensionGeometry.suspension.map f) := by
    let sX := diagonalLeg m (k + 1) (SuspensionGeometry.suspension.obj X) n
    let sY := diagonalLeg m (k + 1) (SuspensionGeometry.suspension.obj Y) n
    let nX := (suspensionNormalizationNatIso q).hom.app (SuspensionGeometry.suspension.obj X)
    let nY := (suspensionNormalizationNatIso q).hom.app (SuspensionGeometry.suspension.obj Y)
    let dF := (diagonalColimitFunctor m (k + 1)).map (SuspensionGeometry.suspension.map f)
    let pF := (integerStablePiFunctor (q + 1)).map (SuspensionGeometry.suspension.map f)
    let gF := (levelCubeGroupFunctor (m + n) ((k + 1) + n)).map
      (SuspensionGeometry.suspension.map f)
    have hd : sX ≫ dF = gF ≫ sY :=
      diagonalLeg_naturality m (k + 1) (SuspensionGeometry.suspension.map f) n
    have hn : dF ≫ nY = nX ≫ pF :=
      (suspensionNormalizationNatIso q).hom.naturality (SuspensionGeometry.suspension.map f)
    calc
      gF ≫ (sY ≫ nY) = (gF ≫ sY) ≫ nY := (Category.assoc gF sY nY).symm
      _ = (sX ≫ dF) ≫ nY := congrArg (fun t => t ≫ nY) hd.symm
      _ = sX ≫ (dF ≫ nY) := Category.assoc sX dF nY
      _ = sX ≫ (nX ≫ pF) := congrArg (fun t => sX ≫ t) hn
      _ = (sX ≫ nX) ≫ pF := (Category.assoc sX nX pF).symm
  have hLeg : integerStablePiLeg q Y n ≫ e.hom.app Y =
      (stageForward n m k).app Y ≫ L Y := by
    exact (congrArg (fun t => integerStablePiLeg q Y n ≫ t)
      (integerSuspensionPiNatIso_hom_app q Y)).trans
        (integerSuspensionPiMap_leg q Y n)
  apply image_of_natIso e f ((L X).hom c) ((integerStablePiLeg q Y n).hom a)
  calc
    _ = (L Y).hom (((levelCubeGroupFunctor (m + n) ((k + 1) + n)).map
        (SuspensionGeometry.suspension.map f)).hom c) :=
      (congrArg (fun g => g.hom c) hL).symm
    _ = (L Y).hom (((stageForward n m k).app Y).hom a) := congrArg (L Y).hom hc
    _ = (e.hom.app Y).hom ((integerStablePiLeg q Y n).hom a) :=
      (congrArg (fun g => g.hom a) hLeg).symm

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
