/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ScalarCofiberSuspensionClass
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ScalarSuspensionClassGroupMap
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionStageInterleaving

/-!
# Actual signed-stage lifts of scalar cofiber representatives

The original changing-degree isomorphism and its odd-stage inversion
transport the actual scalar coefficient lift to the same signed stage
used by the original integer suspension natural isomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift

open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStageGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionLoopShiftGeometry
open PointedCGWH.SuspensionReflectionGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- An actual space-suspension lift gives a preimage of the whole signed stage map. -/
theorem stageForward_image_of_space_lift (n m k : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (a : (levelCubeGroupFunctor (m + n) (k + n)).obj Y)
    (b : (levelCubeGroupFunctor (m + n) ((k + n) + 1)).obj
      (SuspensionGeometry.suspension.obj X))
    (hb : ((levelCubeGroupFunctor (m + n) ((k + n) + 1)).map
      (SuspensionGeometry.suspension.map f)).hom b =
        ((spaceSuspensionGroupMap (k + n)).app (Y.level (m + n))).hom a) :
    ∃ c : (levelCubeGroupFunctor (m + n) ((k + 1) + n)).obj
      (SuspensionGeometry.suspension.obj X),
      ((levelCubeGroupFunctor (m + n) ((k + 1) + n)).map
        (SuspensionGeometry.suspension.map f)).hom c =
          ((stageForward n m k).app Y).hom a := by
  let d := stageDegreeNatIso n m k
  let c := (d.hom.app (SuspensionGeometry.suspension.obj X)).hom b
  have hn := congrArg (fun g => g.hom b)
    (d.hom.naturality (SuspensionGeometry.suspension.map f))
  have hu : ((levelCubeGroupFunctor (m + n) ((k + 1) + n)).map
      (SuspensionGeometry.suspension.map f)).hom c =
        ((unsignedStageForward n m k).app Y).hom a := by
    calc
      _ = (d.hom.app (SuspensionGeometry.suspension.obj Y)).hom
          (((levelCubeGroupFunctor (m + n) ((k + n) + 1)).map
            (SuspensionGeometry.suspension.map f)).hom b) := hn.symm
      _ = (d.hom.app (SuspensionGeometry.suspension.obj Y)).hom
          (((spaceSuspensionGroupMap (k + n)).app (Y.level (m + n))).hom a) :=
        congrArg (d.hom.app (SuspensionGeometry.suspension.obj Y)).hom hb
      _ = _ := by
        rw [unsignedStageForward_space]
        rfl
  by_cases he : n % 2 = 0
  · exact ⟨c, hu.trans (congrArg (fun g => g.hom a) (stageForward_even n m k he Y)).symm⟩
  · refine ⟨c⁻¹, ?_⟩
    rw [map_inv, hu]
    exact (stageForward_odd_apply n m k he Y a).symm

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
