/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.SuspendedFreeSphereHom
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ScalarCofiberSphereLift

/-!
# Actual level classes of the scalar-suspended cofiber lift

The original suspended free/evaluation Hom correspondence realizes the
same scalar lift as a next-degree cube class. Its full target-map square
retains the original Q arrow and the unchanged scalar suspension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev H := toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := Index)
private abbrev S := OriginalISuspension.suspension (B := B) (I := Index)
private abbrev T :=
  CategoryTheory.EnrichedFunctorCat.tensorLeft (A := Index) PointedCGWH.sphereOne

/-- The original scalar Hom lift gives a literal next-degree class at the original level. -/
def suspendedCoefficientClass
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (k : H.obj (S.obj (Q.obj (sphereSource m n))) ⟶ H.obj (S.obj (Q.obj F.left))) :
    PointedCGWH.piN (n + 1)
      (PointedCGWH.SequentialSpectrum.level (T.obj (Q.obj F.left)) m) :=
  (suspendedFreeSpherePiHomEquiv (B := B)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m) n
    (T.obj (Q.obj F.left))).symm (suspendedCoefficientLift F m n k)

/-- Its full original target map is the image of the same scalar suspended Hom lift. -/
theorem suspendedCoefficientClass_map
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (k : H.obj (S.obj (Q.obj (sphereSource m n))) ⟶ H.obj (S.obj (Q.obj F.left))) :
    PointedCGWH.piNMap (n + 1)
        (PointedCGWH.SequentialSpectrum.levelMap (T.map (Q.map F.hom)) m)
        (suspendedCoefficientClass F m n k) =
      (suspendedFreeSpherePiHomEquiv (B := B)
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m) n
        (T.obj (Q.obj F.right))).symm
        (suspendedCoefficientLift F m n k ≫ H.map (T.map (Q.map F.hom))) :=
  (suspendedFreeSpherePiHomEquiv_inverse_naturality (B := B)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m) n
    (T.map (Q.map F.hom)) (suspendedCoefficientLift F m n k)).symm

/-- A proved suspended coefficient equation gives the exact original next-degree map equation. -/
theorem suspendedCoefficientClass_map_of_lift
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (g : sphereSource m n ⟶ Q.obj F.right)
    (k : H.obj (S.obj (Q.obj (sphereSource m n))) ⟶ H.obj (S.obj (Q.obj F.left)))
    (hk : k ≫ H.map (S.map (Q.map F.hom)) =
      H.map (S.map (ε.app (sphereSource m n) ≫ g))) :
    PointedCGWH.piNMap (n + 1)
        (PointedCGWH.SequentialSpectrum.levelMap (T.map (Q.map F.hom)) m)
        (suspendedCoefficientClass F m n k) =
      (suspendedFreeSpherePiHomEquiv (B := B)
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m) n
        (T.obj (Q.obj F.right))).symm
        ((originalSuspendedFreeSphereIso (B := B)
          (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m) n).inv ≫
          H.map (S.map (ε.app (sphereSource m n) ≫ g)) ≫
          (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).hom.app F.right) := by
  rw [suspendedCoefficientClass_map, suspendedCoefficientLift_map F m n g k hk]

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
