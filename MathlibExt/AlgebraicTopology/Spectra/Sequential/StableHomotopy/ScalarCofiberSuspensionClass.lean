/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ScalarCofiberLevelClass
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarFreeSphereHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.SuspendedFreeSphereNormalization

/-!
# The exact scalar unit image of a suspended cofiber representative

The strict free sphere representative, original I-cone suspension comparison
and scalar free evaluation identify the full target class of the coefficient
lift with the actual sphere suspension unit. All original Q maps are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- A strict represented coefficient lift has precisely the original scalar unit target class. -/
theorem suspendedCoefficientClass_map_eq_suspension
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (x : PointedCGWH.piN n (PointedCGWH.SequentialSpectrum.level (Q.obj F.right) m))
    (g : sphereSource m n ⟶ Q.obj F.right)
    (hg : H.map g = levelSphereClass m n (Q.obj F.right) x)
    (k : H.obj (S.obj (Q.obj (sphereSource m n))) ⟶ H.obj (S.obj (Q.obj F.left)))
    (hk : k ≫ H.map (S.map (Q.map F.hom)) =
      H.map (S.map (ε.app (sphereSource m n) ≫ g))) :
    PointedCGWH.piNMap (n + 1)
        (PointedCGWH.SequentialSpectrum.levelMap (T.map (Q.map F.hom)) m)
        (suspendedCoefficientClass F m n k) =
      PointedCGWH.SphereHom.sphereSuspensionClass n
        (PointedCGWH.SequentialSpectrum.level (Q.obj F.right) m) x := by
  let e := suspendedFreeSpherePiHomEquiv (B := B)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)
    n (T.obj (Q.obj F.right))
  have hClass := suspendedCoefficientClass_map_of_lift F m n g k hk
  have hNorm := originalSuspendedFreeSphereIso_strict_map (B := B)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)
    n F.right g
  have hs := suspendedFreeSpherePiHomEquiv_scalarMap (B := B)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)
    n (Q.obj F.right) x g hg
  have hs' := hs.trans (H.map_comp
    (scalarFreeSphereIso
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m) n).inv
    (T.map g))
  apply Eq.trans hClass
  apply e.symm_apply_eq.mpr
  exact hNorm.trans hs'.symm

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
