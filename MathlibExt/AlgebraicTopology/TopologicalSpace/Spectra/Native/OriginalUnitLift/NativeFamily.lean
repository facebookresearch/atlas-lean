/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.FreeFamilyEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.NativeEvaluation

/-!
# Native Family

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.UnitLiftFamily
open scoped MonoidalClosed
namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback

/-- The actual native lift is kept at its complete typed source and target, for every coefficient. -/
def nativeLiftFamily (n r : ℕ) :
    FreeMapFamily (OrthogonalOperatorIndex.ofIndex.{u, v} r)
      (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))
      (PointedCGWH.orthogonalSphere.{u, v} n) nativeUnitObject.{u, v} (sphereFree.{u, v} n) :=
  fun K g => nativeUnitLift.{u, v} n r K g

theorem nativeLiftFamily_naturality (n r : ℕ) :
    FreeMapFamilyNaturality (OrthogonalOperatorIndex.ofIndex.{u, v} r)
      (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))
      (PointedCGWH.orthogonalSphere.{u, v} n) nativeUnitObject.{u, v} (sphereFree.{u, v} n)
      (nativeLiftFamily.{u, v} n r) := by
  intro K K' f g
  have h := rightLift_coefficient (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
    (fun n r => n + r) nativePairFamily.{u, v} nativePair_coefficient_family.{u, v}
    n r (PointedCGWH.orthogonalSphere.{u, v} n) f g
  simpa only [nativeLiftFamily, nativeUnitLift_eq_rightLift] using h

/-- The target is the exact original native lift evaluated on the complete free/evaluation counit. -/
def nativeLiftReadbackTarget (n r : ℕ) :
    PointedCGWH.orthogonalSphere.{u, v} n ⊗
      nativeUnitObject.{u, v}.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r) ⟶
        (sphereFree.{u, v} n).toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r)) :=
  freeMapFamilyTarget (OrthogonalOperatorIndex.ofIndex.{u, v} r)
    (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))
    (PointedCGWH.orthogonalSphere.{u, v} n) nativeUnitObject.{u, v} (sphereFree.{u, v} n)
    (nativeLiftFamily.{u, v} n r)

theorem nativeLiftFamily_evaluate (n r : ℕ) (K : PointedCGWH.{u, v})
    (g : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶ nativeUnitObject.{u, v}) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ K) (sphereFree.{u, v} n)
      (nativeUnitLift.{u, v} n r K g) =
        (PointedCGWH.orthogonalSphere.{u, v} n ◁
          Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K nativeUnitObject.{u, v} g) ≫
            nativeLiftReadbackTarget.{u, v} n r := by
  exact freeMapFamily_evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r)
    (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))
    (PointedCGWH.orthogonalSphere.{u, v} n) nativeUnitObject.{u, v} (sphereFree.{u, v} n)
    (nativeLiftFamily.{u, v} n r) (nativeLiftFamily_naturality.{u, v} n r) K g

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
