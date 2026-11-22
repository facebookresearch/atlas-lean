/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.NativeFamily

/-!
# Native Shifted Family

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
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.UnitLiftFamily
open scoped MonoidalClosed
namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback

/-- Transport a native free object along an equality of its natural-number labels, keeping the
coefficient fixed. -/
def nativeFreeLabelCast {a b : ℕ} (h : a = b) (K : PointedCGWH.{u, v}) :
    Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} a) K ⟶
      Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} b) K :=
  eqToHom (congrArg (fun j => Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} j) K) h)

theorem nativeFreeLabelCast_coefficient {a b : ℕ} (h : a = b)
    {K K' : PointedCGWH.{u, v}} (f : K ⟶ K') :
    Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} a) f ≫ nativeFreeLabelCast h K' =
      nativeFreeLabelCast h K ≫ Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} b) f := by
  cases h
  simp only [nativeFreeLabelCast, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The native unit-lift family with source label `r + n`, transported by commutativity of
addition to `n + r`. -/
def nativeShiftedLiftFamily (n r : ℕ) :
    FreeMapFamily (OrthogonalOperatorIndex.ofIndex.{u, v} r)
      (OrthogonalOperatorIndex.ofIndex.{u, v} (r + n))
      (PointedCGWH.orthogonalSphere.{u, v} n) nativeUnitObject.{u, v} (sphereFree.{u, v} n) :=
  fun K g => nativeFreeLabelCast (Nat.add_comm r n) (PointedCGWH.orthogonalSphere.{u, v} n ⊗ K) ≫
    nativeUnitLift.{u, v} n r K g

theorem nativeShiftedLiftFamily_naturality (n r : ℕ) :
    FreeMapFamilyNaturality (OrthogonalOperatorIndex.ofIndex.{u, v} r)
      (OrthogonalOperatorIndex.ofIndex.{u, v} (r + n))
      (PointedCGWH.orthogonalSphere.{u, v} n) nativeUnitObject.{u, v} (sphereFree.{u, v} n)
      (nativeShiftedLiftFamily.{u, v} n r) := by
  intro K K' f g
  have hCast := nativeFreeLabelCast_coefficient (Nat.add_comm r n)
    (PointedCGWH.orthogonalSphere.{u, v} n ◁ f)
  have hLift := nativeLiftFamily_naturality.{u, v} n r f g
  delta nativeShiftedLiftFamily
  rw [← Category.assoc, hCast, Category.assoc]
  exact congrArg (fun h => nativeFreeLabelCast (Nat.add_comm r n)
    (PointedCGWH.orthogonalSphere.{u, v} n ⊗ K) ≫ h) hLift

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
