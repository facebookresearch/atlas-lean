/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback

/-!
# Identity Generator

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.SpectrumIndexMaps
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf

/-- The complete original ordered identity generator maps to the same identity-frame native inclusion. -/
theorem ordered_generator_identity_image (n : ℕ) :
    orderedSymmetricOperatorHom.{u, v} n (n + n) n (Nat.add_comm n n) ≫
        symmetricOrthogonalOperatorHomMap.{u, v} (Sequential.finiteIndex n)
          (Sequential.finiteIndex (n + n)) =
      (orderedCoefficientIso.{u, v} n).hom ≫ Geometry.identityInclusion.{u, v} n := by
  let N := Sequential.finiteIndex n
  let P := Sequential.finiteIndex (n + n)
  let S := PointedCGWH.sphereSequence.{u, v}.functor.obj N
  let T := PointedCGWH.orthogonalSphere.{u, v} n
  let c := (orderedCoefficientIso.{u, v} n).hom
  let A := PointedCGWH.basedDiscreteObj.{u, v, 0} (N ⊗ N ⟶ P)
  let H := PointedCGWH.symmetricOperatorObj.{u, v} N ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} P
  let B := OrthogonalIndex.hom.{u, v} (n + n) (n + n)
  let p : 𝟙_ PointedCGWH.{u, v} ⟶ A :=
    PointedCGWH.basedDiscreteIncl.{u, v, 0} (N ⊗ N ⟶ P) (𝟙 P)
  let q := symmetricOrthogonalHomMap.{u, v} (N ⊗ N) P
  let m := symmetricOrthogonalOperatorHomMap.{u, v} N P
  let r := OrthogonalIndex.matrixPoint.{u, v} (OrthogonalMatrixHom.id (n + n))
  let i := OrthogonalOperatorIndex.ι.{u, v} n (n + n) n
  let is := Enriched.weightedCoend.ι
    (Enriched.SphereOperator.weight (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} Operad.SmallFinBijGroupoid)
      ((PointedCGWH.copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj N)
      ((PointedCGWH.copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj P))
    PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
    ((PointedCGWH.copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj N)
  have hp : p ≫ q = r :=
    (symmetricOrthogonalHomMap_generator.{u, v} (𝟙 P)).trans
      (congrArg (OrthogonalIndex.matrixPoint.{u, v}) (smallBijectionMatrix_id P))
  have hg : is ≫ m = (q ⊗ₘ c) ≫ i :=
    symmetricOrthogonalOperatorHomMap_generator.{u, v} N P N
  have hs : orderedSymmetricOperatorHom.{u, v} n (n + n) n (Nat.add_comm n n) =
      (λ_ S).inv ≫ (p ⊗ₘ 𝟙 S) ≫ is := rfl
  have hi : Geometry.identityInclusion.{u, v} n =
      (λ_ T).inv ≫ (r ⊗ₘ 𝟙 T) ≫ i := rfl
  have ht : (p ⊗ₘ 𝟙 S) ≫ (q ⊗ₘ c) = r ⊗ₘ c := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, hp]
  have hu : (λ_ S).inv ≫ (r ⊗ₘ c) = c ≫ (λ_ T).inv ≫ (r ⊗ₘ 𝟙 T) := by
    rw [leftUnitor_inv_naturality_assoc, ← id_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rfl
  rw [hs, hi]
  calc
    _ = (λ_ S).inv ≫ (p ⊗ₘ 𝟙 S) ≫ (is ≫ m) := by
      simp only [Category.assoc]
      rfl
    _ = (λ_ S).inv ≫ (p ⊗ₘ 𝟙 S) ≫ (q ⊗ₘ c) ≫ i := by rw [hg]
    _ = (λ_ S).inv ≫ (r ⊗ₘ c) ≫ i := by
      rw [← Category.assoc (p ⊗ₘ 𝟙 S) (q ⊗ₘ c) i, ht]
    _ = _ := by
      rw [← Category.assoc (λ_ S).inv (r ⊗ₘ c) i, hu]
      simp only [Category.assoc]
      rfl

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
