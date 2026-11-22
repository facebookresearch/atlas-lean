/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion

/-!
# Face Algebra

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v uV vV uC vC

open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

section Ordinary
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C]

/-- The entire original left sphere face is the original mixed left face precomposed by the same complete sphere
  coefficient map. -/
theorem leftSphere_precompose (M : MonoidalCategory C) (F : ℕ → V ⥤ C) (S : ℕ → V)
    (gamma : Independent.GammaType M (fun n K => (F n).obj K) S)
    (pair : Independent.PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n, S (n + n) ≅ S n ⊗ S n) :
    ∀ n : ℕ, Independent.leftSphereFamily M F S gamma pair coefficient n =
      (F (n + n)).map (coefficient n).hom ≫
        Independent.leftFaceFamily M (fun n K => (F n).obj K) S gamma pair n n (S n) := by
  let := M
  intro n
  simp only [Independent.leftSphereFamily, Independent.spherePairFamily, Iso.trans_inv,
    Functor.mapIso_inv, Iso.symm_inv, Independent.leftFaceFamily, Category.assoc]

/-- The entire original right sphere face retains the same complete sphere coefficient precomposition. -/
theorem rightSphere_precompose (M : MonoidalCategory C) (F : ℕ → V ⥤ C) (S : ℕ → V)
    (gamma : Independent.GammaType M (fun n K => (F n).obj K) S)
    (pair : Independent.PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n, S (n + n) ≅ S n ⊗ S n) :
    ∀ n : ℕ, Independent.rightSphereFamily M F S gamma pair coefficient n =
      (F (n + n)).map (coefficient n).hom ≫
        Independent.rightFaceFamily M (fun n K => (F n).obj K) S gamma pair n n (S n) := by
  let := M
  intro n
  simp only [Independent.rightSphereFamily, Independent.spherePairFamily, Iso.trans_inv,
    Functor.mapIso_inv, Iso.symm_inv, Independent.rightFaceFamily, Category.assoc]

end Ordinary

/-- The literal actual native left sphere face retains the original free-functor coefficient map and mixed left face. -/
theorem nativeLeftSphereFaces_precompose : ∀ n : ℕ,
    nativeLeftSphereFaces.{u, v} n =
      (nativeFreeFunctor.{u, v} (n + n)).map (PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫
        nativeLeftFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n) :=
  leftSphere_precompose CanonicalSourceSmash.monoidalCategory.{u, v} nativeFreeFunctor.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} gamma.{u, v} nativePairFamily.{u, v}
    (fun n => PointedCGWH.orthogonalSphereTensorIso.{u, v} n n)

/-- The literal actual native right sphere face retains that same original free-functor coefficient map and mixed right
  face. -/
theorem nativeRightSphereFaces_precompose : ∀ n : ℕ,
    nativeRightSphereFaces.{u, v} n =
      (nativeFreeFunctor.{u, v} (n + n)).map (PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫
        nativeRightFaces.{u, v} n n (PointedCGWH.orthogonalSphere.{u, v} n) :=
  rightSphere_precompose CanonicalSourceSmash.monoidalCategory.{u, v} nativeFreeFunctor.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} gamma.{u, v} nativePairFamily.{u, v}
    (fun n => PointedCGWH.orthogonalSphereTensorIso.{u, v} n n)

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
