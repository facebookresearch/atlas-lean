/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereOneComparison
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereMonoidal
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.SphereSequence

/-!
# Ordered powers of the original sphere coefficient

The original smash powers of `sphereOne` map to the original one-point
Euclidean spheres. The seed is the proved original boundary-quotient
comparison, and the recursive maps use the exact original ordered splitting.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower

namespace CategoryTheory.Spectra

/-- The original Orth representation sphere split into its ordered one-dimensional factors. -/
def originalOrthogonalSpherePowerIso : ∀ n : ℕ,
    PointedCGWH.orthogonalSphere.{u, v} n ≅
      tensorPowObj (PointedCGWH.orthogonalSphere.{u, v} 1) n
  | 0 => PointedCGWH.orthogonalSphereZeroIso.{u, v}
  | n + 1 => PointedCGWH.orthogonalSphereTensorIso.{u, v} n 1 ≪≫
      tensorIso (originalOrthogonalSpherePowerIso n) (Iso.refl _)

/-- The original seed identifies every factor before the original ordered splitting. -/
def originalSpherePowerComparisonIso (n : ℕ) :
    tensorPowObj PointedCGWH.sphereOne.{u, v} n ≅ PointedCGWH.orthogonalSphere.{u, v} n :=
  (tensorPowFunctor (C := PointedCGWH.{u, v}) n).mapIso
    orthogonalOneSphereIsoSphereOne.{u, v}.symm ≪≫
      (originalOrthogonalSpherePowerIso.{u, v} n).symm

/-- Degree zero uses the exact original sphere unit. -/
theorem originalSpherePowerComparisonIso_zero :
    (originalSpherePowerComparisonIso.{u, v} 0).hom =
      PointedCGWH.orthogonalSphereUnitIso.{u, v}.hom := by
  change 𝟙 (𝟙_ PointedCGWH.{u, v}) ≫ PointedCGWH.orthogonalSphereZeroIso.{u, v}.inv = _
  rw [Category.id_comp]
  rfl

/-- Every successor uses the preceding full coefficient map and the original seed. -/
theorem originalSpherePowerComparisonIso_succ (n : ℕ) :
    (originalSpherePowerComparisonIso.{u, v} (n + 1)).hom =
      ((originalSpherePowerComparisonIso.{u, v} n).hom ⊗ₘ
        orthogonalOneSphereIsoSphereOne.{u, v}.inv) ≫
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} n 1).inv := by
  change (tensorPowMap orthogonalOneSphereIsoSphereOne.{u, v}.inv n ⊗ₘ
      orthogonalOneSphereIsoSphereOne.{u, v}.inv) ≫
    ((originalOrthogonalSpherePowerIso.{u, v} n).inv ⊗ₘ 𝟙 _) ≫
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} n 1).inv = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
  rfl

/-- The original symmetric finite sphere coefficient maps to the original Orth coefficient. -/
def originalSymmetricOrthogonalCoefficientIso (A : Operad.SmallFinBijGroupoid) :
    PointedCGWH.sphereSequence.{u, v}.functor.obj A ≅
      PointedCGWH.orthogonalSphere.{u, v} A.of.len :=
  originalSpherePowerComparisonIso.{u, v} A.of.len

end CategoryTheory.Spectra
