/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeSphereHom
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SuspendedSphereHom

/-!
# Original scalar-suspended free sphere Hom classes

The actual free/evaluation Quillen pair carries the full suspended sphere
correspondence to every native enriched index. Both functions retain the
same free coefficient, complete spectrum map and actual evaluated target.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
private abbrev H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)

omit B in
private theorem suspendedSphere_isCofibrant (n : ℕ) :
    IsCofibrant (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere.{u, v} n)) := by
  let _ : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} n) := sphere_isCofibrant n
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := PointedCGWH.suspensionLoopAdjunction) inferInstance

/-- The original suspended free coefficient represents the next evaluated homotopy degree. -/
def suspendedFreeSpherePiHomEquiv (a : I) (n : ℕ)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PointedCGWH.piN (n + 1) (X.toEnrichedFunctor.obj a) ≃
      (H.obj ((EnrichedFunctorCat.Free.functor a).obj
        (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n))) ⟶ H.obj X) := by
  let _ : IsCofibrant
      (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere.{u, v} n)) :=
    suspendedSphere_isCofibrant n
  exact (PointedCGWH.SphereHom.suspendedSpherePiHomEquiv n (X.toEnrichedFunctor.obj a)).trans
    (freeHoHomEquiv a
      (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n)) X).symm

/-- The complete forward correspondence preserves every actual native target map. -/
theorem suspendedFreeSpherePiHomEquiv_naturality (a : I) (n : ℕ)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (x : PointedCGWH.piN (n + 1) (X.toEnrichedFunctor.obj a)) :
    suspendedFreeSpherePiHomEquiv a n Y
        (PointedCGWH.piNMap (n + 1) (EnrichedFunctorCat.component f a) x) =
      suspendedFreeSpherePiHomEquiv a n X x ≫ H.map f := by
  let _ : IsCofibrant
      (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere.{u, v} n)) :=
    suspendedSphere_isCofibrant n
  change (freeHoHomEquiv a
      (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n)) Y).symm
      (PointedCGWH.SphereHom.suspendedSpherePiHomEquiv n (Y.toEnrichedFunctor.obj a)
        (PointedCGWH.piNMap (n + 1) (EnrichedFunctorCat.component f a) x)) = _
  rw [PointedCGWH.SphereHom.suspendedSpherePiHomEquiv_naturality,
    freeHoHomEquiv_inverse_naturality]
  rfl

/-- The complete inverse uses the same original evaluated component and target map. -/
theorem suspendedFreeSpherePiHomEquiv_inverse_naturality (a : I) (n : ℕ)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (g : H.obj ((EnrichedFunctorCat.Free.functor a).obj
      (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n))) ⟶ H.obj X) :
    (suspendedFreeSpherePiHomEquiv a n Y).symm (g ≫ H.map f) =
      PointedCGWH.piNMap (n + 1) (EnrichedFunctorCat.component f a)
        ((suspendedFreeSpherePiHomEquiv a n X).symm g) := by
  apply (suspendedFreeSpherePiHomEquiv a n Y).injective
  rw [Equiv.apply_symm_apply, suspendedFreeSpherePiHomEquiv_naturality, Equiv.apply_symm_apply]

end HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom
