/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SphereHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelFibrancy
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarSphereSuspensionComparison

/-!
# Original native free-sphere representatives of evaluated homotopy classes

The actual original free/evaluation Quillen pair transports both localized
Hom functions. The native sphere representatives therefore give the full
cube-class/free-spectrum-Hom correspondence at every original index and
degree. Both functions retain the original evaluation components and all
spectrum target-map naturalities.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
private abbrev H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
private abbrev P := toHomotopyCategory PointedCGWH.{u, v}

/-- The actual native free/evaluation Quillen pair retains complete localized Hom functions. -/
def freeHoHomEquiv (a : I) (K : PointedCGWH.{u, v}) [IsCofibrant K]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (H.obj ((EnrichedFunctorCat.Free.functor a).obj K) ⟶ H.obj X) ≃
      (P.obj K ⟶ P.obj (X.toEnrichedFunctor.obj a)) := by
  let _ : (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    Native.freeAtEvaluation_isQuillenAdjunction a
  exact QuillenOrdinaryHoHom.homEquiv (EnrichedFunctorCat.Free.adjunction a) K X

omit B in
/-- The actual sphere source retains cofibrancy through each original scalar adjunction. -/
theorem sphere_isCofibrant (n : ℕ) : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} n) := by
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  let _ : IsCofibrant PointedCGWH.SphereHom.freePoint.{u, v} :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := PointedCGWH.SphereHom.powerAdjunction n) inferInstance

/-- Original level cube classes have actual original native free-sphere map representatives. -/
def freeSpherePiHomEquiv (a : I) (n : ℕ)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PointedCGWH.piN n (X.toEnrichedFunctor.obj a) ≃
      (H.obj ((EnrichedFunctorCat.Free.functor a).obj (PointedCGWH.SphereHom.sphere n)) ⟶
        H.obj X) := by
  let _ : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} n) := sphere_isCofibrant n
  exact (PointedCGWH.SphereHom.spherePiHomEquiv n (X.toEnrichedFunctor.obj a)).trans
    (freeHoHomEquiv a (PointedCGWH.SphereHom.sphere n) X).symm

/-- Original target maps retain the full free/evaluation Hom square. -/
theorem freeHoHomEquiv_naturality (a : I) (K : PointedCGWH.{u, v}) [IsCofibrant K]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (g : H.obj ((EnrichedFunctorCat.Free.functor a).obj K) ⟶ H.obj X) :
    freeHoHomEquiv a K Y (g ≫ H.map f) =
      freeHoHomEquiv a K X g ≫ P.map (EnrichedFunctorCat.component f a) := by
  let _ : (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    Native.freeAtEvaluation_isQuillenAdjunction a
  exact QuillenOrdinaryHoHom.homEquiv_naturality_right (EnrichedFunctorCat.Free.adjunction a) K g f

/-- The inverse function retains the same original evaluation component. -/
theorem freeHoHomEquiv_inverse_naturality (a : I) (K : PointedCGWH.{u, v}) [IsCofibrant K]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (g : P.obj K ⟶ P.obj (X.toEnrichedFunctor.obj a)) :
    (freeHoHomEquiv a K Y).symm (g ≫ P.map (EnrichedFunctorCat.component f a)) =
      (freeHoHomEquiv a K X).symm g ≫ H.map f := by
  apply (freeHoHomEquiv a K Y).injective
  rw [Equiv.apply_symm_apply, freeHoHomEquiv_naturality, Equiv.apply_symm_apply]

/-- Every original level cube class preserves the actual complete spectrum target map. -/
theorem freeSpherePiHomEquiv_naturality (a : I) (n : ℕ)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (x : PointedCGWH.piN n (X.toEnrichedFunctor.obj a)) :
    freeSpherePiHomEquiv a n Y (PointedCGWH.piNMap n (EnrichedFunctorCat.component f a) x) =
      freeSpherePiHomEquiv a n X x ≫ H.map f := by
  let _ : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} n) := sphere_isCofibrant n
  change (freeHoHomEquiv a (PointedCGWH.SphereHom.sphere n) Y).symm
      (PointedCGWH.SphereHom.spherePiHomEquiv n (Y.toEnrichedFunctor.obj a)
        (PointedCGWH.piNMap n (EnrichedFunctorCat.component f a) x)) = _
  rw [PointedCGWH.SphereHom.spherePiHomEquiv_naturality,
    freeHoHomEquiv_inverse_naturality]
  rfl

/-- The complete inverse sphere representative function retains every target map. -/
theorem freeSpherePiHomEquiv_inverse_naturality (a : I) (n : ℕ)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (g : H.obj ((EnrichedFunctorCat.Free.functor a).obj (PointedCGWH.SphereHom.sphere n)) ⟶
      H.obj X) :
    (freeSpherePiHomEquiv a n Y).symm (g ≫ H.map f) =
      PointedCGWH.piNMap n (EnrichedFunctorCat.component f a)
        ((freeSpherePiHomEquiv a n X).symm g) := by
  apply (freeSpherePiHomEquiv a n Y).injective
  rw [Equiv.apply_symm_apply, freeSpherePiHomEquiv_naturality, Equiv.apply_symm_apply]

end HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom
