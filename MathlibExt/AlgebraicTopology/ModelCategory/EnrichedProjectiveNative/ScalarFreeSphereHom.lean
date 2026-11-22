/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.SuspendedFreeSphereHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.SuspendedFreeSphere
import MathlibExt.CategoryTheory.Enriched.ScalarFreeEvaluation

/-!
# Original scalar images of free sphere homotopy classes

The genuine free identity evaluation and scalar/free associator retain
the original scalar image of every represented sphere class. The actual
suspension unit supplies the next-degree class, with no stable-equivalence
or source-comparison conclusion assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SphereHom

attribute [local instance] PointedCGWH.modelCategory.allObjectsFibrant
private abbrev P := toHomotopyCategory PointedCGWH.{u, v}

/-- Suspending an actual sphere representative gives precisely the original unit-induced class. -/
theorem suspendedSpherePiHomEquiv_scalarMap (n : ℕ) (X : PointedCGWH.{u, v})
    (x : PointedCGWH.piN n X) (f : sphere n ⟶ X)
    (hf : P.map f = spherePiHomEquiv n X x) :
    suspendedSpherePiHomEquiv n (PointedCGWH.suspension.obj X)
        (sphereSuspensionClass n X x) = P.map (PointedCGWH.suspension.map f) := by
  let _ : IsCofibrant (sphere.{u, v} n) :=
    HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom.sphere_isCofibrant n
  have hAdj : PointedCGWH.suspensionLoopAdjunction.homEquiv (sphere n)
      (PointedCGWH.suspension.obj X) (PointedCGWH.suspension.map f) =
      f ≫ PointedCGWH.suspensionLoopAdjunction.unit.app X := by
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using
      PointedCGWH.suspensionLoopAdjunction.homEquiv_naturality_left f
        (𝟙 (PointedCGWH.suspension.obj X))
  rw [suspendedSpherePiHomEquiv_unit, ← hf]
  apply (QuillenOrdinaryHoHom.homEquiv PointedCGWH.suspensionLoopAdjunction
    (sphere n) (PointedCGWH.suspension.obj X)).injective
  rw [Equiv.apply_symm_apply, QuillenOrdinaryHoHom.homEquiv_map, hAdj, P.map_comp]

end PointedCGWH.SphereHom

namespace HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
private abbrev H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
private abbrev P := toHomotopyCategory PointedCGWH.{u, v}
private abbrev T := EnrichedFunctorCat.tensorLeft (A := I) PointedCGWH.sphereOne

/-- The complete localized free evaluation keeps the same scalar/free source comparison. -/
theorem freeHoHomEquiv_scalarMap (a : I) (n : ℕ)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (f : (EnrichedFunctorCat.Free.functor a).obj (PointedCGWH.SphereHom.sphere n) ⟶ X) :
    letI : IsCofibrant (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n)) :=
      Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
        (adj := PointedCGWH.suspensionLoopAdjunction) (sphere_isCofibrant n)
    freeHoHomEquiv (B := B) a
        (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n)) (T.obj X)
        (H.map ((scalarFreeSphereIso a n).inv ≫ T.map f)) =
      P.map (PointedCGWH.suspension.map
        (EnrichedFunctorCat.Free.evaluate a (PointedCGWH.SphereHom.sphere n) X f)) := by
  let _ : IsCofibrant (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere.{u, v} n)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := PointedCGWH.suspensionLoopAdjunction) (sphere_isCofibrant n)
  let _ : (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    Native.freeAtEvaluation_isQuillenAdjunction a
  change QuillenOrdinaryHoHom.homEquiv (EnrichedFunctorCat.Free.adjunction a)
      (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n)) (T.obj X)
      (H.map ((scalarFreeSphereIso a n).inv ≫ T.map f)) = _
  rw [QuillenOrdinaryHoHom.homEquiv_map, EnrichedFunctorCat.Free.adjunction_homEquiv]
  exact P.congr_map
    (EnrichedFunctorCat.Free.evaluate_scalarFreeIso PointedCGWH.sphereOne a
      (PointedCGWH.SphereHom.sphere n) X f)

/-- Every represented free sphere class has its exact original scalar unit image. -/
theorem suspendedFreeSpherePiHomEquiv_scalarMap (a : I) (n : ℕ)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (x : PointedCGWH.piN n (X.toEnrichedFunctor.obj a))
    (f : (EnrichedFunctorCat.Free.functor a).obj (PointedCGWH.SphereHom.sphere n) ⟶ X)
    (hf : H.map f = freeSpherePiHomEquiv (B := B) a n X x) :
    suspendedFreeSpherePiHomEquiv (B := B) a n (T.obj X)
        (PointedCGWH.SphereHom.sphereSuspensionClass n (X.toEnrichedFunctor.obj a) x) =
      H.map ((scalarFreeSphereIso a n).inv ≫ T.map f) := by
  let _ : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} n) := sphere_isCofibrant n
  let _ : IsCofibrant (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere.{u, v} n)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := PointedCGWH.suspensionLoopAdjunction) (sphere_isCofibrant n)
  let _ : (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    Native.freeAtEvaluation_isQuillenAdjunction a
  have hEval := congrArg (freeHoHomEquiv (B := B) a (PointedCGWH.SphereHom.sphere n) X) hf
  change freeHoHomEquiv (B := B) a (PointedCGWH.SphereHom.sphere n) X (H.map f) =
    (freeHoHomEquiv (B := B) a (PointedCGWH.SphereHom.sphere n) X)
      ((freeHoHomEquiv (B := B) a (PointedCGWH.SphereHom.sphere n) X).symm
        (PointedCGWH.SphereHom.spherePiHomEquiv n (X.toEnrichedFunctor.obj a) x)) at hEval
  rw [Equiv.apply_symm_apply] at hEval
  have hMap : freeHoHomEquiv (B := B) a (PointedCGWH.SphereHom.sphere n) X (H.map f) =
      P.map (EnrichedFunctorCat.Free.evaluate a (PointedCGWH.SphereHom.sphere n) X f) := by
    change QuillenOrdinaryHoHom.homEquiv (EnrichedFunctorCat.Free.adjunction a)
      (PointedCGWH.SphereHom.sphere n) X (H.map f) = _
    rw [QuillenOrdinaryHoHom.homEquiv_map, EnrichedFunctorCat.Free.adjunction_homEquiv]
    rfl
  apply (freeHoHomEquiv (B := B) a
    (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n)) (T.obj X)).injective
  change (freeHoHomEquiv (B := B) a
      (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n)) (T.obj X))
      ((freeHoHomEquiv (B := B) a
        (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n)) (T.obj X)).symm
        (PointedCGWH.SphereHom.suspendedSpherePiHomEquiv n
          (PointedCGWH.suspension.obj (X.toEnrichedFunctor.obj a))
          (PointedCGWH.SphereHom.sphereSuspensionClass n (X.toEnrichedFunctor.obj a) x))) = _
  rw [Equiv.apply_symm_apply, freeHoHomEquiv_scalarMap]
  exact PointedCGWH.SphereHom.suspendedSpherePiHomEquiv_scalarMap n
    (X.toEnrichedFunctor.obj a) x
    (EnrichedFunctorCat.Free.evaluate a (PointedCGWH.SphereHom.sphere n) X f)
    (hMap.symm.trans hEval)

end HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom
