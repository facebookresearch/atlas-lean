/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeSphereHom
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SphereNullHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Zero
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoCofiberKernel

/-!
# Original null classes of native free-sphere Hom functions

The original diagram zero and its evaluated native zero prove that the
actual free/evaluation adjunct preserves null maps. The full localized
Hom functions and sphere representatives therefore preserve the same
original null class. The zero-adjunct universal-property argument is
adapted from the project's orthogonal scalar null-Hom construction,
credited to Tsutomu Okano.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped CGWH.modelCategory ZeroObject

namespace HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
private abbrev H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
private abbrev P := toHomotopyCategory PointedCGWH.{u, v}

private instance nativeHasZero : HasZeroObject (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  Diagrams.nativeHasZeroObject

/-- The complete Quillen Hom functions preserve the original coefficient null map. -/
theorem freeHoHomEquiv_null (a : I) (K : PointedCGWH.{u, v}) [IsCofibrant K]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    freeHoHomEquiv (B := B) a K X
      (OrdinaryHoCofiberKernel.nullHom ((EnrichedFunctorCat.Free.functor a).obj K) X) =
      OrdinaryHoCofiberKernel.nullHom K (X.toEnrichedFunctor.obj a) := by
  let _ : (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    Native.freeAtEvaluation_isQuillenAdjunction a
  rw [OrdinaryHoCofiberKernel.nullHom]
  change QuillenOrdinaryHoHom.homEquiv (EnrichedFunctorCat.Free.adjunction a) K X
      (H.map (OrdinaryHoCofiberKernel.nullMap _ X)) = _
  rw [QuillenOrdinaryHoHom.homEquiv_map]
  let adj := EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a
  let Z : EnrichedFunctorCat PointedCGWH.{u, v} I := Diagrams.zeroDiagram
  let hZ : IsZero ((EnrichedFunctorCat.evaluation a).obj Z) :=
    Diagrams.initialDiagram_component_isZero a
  have hA : adj.homEquiv K Z (Diagrams.toZero ((EnrichedFunctorCat.Free.functor a).obj K)) =
      hZ.isTerminal.from K := hZ.isTerminal.hom_ext _ _
  have hR : (EnrichedFunctorCat.evaluation a).map (Diagrams.zeroTo X) =
      hZ.isInitial.to (X.toEnrichedFunctor.obj a) := hZ.isInitial.hom_ext _ _
  have hNull : OrdinaryHoCofiberKernel.nullMap ((EnrichedFunctorCat.Free.functor a).obj K) X =
      Diagrams.toZero ((EnrichedFunctorCat.Free.functor a).obj K) ≫ Diagrams.zeroTo X :=
    (OrdinaryHoChosenPuppe.actualNullMap_eq_chosen
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero _ X).symm
  rw [hNull, adj.homEquiv_naturality_right, hA, hR]
  exact P.congr_map (OrdinaryHoChosenPuppe.actualNullMap_eq_chosen
    ((EnrichedFunctorCat.evaluation a).obj Z) hZ K (X.toEnrichedFunctor.obj a))

/-- Original null cube classes give the actual native free-sphere null morphism. -/
theorem freeSpherePiHomEquiv_null (a : I) (n : ℕ)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    freeSpherePiHomEquiv (B := B) a n X
      (PointedCGWH.SphereHom.nullCube n (X.toEnrichedFunctor.obj a)) =
      OrdinaryHoCofiberKernel.nullHom
        ((EnrichedFunctorCat.Free.functor a).obj (PointedCGWH.SphereHom.sphere n)) X := by
  let _ : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} n) := sphere_isCofibrant n
  change (freeHoHomEquiv a (PointedCGWH.SphereHom.sphere n) X).symm
      (PointedCGWH.SphereHom.spherePiHomEquiv n (X.toEnrichedFunctor.obj a)
        (PointedCGWH.SphereHom.nullCube n (X.toEnrichedFunctor.obj a))) = _
  rw [PointedCGWH.SphereHom.spherePiHomEquiv_nullCube]
  apply (freeHoHomEquiv a (PointedCGWH.SphereHom.sphere n) X).injective
  rw [Equiv.apply_symm_apply, freeHoHomEquiv_null]

end HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom
