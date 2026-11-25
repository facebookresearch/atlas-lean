/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ClosedPointDisjointSupport

/-! # Consumers for a closed point disjoint from an ideal sheaf support -/

namespace ClosedPointDisjointSupportTest

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- The exact source statement, with the original binders. -/
public theorem exactSource {O : Type u} [CommRing O] [IsLocalRing O] {X : Scheme.{u}}
    (σ : Spec (CommRingCat.of O) ⟶ X) [IsClosedImmersion σ]
    (J : X.IdealSheafData) (hJ : σ.base (IsLocalRing.closedPoint O) ∉ J.support)
    {k : Type u} [Field k] (y : J.subscheme ⟶ Spec (CommRingCat.of k)) :
    σ.ker.comap J.subschemeι = ⊤ ∧
      (σ.ker.comap J.subschemeι).IsInvertible ∧
      IsFinite ((σ.ker.comap J.subschemeι).subschemeι ≫ y) ∧
      ∀ q : Spec (CommRingCat.of k),
        ((σ.ker.comap J.subschemeι).subschemeι ≫ y).finrank q = 0 :=
  AlgebraicGeometry.Scheme.Hom.comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support
    σ J hJ y

/-- Boundary case: for the top ideal sheaf the disjointness hypothesis is
automatic, since its support is empty, and the rank conclusion holds. -/
public theorem finrank_eq_zero_top {O : Type u} [CommRing O] [IsLocalRing O]
    {X : Scheme.{u}} (σ : Spec (CommRingCat.of O) ⟶ X) [IsClosedImmersion σ]
    {k : Type u} [Field k]
    (y : (⊤ : X.IdealSheafData).subscheme ⟶ Spec (CommRingCat.of k))
    (q : Spec (CommRingCat.of k)) :
    ((σ.ker.comap (⊤ : X.IdealSheafData).subschemeι).subschemeι ≫ y).finrank q = 0 :=
  (AlgebraicGeometry.Scheme.Hom.comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support
    σ ⊤ (by
      rw [AlgebraicGeometry.Scheme.IdealSheafData.support_top]
      intro h
      exact Set.notMem_empty _ h) y).2.2.2 q

end ClosedPointDisjointSupportTest
