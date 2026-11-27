/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUnderlyingFiniteLimits
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompact
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Product comparison for two finite simplicial realizations

For simplicial sets K,L with finitely many nondegenerate simplices, the canonical comparison
|K×L|→|K|×|L| is a homeomorphism. Its source is compact, its target Hausdorff, and its
underlying map is bijective.

The statement holds in every universe u.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Simplicial MonoidalCategory

namespace SSet

private theorem prodComparison_toTop_bijective (X Y : SSet.{u}) :
    Function.Bijective (Limits.prodComparison SSet.toTop X Y) := by
  let cTop := Limits.prodComparison SSet.toTop X Y
  let cForget := Limits.prodComparison (CategoryTheory.forget TopCat)
    (SSet.toTop.obj X) (SSet.toTop.obj Y)
  let _ : IsIso cForget := inferInstance
  let _ : IsIso ((CategoryTheory.forget TopCat).map cTop ≫ cForget) := by
    rw [← Limits.prodComparison_comp]
    infer_instance
  let _ : IsIso ((CategoryTheory.forget TopCat).map cTop) :=
    IsIso.of_isIso_comp_right _ cForget
  exact (CategoryTheory.isIso_iff_bijective
    ((CategoryTheory.forget TopCat).map cTop)).mp inferInstance

/-- For finite simplicial sets K,L in an arbitrary universe u, geometric realization carries their
binary product to the topological product through the canonical comparison isomorphism. -/
theorem isIso_prodComparison_toTop_finite_finite
    (K L : SSet.{u}) [K.Finite] [L.Finite] :
    IsIso (Limits.prodComparison SSet.toTop K L) := by
  have hTensor : SSet.Finite (K ⊗ L) := by infer_instance
  let _ : SSet.Finite (K ⨯ L) := by
    exact @SSet.finite_of_iso (K ⊗ L) (K ⨯ L)
      ((CartesianMonoidalCategory.tensorLeftIsoProd K).app L) hTensor
  let c := Limits.prodComparison SSet.toTop K L
  let eProd := TopCat.prodIsoProd (SSet.toTop.obj K) (SSet.toTop.obj L)
  let c' := c ≫ eProd.hom
  have hc' : Function.Bijective c' := by
    exact (ConcreteCategory.bijective_of_isIso eProd.hom).comp
      (prodComparison_toTop_bijective K L)
  let e : ↑(SSet.toTop.obj (K ⨯ L)) ≃
      (↑(SSet.toTop.obj K) × ↑(SSet.toTop.obj L)) :=
    Equiv.ofBijective c'.hom hc'
  have he : IsHomeomorph c' :=
    (Continuous.homeoOfEquivCompactToT2 (f := e)
      c'.hom.continuous).isHomeomorph
  let _ : IsIso c' := (TopCat.isIso_iff_isHomeomorph c').mpr he
  exact IsIso.of_isIso_comp_right c eProd.hom

end SSet
