/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUnderlyingFiniteLimits
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompact
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Finite-by-finite realization product comparison

For finite simplicial sets `K L : SSet.{u}`, the product comparison
`Limits.prodComparison SSet.toTop K L` is an isomorphism.

The underlying comparison is bijective because underlying realization
preserves finite limits. The source realization is compact, while the product
of the two target realizations is Hausdorff, so the continuous bijection is a
homeomorphism.

Explicit nonclaims: no arbitrary-product preservation, weak-equivalence,
fibration, cofibration, DeltaGenerated-space, or model-category result.
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

/-- Finite-by-finite realization product comparison iso. -/
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
