/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationFiniteProductComparisonArbitrary

/-!
# Finite-times-arbitrary realization regression (KQ3)

Concrete universe-zero consumer for
`SSet.isIso_prodComparison_toTop_finite_arbitrary` with finite left `Δ[1]`
and right factor the `ℕ`-indexed coproduct of `Δ[0]`. The comparison `IsIso`
is made load-bearing through instance inference (no explicit IsIso
hypothesis). The coproduct-leg naturality fixes the left-finite orientation:
a finite-right-only statement or swapped factors do not prove it.

Explicit nonclaims: no arbitrary-times-arbitrary instance, no global
realization product-preservation instance, no fibration, no anodyne, no
weak-equivalence, and no model-category result.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.FiniteArbitraryTests

/-- Arbitrary right factor: `ℕ`-indexed coproduct of points. -/
noncomputable abbrev Right : SSet.{0} := ∐ fun _ : ℕ => (Δ[0] : SSet.{0})

/-- Finite-times-arbitrary comparison is an iso, via instance inference. -/
theorem isIso_prodComparison_finite_arbitrary :
    IsIso (Limits.prodComparison SSet.toTop (Δ[1] : SSet.{0}) Right) := by
  have := SSet.isIso_prodComparison_toTop_finite_arbitrary (Δ[1] : SSet.{0}) Right
  exact inferInstance

/-- Coproduct-leg naturality with the finite factor fixed on the left. -/
theorem prodComparison_coproduct_leg (k : ℕ) :
    SSet.toTop.map (Limits.prod.map (𝟙 (Δ[1] : SSet.{0}))
        (Limits.Sigma.ι (fun _ : ℕ => (Δ[0] : SSet.{0})) k)) ≫
      Limits.prodComparison SSet.toTop (Δ[1] : SSet.{0}) Right =
    Limits.prodComparison SSet.toTop (Δ[1] : SSet.{0}) (Δ[0] : SSet.{0}) ≫
      Limits.prod.map (𝟙 _) (SSet.toTop.map
        (Limits.Sigma.ι (fun _ : ℕ => (Δ[0] : SSet.{0})) k)) := by
  simpa [Right] using Limits.prodComparison_natural (F := SSet.toTop)
    (𝟙 (Δ[1] : SSet.{0}))
    (Limits.Sigma.ι (fun _ : ℕ => (Δ[0] : SSet.{0})) k)

/-- Finite-by-finite comparison at a symbolic universe. -/
theorem finiteFinite_symbolic
    (K L : SSet.{u}) [K.Finite] [L.Finite] :
    IsIso (Limits.prodComparison SSet.toTop K L) :=
  SSet.isIso_prodComparison_toTop_finite_finite K L

/-- Finite-left/arbitrary-right comparison at a symbolic universe. -/
theorem finiteArbitrary_symbolic
    (K Y : SSet.{u}) [K.Finite] :
    IsIso (Limits.prodComparison SSet.toTop K Y) :=
  SSet.isIso_prodComparison_toTop_finite_arbitrary K Y

/-- The comparison points from realization of a product to the product of realizations. -/
noncomputable def comparisonOrientation_symbolic
    (K Y : SSet.{u}) :
    SSet.toTop.obj (K ⨯ Y) ⟶
      (SSet.toTop.obj K ⨯ SSet.toTop.obj Y) :=
  Limits.prodComparison SSet.toTop K Y

/-- Concrete universe-one finite-by-finite comparison. -/
theorem finiteFinite_u1
    (K L : SSet.{1}) [K.Finite] [L.Finite] :
    IsIso (Limits.prodComparison SSet.toTop K L) :=
  SSet.isIso_prodComparison_toTop_finite_finite K L

/-- Concrete universe-one standard-simplex-left comparison. -/
theorem standardSimplexLeft_u1 (Y : SSet.{1}) :
    IsIso (Limits.prodComparison SSet.toTop
      (Δ[2] : SSet.{1}) Y) :=
  SSet.isIso_prodComparison_toTop_finite_arbitrary _ _

/-- Neither-finite ordinary comparisons are not inferred. -/
example (_K _Y : SSet.{1}) : True := by
  fail_if_success
    let _ : IsIso (Limits.prodComparison SSet.toTop _K _Y) :=
      inferInstance
  trivial

/-- Realization has no global binary-product preservation dictionary. -/
example : True := by
  fail_if_success
    let _ : PreservesBinaryProducts SSet.toTop.{1} := inferInstance
  trivial

#print axioms SSet.isIso_prodComparison_toTop_finite_finite
#print axioms SSet.isIso_prodComparison_toTop_finite_arbitrary
#print axioms isIso_prodComparison_finite_arbitrary
#print axioms prodComparison_coproduct_leg

end MathlibExtTest.AlgebraicTopology.ModelCategory.FiniteArbitraryTests
