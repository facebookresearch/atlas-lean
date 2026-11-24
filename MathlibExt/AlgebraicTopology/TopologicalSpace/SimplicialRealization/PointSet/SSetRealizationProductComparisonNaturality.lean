/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Pointwise naturality for the SSet realization product comparison

KQ3 only. SSet realization specificity throughout.

This file provides the pointwise naturality equation for
`Limits.prodComparison SSet.toTop` through `Limits.prodComparison_natural`
and `ConcreteCategory.congr_hom`, with only the narrow explicit
`ConcreteCategory.comp_apply` normalization. Neither comparison is required
to be an iso.

Explicit nonclaims: no inverse lemma, no injectivity lemma, no boundary
theorem, no client, no arbitrary-functor generality, no colimit, and no
model-category claim.
-/

@[expose] public section

open CategoryTheory Limits Simplicial

universe u

namespace SSet

/-- Pointwise naturality of the SSet realization product comparison in every
universe. -/
theorem prodComparison_toTop_natural_apply
    {X Y X' Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p : ↑(SSet.toTop.obj (X ⨯ Y))) :
    (Limits.prodComparison SSet.toTop X' Y')
        ((SSet.toTop.map (Limits.prod.map f g)) p) =
      (Limits.prod.map (SSet.toTop.map f) (SSet.toTop.map g))
        ((Limits.prodComparison SSet.toTop X Y) p) := by
  have hNat := Limits.prodComparison_natural (F := SSet.toTop) f g
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom hNat p

end SSet
