/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Naturality of the realization product comparison

Gives the pointwise naturality equation for the canonical product comparison of simplicial realization, for arbitrary maps in both factors. The equation uses the comparison maps without invertibility hypotheses.
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
