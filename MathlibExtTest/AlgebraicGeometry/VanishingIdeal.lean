/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.VanishingIdeal

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

example {X : Scheme.{u}} (Z : Closeds X) : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Z

example {X Y T : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (f : T ⟶ X) [IsReduced T]
    (H : Set.range f.base ⊆ Set.range i.base) :
    ∃! g : T ⟶ Y, g ≫ i = f :=
  AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced i f H
