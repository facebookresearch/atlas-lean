/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWProduct
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-! # Binary-product closure for TopCat weak homotopy equivalences

Staged KQ3 packet. This file imports and reuses the sibling provider
`LegacyTopCat.TopCatWeakHomotopyEquivalence`,
which supplies
`TopCat.weakHomotopyEquivalences =
SSet.KanComplex.W.inverseImage TopCat.toSSet`; this file defines no fallback.

Binary-product closure is transported from `SSet.KanComplex.W.prodMap`
across the binary product comparison isomorphisms of the right adjoint
`TopCat.toSSet`, using `Limits.prodComparison_natural` and
`W.respectsIso`. Only binary products are claimed; no arbitrary-product
preservation is proved. No global model/category instance is added.

Mathematical source: Goerss--Jardine, Simplicial Homotopy Theory, I.3,
plus the categorical fact that a right adjoint preserves binary products.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- Binary products of TopCat weak homotopy equivalences are weak homotopy
equivalences, via `SSet.KanComplex.W.prodMap` and the product comparison
isos of the right adjoint `TopCat.toSSet`. -/
theorem weakHomotopyEquivalences.prodMap {X Y A B : TopCat.{u}}
    {f : X ⟶ Y} {g : A ⟶ B}
    (hf : weakHomotopyEquivalences f) (hg : weakHomotopyEquivalences g) :
    weakHomotopyEquivalences (Limits.prod.map f g) := by
  have hfW : SSet.KanComplex.W (TopCat.toSSet.map f) := hf
  have hgW : SSet.KanComplex.W (TopCat.toSSet.map g) := hg
  have hProd := SSet.KanComplex.W.prodMap hfW hgW
  have hNat := Limits.prodComparison_natural (F := TopCat.toSSet) f g
  have : IsIso (Limits.prodComparison TopCat.toSSet X A) := inferInstance
  have : IsIso (Limits.prodComparison TopCat.toSSet Y B) := inferInstance
  have hEq : TopCat.toSSet.map (Limits.prod.map f g) =
      Limits.prodComparison TopCat.toSSet X A ≫
        (Limits.prod.map (TopCat.toSSet.map f) (TopCat.toSSet.map g) ≫
          inv (Limits.prodComparison TopCat.toSSet Y B)) := by
    rw [← Category.comp_id (TopCat.toSSet.map (Limits.prod.map f g)),
      ← IsIso.hom_inv_id (Limits.prodComparison TopCat.toSSet Y B),
      ← Category.assoc, hNat, Category.assoc]
  have hPost := MorphismProperty.RespectsIso.postcomp SSet.KanComplex.W
    (inv (Limits.prodComparison TopCat.toSSet Y B))
    (Limits.prod.map (TopCat.toSSet.map f) (TopCat.toSSet.map g)) hProd
  have hPre := MorphismProperty.RespectsIso.precomp SSet.KanComplex.W
    (Limits.prodComparison TopCat.toSSet X A) _ hPost
  change SSet.KanComplex.W (TopCat.toSSet.map (Limits.prod.map f g))
  rw [hEq]
  exact hPre

end TopCat
