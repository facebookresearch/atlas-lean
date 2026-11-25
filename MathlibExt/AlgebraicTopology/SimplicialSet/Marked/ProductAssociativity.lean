/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Products
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# Original marked product associativity and maximal parameter products

The native simplicial associator preserves exactly the same intersection
of the three original mark sets. Products of maximally marked parameters
are the maximal marking of the same original simplicial product.
The original product maps induce the corresponding marked isomorphisms.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace SSet.Marked

/-- The original product of two actual marked isomorphisms keeps both whole component maps. -/
def prodIso {X X' Y Y' : Marked.{u}} (e : X ≅ X') (f : Y ≅ Y') : prod X Y ≅ prod X' Y' where
  hom := prodMap e.hom f.hom
  inv := prodMap e.inv f.inv
  hom_inv_id := by rw [← prodMap_comp, e.hom_inv_id, f.hom_inv_id, prodMap_id]
  inv_hom_id := by rw [← prodMap_comp, e.inv_hom_id, f.inv_hom_id, prodMap_id]

/-- The native marked associator keeps every original simplex and precisely the same three mark predicates. -/
def prodAssociator (X Y Z : Marked.{u}) : prod (prod X Y) Z ≅ prod X (prod Y Z) where
  hom := ⟨(α_ X.toSSet Y.toSSet Z.toSSet).hom, fun he => ⟨he.1.1, ⟨he.1.2, he.2⟩⟩⟩
  inv := ⟨(α_ X.toSSet Y.toSSet Z.toSSet).inv, fun he => ⟨⟨he.1, he.2.1⟩, he.2.2⟩⟩
  hom_inv_id := Hom.ext (α_ X.toSSet Y.toSSet Z.toSSet).hom_inv_id
  inv_hom_id := Hom.ext (α_ X.toSSet Y.toSSet Z.toSSet).inv_hom_id

/-- The product of the two original maximal markings is the maximal marking of their same original
  simplicial product. -/
def maxProductIso (A K : SSet.{u}) : prod (max A) (max K) ≅ max (A ⊗ K) :=
  isoMk (Iso.refl _) (fun _ => ⟨fun _ => Set.mem_univ _, fun _ => ⟨Set.mem_univ _, Set.mem_univ _⟩⟩)

end SSet.Marked
