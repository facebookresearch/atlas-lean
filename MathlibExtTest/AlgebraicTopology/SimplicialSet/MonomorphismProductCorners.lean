/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.MonomorphismProductCorners
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Clients of the simplicial product-corner image criterion

Either coordinate suffices for a preimage. The pair of vertices of two
zero-simplices does not lie in the corner of their boundary inclusions.

The original Formal-Math development is by Tsutomu Okano and Avocado.
-/

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace MonomorphismProductCornersTest

variable {A B K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L) [Mono i] [Mono j]

-- A preimage in either factor gives a preimage in the actual pushout source.
example (n : SimplexCategoryᵒᵖ) (a : A.obj n) (l : L.obj n) :
    ∃ x : (Arrow.mk i □ Arrow.mk j).left.obj n,
      (Arrow.mk i □ Arrow.mk j).hom.app n x = (i.app n a, l) :=
  (SSet.mem_range_pushoutProduct_iff i j n (i.app n a) l).mpr (Or.inr ⟨a, rfl⟩)

example (n : SimplexCategoryᵒᵖ) (b : B.obj n) (k : K.obj n) :
    ∃ x : (Arrow.mk i □ Arrow.mk j).left.obj n,
      (Arrow.mk i □ Arrow.mk j).hom.app n x = (b, j.app n k) :=
  (SSet.mem_range_pushoutProduct_iff i j n b (j.app n k)).mpr (Or.inl ⟨k, rfl⟩)

-- The range is not necessarily the whole product: neither boundary contains the vertex.
example :
    let arrow := Arrow.mk (SSet.boundary.{u} 0).ι
    let vertex : (Δ[0] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.objMk .id
    (vertex, vertex) ∉ Set.range ((arrow □ arrow).hom.app (op ⦋0⦌)) := by
  dsimp only
  rw [SSet.mem_range_pushoutProduct_iff, or_self]
  rintro ⟨⟨simplex, hsimplex⟩, heq⟩
  change simplex = SSet.stdSimplex.objMk .id at heq
  exact SSet.stdSimplex.notMem_boundary 0 (heq ▸ hsimplex)

end MonomorphismProductCornersTest
