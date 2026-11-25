/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteSubcomplexCells
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteGeneratedSubcomplex

@[expose] public section

/-!
# Finite-ambient-cells client test

Minimal downstream client for `SSet.Subcomplex.AmbientCells` and
`ambientCellsEmbedding`. Fixes the vertex-0 subcomplex of `Δ[1]`, obtains its
finiteness through the `ofSimplex` wrapper, exercises the inferred
`Finite (AmbientCells ...)` instance, and checks that mapping the embedded cell
along `A.ι` recovers the ambient carrier; a bare `inferInstance` alone is not
the test.

API-reuse map (all `reuse`): `SSet.stdSimplex.const` for the vertex,
`SSet.Subcomplex.ofSimplex` for the subcomplex,
`SSet.Subcomplex.finite_ofSimplex` for subcomplex finiteness,
`SSet.Subcomplex.AmbientCells`/`ambientCellsEmbedding` for the client, and
`SSet.S.map`/`A.ι` coherence. No colimit/topology/model-category claim.
-/

set_option autoImplicit false

open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteSubcomplexCellsTests

/-- Vertex 0 of `Δ[1]` as a 0-simplex. -/
def vertex0 : (Δ[1] : SSet.{0}) _⦋0⦌ :=
  SSet.stdSimplex.const 1 0 _

/-- The vertex-0 subcomplex of `Δ[1]`. -/
abbrev vertexSubcomplex : (Δ[1] : SSet.{0}).Subcomplex :=
  SSet.Subcomplex.ofSimplex vertex0

instance : SSet.Finite (vertexSubcomplex : SSet.{0}) :=
  SSet.Subcomplex.finite_ofSimplex _ vertex0

/-- Inferred finiteness of the ambient cells, via the embedding instance. -/
theorem ambientCells_finite :
    Finite (SSet.Subcomplex.AmbientCells vertexSubcomplex) :=
  inferInstance

/-- Mapping the embedded cell along `A.ι` recovers the ambient carrier. -/
theorem ambientCells_coherence (a : SSet.Subcomplex.AmbientCells vertexSubcomplex) :
    SSet.S.map vertexSubcomplex.ι
      (SSet.Subcomplex.ambientCellsEmbedding vertexSubcomplex a).toS =
      a.val.toS := rfl

#print axioms ambientCells_finite
#print axioms ambientCells_coherence

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteSubcomplexCellsTests
