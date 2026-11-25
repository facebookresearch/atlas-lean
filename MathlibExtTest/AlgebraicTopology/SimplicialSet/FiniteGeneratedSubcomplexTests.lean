/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteGeneratedSubcomplex

@[expose] public section

/-!
# Finite-generated-subcomplex client test

Minimal downstream client for `SSet.Subcomplex.finite_iSup_ofSimplex`.
Uses the explicit two-vertex family of `Δ[1]`, obtains finiteness of the
supremum of the generated subcomplexes through the wrapper, and exercises
membership/`≤` facts for both generators so a wrong family cannot pass.

API-reuse map (all `reuse`): `SSet.stdSimplex.const` and
`SSet.stdSimplex.obj₀Equiv` for the vertices, `SSet.Subcomplex.ofSimplex`,
`SSet.Subcomplex.finite_iSup_ofSimplex`,
`SSet.Subcomplex.mem_ofSimplex_obj` for membership, and core `le_iSup` for
the generator inequalities. No generic restatement and no
colimit/topology/model-category claim.
-/

set_option autoImplicit false

open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteGeneratedSubcomplexTests

/-- The two vertices of `Δ[1]`, at fixed degree `0`. -/
def vertex : Fin 2 → (Δ[1] : SSet.{0}) _⦋0⦌ :=
  fun i => SSet.stdSimplex.const 1 i _

/-- The two vertices as an explicit finite family of simplices. -/
def vertexPair : Fin 2 → Σ n, (Δ[1] : SSet.{0}) _⦋n⦌ :=
  fun i => ⟨0, vertex i⟩

/-- The entries really are the two distinct vertices. -/
lemma vertex_applied (i : Fin 2) :
    SSet.stdSimplex.obj₀Equiv (vertex i) = i := by
  simp [vertex, SSet.stdSimplex.const]

lemma vertex_zero_ne_one : vertex 0 ≠ vertex 1 := by
  intro h
  have h0 := vertex_applied 0
  have h1 := vertex_applied 1
  rw [h] at h0
  exact absurd (h1.symm.trans h0) (by decide)

/-- Finiteness of the supremum, through the wrapper (not synthesized). -/
theorem vertexSupFinite :
    SSet.Finite
      ((⨆ i, SSet.Subcomplex.ofSimplex (vertexPair i).2 :
        (Δ[1] : SSet.{0}).Subcomplex) : SSet.{0}) :=
  SSet.Subcomplex.finite_iSup_ofSimplex _ vertexPair

/-- Each generator lies in its own generated subcomplex. -/
lemma vertex_mem_ofSimplex (i : Fin 2) :
    (vertexPair i).2 ∈ (SSet.Subcomplex.ofSimplex (vertexPair i).2).obj _ :=
  SSet.Subcomplex.mem_ofSimplex_obj _

/-- Each generator lies below the supremum. -/
lemma vertex_ofSimplex_le_sup (i : Fin 2) :
    SSet.Subcomplex.ofSimplex (vertexPair i).2 ≤
      ⨆ j, SSet.Subcomplex.ofSimplex (vertexPair j).2 :=
  le_iSup (fun j => SSet.Subcomplex.ofSimplex (vertexPair j).2) i

/-- Each generator is a member of the supremum subcomplex. -/
lemma vertex_mem_sup (i : Fin 2) :
    (vertexPair i).2 ∈
      (⨆ j, SSet.Subcomplex.ofSimplex (vertexPair j).2 :
        (Δ[1] : SSet.{0}).Subcomplex).obj _ :=
  (vertex_ofSimplex_le_sup i) _ (vertex_mem_ofSimplex i)

#print axioms vertexSupFinite
#print axioms vertex_zero_ne_one
#print axioms vertex_mem_sup

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteGeneratedSubcomplexTests
