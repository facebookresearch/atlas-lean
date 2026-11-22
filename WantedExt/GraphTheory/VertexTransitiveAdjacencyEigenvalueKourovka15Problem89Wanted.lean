/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Adjacency eigenvalues of vertex-transitive graphs (Kourovka Notebook Problem 15.89)

Kourovka Notebook, Problem 15.89 (V. I. Trofimov): let `Γ` be an infinite undirected connected
vertex-symmetric graph of finite valency without loops or multiple edges. Is it true that every
complex number is an eigenvalue of the adjacency matrix of `Γ` acting on the complex vector space of
all complex-valued functions on the vertex set of `Γ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MathlibExt.GraphTheory.VertexTransitiveAdjacencyEigenvalueKourovka15Problem89Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.89 (V. I. Trofimov). UnsolvedMath record
UM-00701177 (`KOU-15.89`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are Mathlib `SimpleGraph`s (no loops or multiple edges) with `LocallyFinite` (finite
valency); vertex-symmetric means the automorphism group is transitive on vertices. The adjacency
operator sends `f` to `v ↦ ∑_{w ~ v} f w` on all functions `V → ℂ`, and `z` is an eigenvalue when
some nonzero `f` satisfies `A f = z f`.
-/

/-- Kourovka 15.89 (V. I. Trofimov): for every infinite connected vertex-transitive locally finite
simple graph `Γ` and every `z ∈ ℂ` there is a nonzero `f : V → ℂ` with `∑_{w ~ v} f w = z f v`
for every vertex `v`, i.e. every complex number is an eigenvalue of the adjacency operator on all
functions `V → ℂ`. -/
def everyComplexNumberIsAdjacencyEigenvalue : Prop :=
  ∀ (V : Type) (Γ : SimpleGraph V) [Γ.LocallyFinite], Infinite V → Γ.Connected →
    (∀ v w : V, ∃ φ : Γ ≃g Γ, φ v = w) →
      ∀ z : ℂ, ∃ f : V → ℂ, f ≠ 0 ∧ ∀ v, ∑ w ∈ Γ.neighborFinset v, f w = z * f v

/--
Resolved false: Jayadevan showed that the Cayley graph of `⟨a, t | a³ = t² = 1⟩` with respect to
`{a^i t a^j : 1 ≤ i, j ≤ 2}` is infinite, connected, simple, four-regular and vertex-transitive, and
that its adjacency operator on `ℂ^G` has point spectrum exactly `ℂ ∖ {0}`, so `0` is not an
eigenvalue; the Kourovka Notebook (21st issue) marks 15.89 solved, "No, not always" (AI solution
confirmed by V. I. Trofimov). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.89 (V. I.
Trofimov); resolution: A. Jayadevan, Punctured point spectrum of a four-regular bipartite Cayley
graph, preprint, Zenodo record 22722077 (2026), AI-generated solution confirmed by V. I. Trofimov,
main theorem (for G = ⟨a, t | a³ = t² = 1⟩ and S = {a^i t a^j : 1 ≤ i, j ≤ 2}, the Cayley graph is
infinite, connected, simple, 4-regular and vertex-transitive with point spectrum ℂ ∖ {0}); the
Kourovka Notebook (21st issue) marks 15.89 solved, https://zenodo.org/records/22722077.
-/
public theorem_wanted everyComplexNumberIsAdjacencyEigenvalue_refuted :
    ¬ everyComplexNumberIsAdjacencyEigenvalue

end MathlibExt.GraphTheory.VertexTransitiveAdjacencyEigenvalueKourovka15Problem89Wanted
