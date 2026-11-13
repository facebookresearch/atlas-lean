/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Triangle-independent edge sets and triangle transversals (Erdős Problem 621)

Erdős Problem 621 (Erdős, Gallai and Tuza): let `G` be a graph on `n` vertices, `α₁(G)` the maximum
number of edges that contain at most one edge from every triangle, and `τ₁(G)` the minimum number of
edges that contain at least one edge from every triangle. Is it true that `α₁(G) + τ₁(G) ≤ n²/4`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.GraphTheory.TriangleIndependentPlusTransversalErdosProblem621Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #621, https://www.erdosproblems.com/621 (status PROVED
(LEAN)). UnsolvedMath record UM-30006955 (`EP-621`), dataset ulamai/UnsolvedMath v1.8.0.

Both quantities range over subsets of the edge set of `G`; the inequality is stated as `4 (α₁ + τ₁)
≤ n²` in `ℕ`. Compared with the formal-conjectures statement `ErdosProblems/621.lean` (equivalent;
no code imported).
-/

/-- `α₁(G)`: the largest size of a set of edges of `G` containing at most one edge of every
triangle of `G`. -/
noncomputable def triangleIndependenceNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {k | ∃ A ⊆ G.edgeSet, A.ncard = k ∧ ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
    (({s(x, y), s(y, z), s(x, z)} : Set (Sym2 (Fin n))) ∩ A).ncard ≤ 1}

/-- `τ₁(G)`: the least size of a set of edges of `G` containing at least one edge of every
triangle of `G`. -/
noncomputable def triangleTransversalNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ T ⊆ G.edgeSet, T.ncard = k ∧ ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
    s(x, y) ∈ T ∨ s(y, z) ∈ T ∨ s(x, z) ∈ T}

/-- Erdős Problem 621 (Erdős, Gallai and Tuza): every graph `G` on `n` vertices has
`α₁(G) + τ₁(G) ≤ n²/4`, stated as `4 (α₁(G) + τ₁(G)) ≤ n²`. -/
def triangleIndependentPlusTransversal : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    4 * (triangleIndependenceNumber G + triangleTransversalNumber G) ≤ n ^ 2

/--
Resolved true: Norin and Sun proved `α₁(G) + τ_B(G) ≤ |V(G)|²/4`, where `τ_B(G)` is the least number
of edges whose removal makes `G` bipartite; removing those edges destroys every triangle, so `τ₁(G)
≤ τ_B(G)`. erdosproblems.com/621 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #621, https://www.erdosproblems.com/621 (status PROVED (LEAN)); resolution: S. Norin and
Y.-R. Sun, Triangle-independent sets vs. cuts, arXiv:1602.04370 (2016), abstract: α₁(G) + τ_B(G) ≤
|V(G)|²/4, where τ_B(G) is the least size of an edge set whose removal makes G bipartite; τ₁ ≤ τ_B
(erdosproblems.com/621), https://arxiv.org/abs/1602.04370.
-/
public theorem_wanted triangleIndependentPlusTransversal_holds : triangleIndependentPlusTransversal

end MathlibExt.GraphTheory.TriangleIndependentPlusTransversalErdosProblem621Wanted
