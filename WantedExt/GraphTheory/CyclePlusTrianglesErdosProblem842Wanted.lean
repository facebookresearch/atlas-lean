/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The cycle-plus-triangles theorem (Erdős Problem 842)

Erdős Problem 842: let `G` be a graph on `3n` vertices formed by taking `n` vertex-disjoint
triangles and adding a Hamiltonian cycle (with all new edges) between these vertices. Does `G` have
chromatic number at most `3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GraphTheory.CyclePlusTrianglesErdosProblem842Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #842, https://www.erdosproblems.com/842 (status
PROVED). UnsolvedMath record UM-30007057 (`EP-842`), dataset ulamai/UnsolvedMath v1.8.0.

`T` is `n` vertex-disjoint triangles (its vertices are labelled by `Fin n × Fin 3`, adjacent iff
distinct with equal first coordinate); `C` is the image of the cycle graph on `Fin (3n)` under a
bijection; 'all new edges' is `Disjoint T C`. For `n = 1` no such `C` exists. Compared with the
formal-conjectures statement `ErdosProblems/842.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 842: a graph on `3n` vertices that is the union of `n` vertex-disjoint triangles
`T` and an edge-disjoint Hamiltonian cycle `C` has chromatic number at most `3`. -/
def cyclePlusTrianglesThreeColorable : Prop :=
  ∀ (n : ℕ) (V : Type) (T C : SimpleGraph V),
    (∃ e : V ≃ Fin n × Fin 3, ∀ u v, T.Adj u v ↔ u ≠ v ∧ (e u).1 = (e v).1) →
    (∃ e : Fin (3 * n) ≃ V, C = (SimpleGraph.cycleGraph (3 * n)).map e.toEmbedding) →
    Disjoint T C → (T ⊔ C).Colorable 3

/--
Resolved true: Fleischner and Stiebitz proved the cycle-plus-triangles theorem, that every such
graph is `3`-colorable; erdosproblems.com/842 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #842, https://www.erdosproblems.com/842 (status PROVED); resolution: H.
Fleischner and M. Stiebitz, A solution to a colouring problem of P. Erdős, Discrete Math. 101
(1992), 39-48, arXiv:2406.17723, Section 1: Fleischner and Stiebitz (and later Sachs) proved that
gluing vertex-disjoint triangles onto a single cycle always gives a 3-colourable graph, the cycle
plus triangles theorem, answering a question of Erdős; erdosproblems.com/842: the answer is yes,
proved by Fleischner and Stiebitz, https://doi.org/10.1016/0012-365X(92)90588-7.
-/
public theorem_wanted cyclePlusTrianglesThreeColorable_holds : cyclePlusTrianglesThreeColorable

end MathlibExt.GraphTheory.CyclePlusTrianglesErdosProblem842Wanted
