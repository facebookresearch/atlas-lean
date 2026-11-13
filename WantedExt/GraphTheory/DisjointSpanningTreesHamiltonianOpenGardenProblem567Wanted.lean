/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Disjoint shortest spanning trees and Hamiltonicity (Open Problem Garden 567)

Open Problem Garden, What is the smallest number of disjoint spanning trees made a graph Hamiltonian
(B. Goldengorin): in a weighted complete graph, take an arbitrary shortest spanning tree `T₁`, then
an arbitrary shortest spanning tree `T₂` of the remaining edges, and so on. What is the smallest `k`
such that `T₁ ∪ ⋯ ∪ T_k` contains a Hamiltonian path (Question 1), a shortest Hamiltonian path
(Question 2)? Questions 3 and 4 ask the same with 1-trees and a Hamiltonian cycle, a shortest
Hamiltonian cycle.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

@[expose] public section

namespace MathlibExt.GraphTheory.DisjointSpanningTreesHamiltonianOpenGardenProblem567Wanted

/-!
Source: Open Problem Garden, What is the smallest number of disjoint spanning trees made a graph
Hamiltonian (node 567; B. Goldengorin),
http://www.openproblemgarden.org/op/what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian.
UnsolvedMath record UM-00003282 (`OPG-567`), dataset ulamai/UnsolvedMath v1.8.0.

Vertices are `Fin n`, edge weights are positive reals (restricting to positive weights only weakens
the positive answers, so their refutations are stronger). `IsSuccessiveShortest` lets each `Tᵢ` be
any member of minimum weight among those avoiding `T₁, …, T_{i-1}` (the page's "arbitrary shortest"
tree). A 1-tree with special vertex `v₀` (Held-Karp, as in the travelling salesman literature the
page refers to) is a spanning tree of the other vertices plus two edges at `v₀`; the special vertex
is arbitrary. A shortest Hamiltonian path (cycle) is one of minimum weight among all Hamiltonian
paths (cycles) of the complete graph. Each question is formalized as a positive answer, the
existence of one `k` that works for every weighted complete graph, and refuted.
-/

variable {n : ℕ}

/-- The edges of the complete graph `K_n` on `Fin n`. -/
def completeEdges (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ¬ e.IsDiag

/-- The total weight of a set of edges. -/
def weight (w : Sym2 (Fin n) → ℝ) (T : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ e ∈ T, w e

/-- `T` is the edge set of a spanning tree of `K_n` that uses only edges of `A`. -/
def IsSpanningTreeIn (A T : Finset (Sym2 (Fin n))) : Prop :=
  T ⊆ A ∧ (SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin n)))).IsTree

/-- `T` is a 1-tree with special vertex `v₀` (Held-Karp) that uses only edges of `A`: the edges of
`T` not at `v₀` form a spanning tree of the other vertices, and exactly two edges of `T` are at
`v₀`. -/
def IsOneTreeIn (v₀ : Fin n) (A T : Finset (Sym2 (Fin n))) : Prop :=
  T ⊆ A ∧ ((SimpleGraph.fromEdgeSet {e | e ∈ T ∧ v₀ ∉ e}).induce {v | v ≠ v₀}).IsTree ∧
    (T.filter fun e => v₀ ∈ e).card = 2

/-- `T₀, …, T_{k-1}` are successive shortest members of a class `P` of edge sets (spanning trees or
1-trees) of `K_n` with edge weights `w`: each `Tᵢ` is a member of minimum weight among the members
that avoid the edges of `T₀, …, T_{i-1}`, chosen arbitrarily among those of minimum weight. -/
def IsSuccessiveShortest (P : Finset (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) → Prop)
    (w : Sym2 (Fin n) → ℝ) {k : ℕ} (T : Fin k → Finset (Sym2 (Fin n))) : Prop :=
  ∀ i : Fin k, P (completeEdges n \ (Finset.univ.filter (· < i)).biUnion T) (T i) ∧
    ∀ T', P (completeEdges n \ (Finset.univ.filter (· < i)).biUnion T) T' →
      weight w (T i) ≤ weight w T'

/-- The union `T^k = (V, E₀ ∪ ⋯ ∪ E_{k-1})` of the edge sets `T₀, …, T_{k-1}`. -/
def unionGraph {k : ℕ} (T : Fin k → Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet ((Finset.univ.biUnion T : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))

/-- The weight of a walk: the sum of the weights of its edges. -/
def walkWeight (w : Sym2 (Fin n) → ℝ) {G : SimpleGraph (Fin n)} {a b : Fin n} (p : G.Walk a b) :
    ℝ :=
  (p.edges.map w).sum

/-- `H` contains a Hamiltonian path. -/
def HasHamiltonianPath (H : SimpleGraph (Fin n)) : Prop :=
  ∃ (a b : Fin n) (p : H.Walk a b), p.IsHamiltonian

/-- `H` contains a shortest Hamiltonian path of the weighted complete graph: a Hamiltonian path of
`H` whose weight is at most that of every Hamiltonian path of `K_n`. -/
def HasShortestHamiltonianPath (w : Sym2 (Fin n) → ℝ) (H : SimpleGraph (Fin n)) : Prop :=
  ∃ (a b : Fin n) (p : H.Walk a b), p.IsHamiltonian ∧
    ∀ (a' b' : Fin n) (q : (⊤ : SimpleGraph (Fin n)).Walk a' b'), q.IsHamiltonian →
      walkWeight w p ≤ walkWeight w q

/-- `H` contains a Hamiltonian cycle (`H` is Hamiltonian). -/
def HasHamiltonianCycle (H : SimpleGraph (Fin n)) : Prop :=
  ∃ (a : Fin n) (p : H.Walk a a), p.IsHamiltonianCycle

/-- `H` contains a shortest Hamiltonian cycle of the weighted complete graph: a Hamiltonian cycle of
`H` whose weight is at most that of every Hamiltonian cycle of `K_n`. -/
def HasShortestHamiltonianCycle (w : Sym2 (Fin n) → ℝ) (H : SimpleGraph (Fin n)) : Prop :=
  ∃ (a : Fin n) (p : H.Walk a a), p.IsHamiltonianCycle ∧
    ∀ (a' : Fin n) (q : (⊤ : SimpleGraph (Fin n)).Walk a' a'), q.IsHamiltonianCycle →
      walkWeight w p ≤ walkWeight w q

/-- Question 1, with a positive answer: some fixed number `k` works, that is, for every complete
graph with positive edge weights, the union of any `k` successive shortest spanning trees contains a
Hamiltonian path. -/
def spanningTreesGiveHamiltonianPath : Prop :=
  ∃ k : ℕ, ∀ (n : ℕ) (w : Sym2 (Fin n) → ℝ), (∀ e, 0 < w e) →
    ∀ T : Fin k → Finset (Sym2 (Fin n)), IsSuccessiveShortest IsSpanningTreeIn w T →
      HasHamiltonianPath (unionGraph T)

/-- Question 2, with a positive answer: for some fixed `k`, the union of any `k` successive shortest
spanning trees contains a shortest Hamiltonian path. -/
def spanningTreesGiveShortestHamiltonianPath : Prop :=
  ∃ k : ℕ, ∀ (n : ℕ) (w : Sym2 (Fin n) → ℝ), (∀ e, 0 < w e) →
    ∀ T : Fin k → Finset (Sym2 (Fin n)), IsSuccessiveShortest IsSpanningTreeIn w T →
      HasShortestHamiltonianPath w (unionGraph T)

/-- Question 3, with a positive answer: for some fixed `k`, the union of any `k` successive shortest
1-trees (any special vertex) is Hamiltonian. -/
def oneTreesGiveHamiltonianCycle : Prop :=
  ∃ k : ℕ, ∀ (n : ℕ) (v₀ : Fin n) (w : Sym2 (Fin n) → ℝ), (∀ e, 0 < w e) →
    ∀ T : Fin k → Finset (Sym2 (Fin n)), IsSuccessiveShortest (IsOneTreeIn v₀) w T →
      HasHamiltonianCycle (unionGraph T)

/-- Question 4, with a positive answer: for some fixed `k`, the union of any `k` successive shortest
1-trees contains a shortest Hamiltonian cycle. -/
def oneTreesGiveShortestHamiltonianCycle : Prop :=
  ∃ k : ℕ, ∀ (n : ℕ) (v₀ : Fin n) (w : Sym2 (Fin n) → ℝ), (∀ e, 0 < w e) →
    ∀ T : Fin k → Finset (Sym2 (Fin n)), IsSuccessiveShortest (IsOneTreeIn v₀) w T →
      HasShortestHamiltonianCycle w (unionGraph T)

/--
Resolved false: DeVos observes on the problem page that no `k` works: in `K_{6k}` with weight `1` on
a spanning `K_{2k,4k}` and weight `2` elsewhere, `k` edge-disjoint spanning trees of the `K_{2k,4k}`
are successive shortest spanning trees, and their union, a subgraph of the unbalanced complete
bipartite graph, has no Hamiltonian path. Source: Open Problem Garden, What is the smallest number
of disjoint spanning trees made a graph Hamiltonian (node 567; B. Goldengorin),
http://www.openproblemgarden.org/op/what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian;
resolution: M. DeVos, comment 'Is this statement correct?' (September 10th, 2007) on the Open
Problem Garden page of problem 567, no k works for any of the four questions: in K_{6k}, weight 1 on
the edges between {1, ..., 2k} and {2k+1, ..., 6k} (a K_{2k,4k}, which has k edge-disjoint spanning
trees by Nash-Williams' theorem) and weight 2 on the other edges; the procedure may choose all k
trees inside the K_{2k,4k}, whose union has no Hamiltonian path,
http://www.openproblemgarden.org/op/what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian.
-/
public theorem_wanted spanningTreesGiveHamiltonianPath_refuted : ¬ spanningTreesGiveHamiltonianPath

/--
Resolved false: DeVos's example (`K_{6k}`, weight `1` on a spanning `K_{2k,4k}`, `2` elsewhere)
shows that no `k` works for any of the four questions; the union of the `k` chosen trees lies in the
`K_{2k,4k}`, so it has no Hamiltonian path, shortest or not. Source: Open Problem Garden, What is
the smallest number of disjoint spanning trees made a graph Hamiltonian (node 567; B. Goldengorin),
http://www.openproblemgarden.org/op/what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian;
resolution: M. DeVos, comment 'Is this statement correct?' (September 10th, 2007) on the Open
Problem Garden page of problem 567, no k works for any of the four questions: in K_{6k}, weight 1 on
the edges between {1, ..., 2k} and {2k+1, ..., 6k} (a K_{2k,4k}, which has k edge-disjoint spanning
trees by Nash-Williams' theorem) and weight 2 on the other edges; the procedure may choose all k
trees inside the K_{2k,4k}, whose union has no Hamiltonian path,
http://www.openproblemgarden.org/op/what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian.
-/
public theorem_wanted spanningTreesGiveShortestHamiltonianPath_refuted :
    ¬ spanningTreesGiveShortestHamiltonianPath

/--
Resolved false: DeVos states on the problem page that no `k` gives a positive answer to any of the
four questions, Question 3 included; the example his comment works out (for spanning trees) is
`K_{6k}` with weight `1` on a spanning `K_{2k,4k}` and `2` elsewhere, and no subgraph of the
unbalanced `K_{2k,4k}` has a Hamiltonian cycle. Source: Open Problem Garden, What is the smallest
number of disjoint spanning trees made a graph Hamiltonian (node 567; B. Goldengorin),
http://www.openproblemgarden.org/op/what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian;
resolution: M. DeVos, comment 'Is this statement correct?' (September 10th, 2007) on the Open
Problem Garden page of problem 567, no k works for any of the four questions: in K_{6k}, weight 1 on
the edges between {1, ..., 2k} and {2k+1, ..., 6k} (a K_{2k,4k}, which has k edge-disjoint spanning
trees by Nash-Williams' theorem) and weight 2 on the other edges; the procedure may choose all k
trees inside the K_{2k,4k}, whose union has no Hamiltonian path,
http://www.openproblemgarden.org/op/what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian.
-/
public theorem_wanted oneTreesGiveHamiltonianCycle_refuted : ¬ oneTreesGiveHamiltonianCycle

/--
Resolved false: DeVos states on the problem page that no `k` gives a positive answer to any of the
four questions, Question 4 included; the example his comment works out (for spanning trees) is
`K_{6k}` with weight `1` on a spanning `K_{2k,4k}` and `2` elsewhere, and no subgraph of the
unbalanced `K_{2k,4k}` contains a Hamiltonian cycle, shortest or not. Source: Open Problem Garden,
What is the smallest number of disjoint spanning trees made a graph Hamiltonian (node 567; B.
Goldengorin),
http://www.openproblemgarden.org/op/what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian;
resolution: M. DeVos, comment 'Is this statement correct?' (September 10th, 2007) on the Open
Problem Garden page of problem 567, no k works for any of the four questions: in K_{6k}, weight 1 on
the edges between {1, ..., 2k} and {2k+1, ..., 6k} (a K_{2k,4k}, which has k edge-disjoint spanning
trees by Nash-Williams' theorem) and weight 2 on the other edges; the procedure may choose all k
trees inside the K_{2k,4k}, whose union has no Hamiltonian path,
http://www.openproblemgarden.org/op/what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian.
-/
public theorem_wanted oneTreesGiveShortestHamiltonianCycle_refuted :
    ¬ oneTreesGiveShortestHamiltonianCycle

end MathlibExt.GraphTheory.DisjointSpanningTreesHamiltonianOpenGardenProblem567Wanted
