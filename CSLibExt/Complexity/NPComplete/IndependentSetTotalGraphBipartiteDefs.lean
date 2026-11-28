/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on total graphs of bipartite graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, comment:
"Remains NP-complete … for total graphs of bipartite graphs [Yannakakis and Gavril, 1978]";
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on Applied
Mathematics 38(3) (1980), 364-372, doi:10.1137/0138030.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetTotalGraphBipartite

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev IndependentSetTotalGraphBipartiteInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IndependentSetTotalGraphBipartiteInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is isomorphic to the total graph of a bipartite graph `H` (on vertices `Fin m`): the disjoint sum
of `H` and its line graph, together with the edges joining each vertex `a` of `H` to each edge
`e` of `H` containing it; and `0 < K ≤ |V|`. -/
def WellFormed (i : IndependentSetTotalGraphBipartiteInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∃ (m : ℕ) (H : SimpleGraph (Fin m)), H.IsBipartite ∧
      Nonempty (Graph i ≃g (H ⊕g H.lineGraph) ⊔ SimpleGraph.fromRel fun x y =>
        ∃ (a : Fin m) (e : H.edgeSet), x = Sum.inl a ∧ y = Sum.inr e ∧ a ∈ (e : Sym2 (Fin m)))) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at least `K` vertices contains no two adjacent vertices. -/
def IndependentSetTotalGraphBipartiteFeasible
    (i : IndependentSetTotalGraphBipartiteInstance) : Prop :=
  ∃ s : Finset (Fin i.1), i.2.2 ≤ s.card ∧ (Graph i).IsIndepSet (s : Set (Fin i.1))

open Classical in
/-- INDEPENDENT SET on total graphs of bipartite graphs as a decision problem over
bitstrings. -/
noncomputable def independentSetTotalGraphBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentSetTotalGraphBipartiteInstance) x with
  | some i => decide (WellFormed i ∧ IndependentSetTotalGraphBipartiteFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetTotalGraphBipartite
