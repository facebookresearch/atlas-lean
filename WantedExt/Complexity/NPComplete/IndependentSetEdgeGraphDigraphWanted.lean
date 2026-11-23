/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on edge graphs of directed graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, comment:
"Remains NP-complete … for edge graphs of directed graphs [Gavril, 1977a]";
F. Gavril, "Some NP-complete problems on graphs", Proceedings of the 11th Conference on
Information Sciences and Systems, Johns Hopkins University, Baltimore (1977), 91-95 (not
available; the result and its attribution are those recorded by Garey and Johnson);
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetEdgeGraphDigraph

/-!
# INDEPENDENT SET on edge graphs of directed graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is the edge graph of some directed graph, and a positive
integer `K ≤ |V|`. QUESTION: does `G` contain an independent set of size `K` or more, that is,
a subset `V' ⊆ V` with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in
`E`?

The edge graph of a directed graph `D` has the arcs of `D` as its vertices; two distinct arcs are
adjacent when the head of one is the tail of the other. This is the undirected simple graph
underlying the line digraph of Harary and Norman ("Some properties of line digraphs", Rendiconti del
Circolo Matematico di Palermo 9 (1960), 161-168, doi:10.1007/BF02854581), in which there is an arc
from `(u, v)` to `(v, w)`. It is the only reading under which the [GT20] comment is consistent: were
arcs adjacent whenever they share an endpoint, the edge graph would be the line graph of the
underlying multigraph, and Garey and Johnson list INDEPENDENT SET as polynomial "for edge graphs (by
matching)" in the same comment. `digraphEdgeGraph` builds it on the arcs of a Mathlib `Digraph`; "is
the edge graph of" means isomorphic to it (Mathlib's `SimpleGraph.Iso`).

Hardness: when `D` has no loops, a set `S` of arcs is independent exactly when no vertex of `D` is
both a head and a tail of arcs of `S`, that is, when all arcs of `S` go from a vertex set `X` to its
complement; so `α` of the edge graph is the maximum number of arcs leaving a vertex set (MAX
DIRECTED CUT). For an undirected graph `H`, let the loopless digraph `D` have the two arcs `(u, v)`
and `(v, u)` for every edge `{u, v}`: the arcs leaving `X` are one per edge of `H` between `X` and
its complement, so the edge graph of `D` has an independent set of `K` or more vertices iff `H` has
a cut of `K` or more edges, which is SIMPLE MAX CUT, NP-complete by Garey, Johnson and Stockmeyer
(1976) (`MaxCutWanted`). Membership in NP: `n` is binary, so the certificate covers only the
non-isolated vertices of `G`, at most `2 |E|` of them. Deleting from `D` the arcs that are isolated
vertices of its edge graph leaves, on the remaining arcs, the edge graph of the remaining digraph,
and a fresh arc `x → y` between two new vertices is an isolated vertex of the edge graph; hence `G`
is the edge graph of a digraph iff the subgraph induced by its non-isolated vertices is. The
certificate is a digraph for that subgraph, restricted to the endpoints of its arcs (at most `4 |E|`
vertices), the isomorphism, and the part `S` of `V'` among the non-isolated vertices, checked
against `|S| + (n - c) ≥ K` with `c` the number of non-isolated vertices (isolated vertices can
always join an independent set).

The instance, the graph and the question follow
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`: a vertex count `n`
(vertices `Fin n`), an edge list and the bound `K`; the independent set is a `Finset` whose
coercion is Mathlib's `SimpleGraph.IsIndepSet`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The edge graph of a digraph `D`: its vertices are the arcs `(u, v)` of `D`, and two distinct
arcs are adjacent when the head of one is the tail of the other. -/
def digraphEdgeGraph {V : Type*} (D : Digraph V) :
    SimpleGraph {a : V × V // D.Adj a.1 a.2} :=
  SimpleGraph.fromRel fun a b => a.1.2 = b.1.1

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev IndependentSetEdgeGraphDigraphInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IndependentSetEdgeGraphDigraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is isomorphic to the edge graph of a digraph `D` (on vertices `Fin m`), and `0 < K ≤ |V|`. -/
def WellFormed (i : IndependentSetEdgeGraphDigraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∃ (m : ℕ) (D : Digraph (Fin m)), Nonempty (Graph i ≃g digraphEdgeGraph D)) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at least `K` vertices contains no two adjacent vertices. -/
def IndependentSetEdgeGraphDigraphFeasible
    (i : IndependentSetEdgeGraphDigraphInstance) : Prop :=
  ∃ s : Finset (Fin i.1), i.2.2 ≤ s.card ∧ (Graph i).IsIndepSet (s : Set (Fin i.1))

open Classical in
/-- INDEPENDENT SET on edge graphs of directed graphs as a decision problem over bitstrings. -/
noncomputable def independentSetEdgeGraphDigraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentSetEdgeGraphDigraphInstance) x with
  | some i => decide (WellFormed i ∧ IndependentSetEdgeGraphDigraphFeasible i)
  | none => false

/-- **INDEPENDENT SET on edge graphs of directed graphs is NP-complete.**
Source: Garey and Johnson (1979), [GT20], comment; Gavril (1977). -/
public theorem_wanted independentSetEdgeGraphDigraph_npComplete :
    independentSetEdgeGraphDigraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetEdgeGraphDigraphDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetEdgeGraphDigraph
