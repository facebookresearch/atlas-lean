/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH on locally connected graphs is NP-complete

Source:
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024
(NP-completeness of TREEWIDTH on all graphs, the source problem of the reduction);
ISGCI, *Information System on Graph Classes and their Inclusions*, class "locally connected"
(gc_932, https://www.graphclasses.org/classes/gc_932.html), problem treewidth decomposition:
NP-complete, reference [1506] (a note: adding a universal vertex to a connected graph gives a
locally connected graph; "Treewidth is reduced analogously to clique (Communicated by Arne
Leitert)").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TreewidthWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthLocallyConnected

open MetaMathlibExt.Complexity.NPComplete.Treewidth

/-!
# TREEWIDTH on locally connected graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is locally connected, that is, for every vertex `v` the open
neighbourhood `N(v)` induces a connected subgraph of `G`, and an integer `K`.
QUESTION: is the treewidth of `G` at most `K`?

This is TREEWIDTH (`TreewidthWanted`) restricted to ISGCI's class "locally connected" (gc_932:
"A graph G is locally connected iff for every vertex v, the open neighbourhood N(v) of v induces
a connected graph in G."): the instance type, graph, well-formedness and question
(`Treewidth.TreewidthFeasible`, a tree decomposition with bags of at most `K + 1` vertices) are
those of that module, and the restriction is added to well-formedness, written as in
`LocallyConnectedHamiltonianCircuitWanted`: for every `v`, `G.induce (G.neighborSet v)` is
`SimpleGraph.Connected`. Mathlib's `Connected` includes nonemptiness, so a graph with an
isolated vertex is not locally connected here; the reduction below never produces isolated
vertices, so the hardness holds under either convention for the empty neighbourhood.

Hardness, as recorded by ISGCI's note [1506]: adding a vertex adjacent to every vertex of a
connected graph `H` gives a locally connected graph (the new vertex sees `H`, and every other
vertex sees the new vertex, which is adjacent to all its other neighbours), and it raises the
treewidth by exactly one: a tree decomposition of `H` with the new vertex added to every bag is
one of the new graph, and restricting a tree decomposition of the new graph to the nodes whose
bags contain the new vertex, and removing that vertex, gives one of `H` (the same argument as
in `TreewidthDuallyChordalWanted`). The reduction from TREEWIDTH, whose vertex count is in
binary: isolated vertices do not change the treewidth of a graph with an edge (each goes into a
new one-vertex bag), so an instance `(H, K)` whose graph has no edge (treewidth at most `0`) is
mapped to a fixed yes-instance, and otherwise the isolated vertices are deleted and the rest
relabeled on at most `2|E|` vertices; adding two new vertices adjacent to everything (the first
makes the graph connected) then gives the equivalent instance `(H', K + 2)` of this problem, of
size polynomial in the input. Membership in NP: a locally connected graph has no isolated
vertex, so `|V| ≤ 2|E|`, and a tree decomposition with at most `max 1 |V|` nodes (one node
for the graph with no vertices) is a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is locally connected (every open neighbourhood induces a connected graph). -/
def LocallyConnectedWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ ∀ v, ((Graph i).induce ((Graph i).neighborSet v)).Connected

open Classical in
/-- TREEWIDTH on locally connected graphs as a decision problem over bitstrings. -/
noncomputable def treewidthLocallyConnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (LocallyConnectedWellFormed i ∧ TreewidthFeasible i)
  | none => false

/-- **TREEWIDTH on locally connected graphs is NP-complete.** Source: ISGCI, class gc_932,
reference [1506]; Arnborg, Corneil and Proskurowski (1987) (TREEWIDTH). -/
public theorem_wanted treewidthLocallyConnected_npComplete :
    treewidthLocallyConnectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treewidthLocallyConnectedDec

end MetaMathlibExt.Complexity.NPComplete.TreewidthLocallyConnected
