/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on locally connected graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class "locally connected"
(gc_932, https://www.graphclasses.org/classes/gc_932.html), problem Independent set:
NP-complete, reference [1506] (a note communicated by P. Irzhavski: adding a universal vertex
to a connected graph gives a locally connected graph, "Similarly for independent set").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IndependentSetLocallyConnectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetLocallyConnected

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-!
# INDEPENDENT SET on locally connected graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is locally connected, that is, for every vertex `v` the open
neighbourhood `N(v)` induces a connected subgraph of `G`, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) restricted to ISGCI's class "locally connected" (gc_932: "A
graph G is locally connected iff for every vertex v, the open neighbourhood N(v) of v induces a
connected graph in G."). The instance type (vertex count `n`, edge list, bound `K`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (a `Finset` of at least `K`
vertices whose coercion is Mathlib's `SimpleGraph.IsIndepSet`) are those of
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`, whose triangle-free
restriction lives only in its `WellFormed`, which this module does not use. `WellFormed` here
asks for a simple edge list on `Fin n`, `0 < K ≤ |V|` ([GT20]'s instance class), and local
connectivity written as in `LocallyConnectedHamiltonianCircuitWanted`: for every `v`,
`G.induce (G.neighborSet v)` is `SimpleGraph.Connected`. Mathlib's `Connected` includes
nonemptiness, so a graph with an isolated vertex is not locally connected here; the reduction
below never produces isolated vertices, so the hardness holds under either convention for the
empty neighbourhood. Without isolated vertices `|V| ≤ 2|E|`, so the binary vertex count does not
make the problem succinct.

Hardness, as recorded by ISGCI's note [1506]: adding a vertex adjacent to every vertex of a
connected graph `H` gives a locally connected graph (the new vertex sees `H`, and every other
vertex sees the new vertex, which is adjacent to all its other neighbours), and for nonempty `H`
it leaves the largest independent set unchanged. Applied twice to a nonempty graph (the first
new vertex makes the graph connected), it reduces INDEPENDENT SET to this problem. Membership in
NP: the independent set is a certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDEPENDENT SET on locally connected graphs is NP-complete.** Source: ISGCI, class gc_932,
reference [1506]; Garey and Johnson (1979), [GT20] (parent problem). -/
public theorem_wanted independentSetLocallyConnected_npComplete :
    independentSetLocallyConnectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetLocallyConnectedDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetLocallyConnected
