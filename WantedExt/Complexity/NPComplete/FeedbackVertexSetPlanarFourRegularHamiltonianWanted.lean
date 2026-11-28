/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on planar 4-regular Hamiltonian graphs is NP-complete

Source:
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 3.5;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (undirected version in
the comment; the parent problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class
"4-regular ∩ hamiltonian ∩ planar" (gc_1315), problem Feedback vertex set: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetPlanarFourRegularHamiltonianDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPlanarFourRegularHamiltonian

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

/-!
# FEEDBACK VERTEX SET on planar 4-regular Hamiltonian graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is planar, 4-regular (every vertex has degree 4) and
Hamiltonian (has a cycle through every vertex), and a positive integer `K ≤ |V|`. QUESTION: is
there a set `S ⊆ V` of at most `K` vertices such that `G - S` is acyclic (a forest)?

Cavallaro, Theorem 3.5: "Feedback Vertex Set on 4-regular planar Hamiltonian graphs with known
Hamilton-cycle is NP-complete", where Feedback Vertex Set asks, "given a graph `G` and some
integer `k`, [...] whether there is a set of size `k` whose deletion leaves `G` acyclic". This
module asks for at most `K` vertices, as the parent does; a superset of a feedback vertex set is
one, so the two readings agree for `K ≤ |V|`. The reduction outputs a Hamiltonian cycle together
with the graph; dropping the cycle gives a reduction to the problem stated here, where the cycle
is not part of the instance.

This is FEEDBACK VERTEX SET on planar graphs (`FeedbackVertexSetPlanarWanted`) restricted to
4-regular Hamiltonian graphs. The instance type (vertex count `n`, edge list, bound `K`), the
graph (`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (some `Finset` `S` with
`|S| ≤ K` whose complement induces a subgraph satisfying Mathlib's `SimpleGraph.IsAcyclic`) are
those of FEEDBACK VERTEX SET (`FeedbackVertexSetWanted`), and well-formedness is that of the
planar module (a simple edge list, the shared MathlibExt predicate `SimpleGraph.IsPlanar`, and
the bound `0 < K ≤ |V|` of Garey and Johnson's [GT7] instance), to which this module adds
4-regularity, Mathlib's `SimpleGraph.IsRegularOfDegree 4`, and Hamiltonicity, Mathlib's
`SimpleGraph.IsHamiltonian`, as in `IndependentSetPlanarRegularHamiltonianWanted`. The bound
changes no answer that matters: `K = 0` asks whether a 4-regular graph is acyclic (never, when
`n > 0`), and `K ≥ |V|` is always a yes. Mathlib's `IsHamiltonian` holds vacuously for a
one-vertex graph, which is not 4-regular, so on 4-regular graphs it says exactly that a
Hamiltonian cycle exists. Membership in NP takes `S` together with a Hamiltonian cycle as the
certificate; planarity and degrees are checked in polynomial time. Every vertex has degree 4,
so `n ≤ |E|` and the binary vertex count does not make the encoding succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET on planar 4-regular Hamiltonian graphs is NP-complete.** Source:
Cavallaro (2019), Theorem 3.5; Garey and Johnson (1979), [GT7] (parent problem). -/
public theorem_wanted feedbackVertexSetPlanarFourRegularHamiltonian_npComplete :
    feedbackVertexSetPlanarFourRegularHamiltonianDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetPlanarFourRegularHamiltonianDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPlanarFourRegularHamiltonian
