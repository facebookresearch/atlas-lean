/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on locally connected graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_932` (locally
connected, https://www.graphclasses.org/classes/gc_932.html), problem Domination: NP-complete,
with its note 1506 (communicated by A. Leitert): adding a true twin to every vertex gives a
locally connected graph with the same domination number.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DominatingSetLocallyConnectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetLocallyConnected

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on locally connected graphs is NP-complete

INSTANCE: a locally connected graph `G = (V, E)`, i.e. for every vertex `v` the open
neighbourhood `N(v)` induces a connected graph, and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex of `V - V'` is adjacent to a vertex of `V'`?

This is DOMINATING SET on the ISGCI class `gc_932`. The instance, its well-formedness and the
question are those of `CSLibExt.Complexity.NPComplete.DominatingSetDefs` ([GT2]: a simple
graph on `Fin n` given by an edge list, and the bound `K`). The restriction adds `0 < K ≤ |V|`
([GT2]'s instance class) and local connectivity, written as in
`WantedExt.Complexity.NPComplete.LocallyConnectedHamiltonianCircuitWanted`:
`G.induce (G.neighborSet v)` is `SimpleGraph.Connected` for every `v`. Mathlib's `Connected`
includes nonemptiness, so a graph with an isolated vertex is not locally connected here.

ISGCI's note 1506 gives the reduction from DOMINATING SET: add to every vertex `v` a true twin
`v*` (adjacent to `v` and to every neighbour of `v` and its twin). In the new graph the
neighbourhood of `v` contains `v*`, which is adjacent to all its other vertices, so it induces a
connected graph, and likewise for `v*`; in particular no vertex is isolated. A dominating set of
`G` dominates the new graph, and replacing every twin `v*` in a dominating set of the new graph
by `v` gives a dominating set of `G` of no larger size. Local connectivity is checked in
polynomial time, so the problem is in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DOMINATING SET on locally connected graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT2]; ISGCI (`gc_932`, note 1506). -/
public theorem_wanted dominatingSetLocallyConnected_npComplete :
    dominatingSetLocallyConnectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetLocallyConnectedDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetLocallyConnected
