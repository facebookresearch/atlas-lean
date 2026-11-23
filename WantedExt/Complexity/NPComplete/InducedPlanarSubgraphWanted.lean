/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED PLANAR SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT27] PLANAR SUBGRAPH, p. 197
(comment: "Corresponding problem in which `G'` is the subgraph induced by a set `V'` of at
least `K` vertices is also NP-complete");
M. S. Krishnamoorthy and N. Deo, "Node-deletion NP-complete problems", SIAM Journal on
Computing 8 (1979), 619-625, doi:10.1137/0208049 (property (v), planar);
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import WantedExt.Complexity.NPComplete.InducedSubgraphWithPropertyPiWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedPlanarSubgraph

/-!
# INDUCED PLANAR SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is there a subset
`V' ⊆ V` with `|V'| ≥ K` such that the subgraph of `G` induced by `V'` is planar?

This is INDUCED SUBGRAPH WITH PROPERTY Π ([GT21], `InducedSubgraphWithPropertyPiWanted`) for
the property "planar", so the instance type, `InducedSubgraphWithPropertyPi.WellFormed`
(a simple edge list on `Fin n` and `0 < K ≤ |V|`) and
`InducedSubgraphWithPropertyPi.InducedSubgraphWithPropertyPiFeasible` (some injective
`f : Fin m ↪ Fin n` with `m ≥ K` whose induced subgraph `G.comap f` has the property) are
reused unchanged. Planarity is the shared MathlibExt predicate `SimpleGraph.IsPlanar`
(a crossing-free straight-line drawing), as in `PlanarSubgraphWanted`; by Fáry's theorem
this is planarity for finite simple graphs.

The [GT21] theorem is stated under hypotheses on the property (hereditary, nontrivial,
polynomial-time testable); the statement below is unconditional and does not depend on
establishing those hypotheses for planarity.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The graph property "planar": a graph on `Fin m` has a crossing-free straight-line drawing
(`SimpleGraph.IsPlanar`). -/
def planarProperty : InducedSubgraphWithPropertyPi.GraphProperty :=
  fun _ G => G.IsPlanar

/-- INDUCED PLANAR SUBGRAPH as a decision problem over bitstrings: INDUCED SUBGRAPH WITH
PROPERTY Π for `Π` = planar. -/
noncomputable def inducedPlanarSubgraphDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  InducedSubgraphWithPropertyPi.inducedSubgraphWithPropertyPiDec planarProperty

/-- **INDUCED PLANAR SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT27],
comment; Krishnamoorthy and Deo (1979); Yannakakis (1978). -/
public theorem_wanted inducedPlanarSubgraph_npComplete :
    inducedPlanarSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inducedPlanarSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.InducedPlanarSubgraph
