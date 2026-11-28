/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM WEIGHT CONNECTED SUBGRAPH is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
145-159, doi:10.1016/0196-6774(85)90025-2, problem [5] MAXIMUM WEIGHT CONNECTED SUBGRAPH
(reference: A. Vergis, manuscript, 1983, not available; transformation from STEINER TREE IN
GRAPHS [ND12]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumWeightConnectedSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumWeightConnectedSubgraph

/-!
# MAXIMUM WEIGHT CONNECTED SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)`, an integral (and possibly negative) weight `w(v)` for each
`v ∈ V`, and a bound `B`.
QUESTION: is there a connected subgraph of `G` whose total vertex weight is at least `B`?

Johnson reports the problem NP-complete (Vergis, by a transformation from STEINER TREE IN
GRAPHS), even for planar `G` of maximum degree 3 with all weights `+1` or `-1`.

The vertices are `0, ..., n - 1`, the graph is given by a simple edge list
(`Cslib.Complexity.Karp.edgeGraph`), and the weights by a list of length `n`. Weights and `B`
are integers, each given as a (positive part, negative part) pair as in `ZeroOneILPWanted`;
numbers use the binary encoding. Only the vertex set of the subgraph enters its weight, and a
vertex set `S` carries a connected subgraph of `G` exactly when the subgraph of `G` induced on
`S` is connected, so the question asks for a vertex set `S` whose induced subgraph is connected
(Mathlib's `SimpleGraph.Connected`, which requires `S` nonempty) with `∑_{v ∈ S} w(v) ≥ B`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM WEIGHT CONNECTED SUBGRAPH is NP-complete.** Source: Johnson (1985),
NP-completeness column, problem [5] (Vergis). -/
public theorem_wanted maximumWeightConnectedSubgraph_npComplete :
    maximumWeightConnectedSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumWeightConnectedSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.MaximumWeightConnectedSubgraph
