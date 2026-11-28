/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED DOMINATING SET on 4-regular graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET, p. 190, comment
("Variation in which the subgraph induced by V' is required to be connected is also
NP-complete", credited there to [Garey and Johnson, unpublished]);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 5(1)
(1984), 147-160, doi:10.1016/0196-6774(84)90045-2, Section 3 (records that the unpublished
1978 result of Garey and Johnson covers CONNECTED DOMINATING SET on "4-regular (not necessarily
planar) graphs"; the original proof was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConnectedDominatingSetFourRegularDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSetFourRegular

open MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSet
  (ConnectedDominatingSetInstance Graph ConnectedDominatingSetFeasible)

/-!
# CONNECTED DOMINATING SET on 4-regular graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is regular of degree 4, and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set `V' ⊆ V` of size `K` or less for `G` (for all
`u ∈ V - V'` there is a `v ∈ V'` with `{u, v} ∈ E`) such that the subgraph of `G` induced by
`V'` is connected?

The instance, its graph, the simple-edge-list well-formedness and the question are those of
CONNECTED DOMINATING SET (`WantedExt.Complexity.NPComplete.ConnectedDominatingSetWanted`: a
simple graph on `Fin n` given by an edge list, and a set of at most `K` vertices that dominates
every vertex and induces a connected subgraph, Mathlib's `SimpleGraph.Connected` of
`SimpleGraph.induce`). The restriction adds `0 < K ≤ |V|` ([GT2]'s instance class) and that the
graph is regular of degree 4 (Mathlib's `SimpleGraph.IsRegularOfDegree 4`: every vertex has
degree 4).

Garey and Johnson list the connected variant as NP-complete "even for planar graphs that are
regular of degree 4"; Johnson's March 1984 column calls that class a transcription error and
records the classes of the unpublished proof as 4-regular graphs and planar graphs of maximum
degree 4. This module states the first. Membership in NP: the certificate is `V'`; domination,
connectivity and 4-regularity are checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONNECTED DOMINATING SET on 4-regular graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT2], comment, as corrected by Johnson (1984). -/
public theorem_wanted connectedDominatingSetFourRegular_npComplete :
    connectedDominatingSetFourRegularDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L connectedDominatingSetFourRegularDec

end MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSetFourRegular
