/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED DOMINATING SET on planar graphs of maximum degree 4 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET, p. 190, comment
("Variation in which the subgraph induced by V' is required to be connected is also
NP-complete", credited there to [Garey and Johnson, unpublished]);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 5(1)
(1984), 147-160, doi:10.1016/0196-6774(84)90045-2, Section 3 (records that the unpublished
1978 result of Garey and Johnson covers CONNECTED DOMINATING SET on "planar graphs with maximum
degree 4"; the original proof was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ConnectedDominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSetPlanarMaxDegreeFour

open MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSet
  (ConnectedDominatingSetInstance Graph ConnectedDominatingSetFeasible)

/-!
# CONNECTED DOMINATING SET on planar graphs of maximum degree 4 is NP-complete

INSTANCE: a planar graph `G = (V, E)` with no vertex degree exceeding 4, and a positive integer
`K ≤ |V|`.
QUESTION: is there a dominating set `V' ⊆ V` of size `K` or less for `G` (for all
`u ∈ V - V'` there is a `v ∈ V'` with `{u, v} ∈ E`) such that the subgraph of `G` induced by
`V'` is connected?

The instance, its graph, the simple-edge-list well-formedness and the question are those of
CONNECTED DOMINATING SET (`WantedExt.Complexity.NPComplete.ConnectedDominatingSetWanted`: a
simple graph on `Fin n` given by an edge list, and a set of at most `K` vertices that dominates
every vertex and induces a connected subgraph, Mathlib's `SimpleGraph.Connected` of
`SimpleGraph.induce`). The restriction adds `0 < K ≤ |V|` ([GT2]'s instance class) and the
class: planarity as the repository's `SimpleGraph.IsPlanar` (a crossing-free straight-line
drawing, which by Fáry's theorem exists exactly for planar graphs) and the degree bound as
Mathlib's `SimpleGraph.degree`.

Garey and Johnson list the connected variant as NP-complete "even for planar graphs that are
regular of degree 4"; Johnson's March 1984 column calls that class a transcription error and
records the classes of the unpublished proof as 4-regular graphs and planar graphs of maximum
degree 4. This module states the second. Membership in NP: the certificate is `V'`; domination,
connectivity and degrees are checked directly and planarity in linear time (Hopcroft and
Tarjan, J. ACM 21 (1974), 549-568).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance: a well-formed CONNECTED DOMINATING SET instance with
`0 < K ≤ |V|` whose graph is planar with every vertex degree at most 4. -/
def WellFormed (i : ConnectedDominatingSetInstance) : Prop :=
  ConnectedDominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ (Graph i).IsPlanar ∧
    ∀ v, (Graph i).degree v ≤ 4

open Classical in
/-- CONNECTED DOMINATING SET on planar graphs of maximum degree 4 as a decision problem over
bitstrings. -/
noncomputable def connectedDominatingSetPlanarMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConnectedDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ ConnectedDominatingSetFeasible i)
  | none => false

/-- **CONNECTED DOMINATING SET on planar graphs of maximum degree 4 is NP-complete.** Source:
Garey and Johnson (1979), [GT2], comment, as corrected by Johnson (1984). -/
public theorem_wanted connectedDominatingSetPlanarMaxDegreeFour_npComplete :
    connectedDominatingSetPlanarMaxDegreeFourDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L connectedDominatingSetPlanarMaxDegreeFourDec

end MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSetPlanarMaxDegreeFour
