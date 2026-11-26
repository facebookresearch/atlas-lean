/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT for circular-arc graphs is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (SIMPLE MAX CUT
for circular-arc graphs, open there);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for
the 21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (entry N [1]);
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70 (2023), 307-322, doi:10.1007/s00454-022-00472-y, Theorem 1;
R. M. McConnell, "Linear-time recognition of circular-arc graphs", Algorithmica 37 (2003),
93-147, doi:10.1007/s00453-003-1032-7;
K. S. Booth and G. S. Lueker, "Testing for the consecutive ones property, interval graphs, and
graph planarity using PQ-tree algorithms", Journal of Computer and System Sciences 13 (1976),
335-379, doi:10.1016/S0022-0000(76)80045-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DomaticNumberCircularArcWanted
public import WantedExt.Complexity.NPComplete.MaxCutWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCircularArc

open MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT for circular-arc graphs is NP-complete

INSTANCE: a circular-arc graph `G = (V, E)`, that is, the intersection graph of a family of arcs
of a circle, and a positive integer `K`.
QUESTION: is there a partition of `V` into two sets with at least `K` edges between them?

This is SIMPLE MAX CUT (MAX CUT with all edge weights one) restricted to circular-arc graphs,
an entry of Johnson's Table 1 that de Figueiredo, de Melo, Sasaki and Silva resolve as
NP-complete by Adhikary, Bose, Mukherjee and Roy: they prove SIMPLE MAX CUT NP-complete on
interval graphs, and every interval graph is a circular-arc graph (replace the interval
endpoints by their ranks `0, …, 2|V| - 1` and use the intervals as arcs that do not wrap).
The instance, the simple-edge-list conditions and the question are those of MAXIMUM CUT
(`MaxCutWanted`, whose question counts edges), reused as in
`SimpleMaxCutUndirectedPathGraphsWanted`; the restriction adds to `WellFormed` that
`Cslib.Complexity.Karp.edgeGraph` is a circular-arc graph, and `0 < K`.

"Circular-arc graph" is the repository's predicate `DomaticNumberCircularArc.IsCircularArcGraph`
(stated for the same instance type `ℕ × List (ℕ × ℕ) × ℕ`; it reads only the vertex count and
the edge list): for some `L`, the vertices carry closed arcs with endpoints among the `L` points
of the circle such that two distinct vertices are adjacent exactly when their arcs meet.

Membership in NP: a cut is a polynomial certificate. Vertices outside the edge list are
isolated and do not affect the cut. A graph with an isolated vertex is a circular-arc graph
exactly when the remaining graph is an interval graph (cut the circle inside the isolated
vertex's arc), so class membership is decided on the non-isolated vertices, by McConnell's
circular-arc recognition when there is no isolated vertex and by Booth and Lueker's interval
recognition otherwise; the binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
`Fin n`) whose graph is a circular-arc graph, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧
    DomaticNumberCircularArc.IsCircularArcGraph i ∧
    0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT for circular-arc graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutCircularArcDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

/-- **SIMPLE MAX CUT for circular-arc graphs is NP-complete.**
Source: Johnson (1985), Table 1; de Figueiredo, de Melo, Sasaki and Silva (2022);
Adhikary, Bose, Mukherjee and Roy (2023). -/
public theorem_wanted simpleMaxCutCircularArc_npComplete :
    simpleMaxCutCircularArcDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutCircularArcDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCircularArc
