/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX on line graphs is NP-complete

Source:
L. Cai and J. A. Ellis, "NP-completeness of edge-colouring some restricted graphs", Discrete
Applied Mathematics 30 (1991), 15-27, doi:10.1016/0166-218X(91)90010-T (full text not available
here; the result as recorded below);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021 (arXiv:2104.14395; Table 1, CHROMATIC INDEX on edge (or line)
graphs: "N [28]", and Section 3: "L. Cai and J. A. Ellis proved that deciding whether
`χ′(G) = 3` is NP-complete even for COMPARABILITY graphs and for LINE graphs [28]").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.EdgeColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexLineGraphs

open EdgeColoring (EdgeColoringInstance EdgeColoringFeasible)

/-!
# CHROMATIC INDEX on line graphs is NP-complete

INSTANCE: a line graph `G = (V, E)` and a positive integer `K`. QUESTION: is the chromatic index
of `G` at most `K`, i.e., can `E` be partitioned into at most `K` matchings?

This is EDGE COLORING (`EdgeColoringWanted`: Garey and Johnson's chromatic index problem, proved
NP-complete by Holyer) restricted to line graphs, the CHROMATIC INDEX column and EDGE (OR LINE)
graphs row of Johnson's 1985 table as revised by de Figueiredo, de Melo, Sasaki and Silva, who
record the entry as NP-complete, citing Cai and Ellis: deciding whether `χ′(G) = 3` is
NP-complete for line graphs. Up to trivial cases this is the question `χ′(G) ≤ 3` (a graph with a
vertex of degree more than `3` has `χ′(G) > 3`, and graphs of maximum degree at most `2` are
edge-colored in polynomial time), so the problem with `K` in the input is NP-hard.

The instance, its well-formedness (a simple edge list on `Fin n`) and the question (a coloring
of the listed edges with colors `0, …, K - 1` in which edges sharing an endpoint differ) are
those of `EdgeColoringWanted`. This module adds `0 < K` (Johnson's "positive integer") and the
restriction that the graph is a line graph, the repository's
`MetaMathlibExt.SimpleGraph.IsLineGraph`: isomorphic to Mathlib's `SimpleGraph.lineGraph` of a
graph on some `Fin k`. The graph of the instance is `Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : EdgeColoringInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: well formed for EDGE COLORING (a simple edge list on
`Fin n`), `K > 0`, and the graph is a line graph. -/
def WellFormed (i : EdgeColoringInstance) : Prop :=
  EdgeColoring.WellFormed i ∧ 0 < i.2.2 ∧ MetaMathlibExt.SimpleGraph.IsLineGraph (Graph i)

open Classical in
/-- CHROMATIC INDEX on line graphs as a decision problem over bitstrings. -/
noncomputable def chromaticIndexLineGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := EdgeColoringInstance) x with
  | some i => decide (WellFormed i ∧ EdgeColoringFeasible i)
  | none => false

/-- **CHROMATIC INDEX on line graphs is NP-complete.** Source: Cai and Ellis (1991); de Figueiredo,
de Melo, Sasaki and Silva (2022), Table 1 and Section 3. -/
public theorem_wanted chromaticIndexLineGraphs_npComplete :
    chromaticIndexLineGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chromaticIndexLineGraphsDec

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexLineGraphs
