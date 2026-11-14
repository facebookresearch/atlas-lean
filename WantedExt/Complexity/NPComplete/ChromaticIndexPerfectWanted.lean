/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX for perfect graphs is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (sixteenth edition), Journal
of Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "Perfect", column
"ChrInd": "O?", apparently open in 1985); L. Cai and J. A. Ellis, "NP-completeness of
edge-colouring some restricted graphs", Discrete Applied Mathematics 30 (1991), 15-27,
doi:10.1016/0166-218X(91)90010-T (NP-complete for regular comparability graphs, which are perfect;
see `ChromaticIndexRegularComparabilityWanted`); C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki
and A. Silva, "Revising Johnson's table for the 21st century", Discrete Applied Mathematics 323
(2022), doi:10.1016/j.dam.2021.05.021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.PerfectGraph
public import WantedExt.Complexity.NPComplete.EdgeColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexPerfect

open MetaMathlibExt.Complexity.NPComplete.EdgeColoring (EdgeColoringInstance EdgeColoringFeasible)

/-!
# CHROMATIC INDEX for perfect graphs is NP-complete

INSTANCE: a perfect graph `G = (V, E)` and a positive integer `K`. QUESTION: is the chromatic
index of `G` at most `K`, i.e. can `E` be partitioned into at most `K` matchings?

This is CHROMATIC INDEX (`EdgeColoringWanted`) restricted to perfect graphs, the entry of Table 1
of the sixteenth edition of Johnson's column (row "Perfect", column "ChrInd") that was open in
1985. Cai and Ellis proved the problem NP-complete for regular comparability graphs, and
comparability graphs are perfect. The instance type, `EdgeColoring.WellFormed` (simple edge list)
and `EdgeColoring.EdgeColoringFeasible` (a color below `K` for each listed edge, different on any
two edges sharing an end) are the parent's, unchanged; `WellFormed` adds the restriction,
MathlibExt `MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect` (every induced
subgraph has chromatic number equal to its clique number, as in `FeedbackVertexSetPerfectWanted`)
on the graph `Cslib.Complexity.Karp.edgeGraph n E`, and `0 < K` (as in the comparability-graph
sibling).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's simple edge list, the graph is perfect, and `K`
is positive. -/
def WellFormed (i : EdgeColoringInstance) : Prop :=
  EdgeColoring.WellFormed i ∧
    MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect
      (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧ 0 < i.2.2

open Classical in
/-- CHROMATIC INDEX for perfect graphs as a decision problem over bitstrings. -/
noncomputable def chromaticIndexPerfectDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeColoringInstance) x with
  | some i => decide (WellFormed i ∧ EdgeColoringFeasible i)
  | none => false

/-- **CHROMATIC INDEX is NP-complete for perfect graphs.** Source: Johnson, NP-completeness
column (1985), Table 1; Cai and Ellis (1991). -/
public theorem_wanted chromaticIndexPerfect_npComplete :
    chromaticIndexPerfectDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chromaticIndexPerfectDec

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexPerfect
