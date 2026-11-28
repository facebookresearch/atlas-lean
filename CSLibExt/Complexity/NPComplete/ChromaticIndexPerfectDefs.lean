/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX for perfect graphs: definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.PerfectGraph
public import CSLibExt.Complexity.NPComplete.EdgeColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexPerfect

open MetaMathlibExt.Complexity.NPComplete.EdgeColoring (EdgeColoringInstance EdgeColoringFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexPerfect
