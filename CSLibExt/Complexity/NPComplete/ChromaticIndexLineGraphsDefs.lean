/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX on line graphs: definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.EdgeColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexLineGraphs

open EdgeColoring (EdgeColoringInstance EdgeColoringFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexLineGraphs
