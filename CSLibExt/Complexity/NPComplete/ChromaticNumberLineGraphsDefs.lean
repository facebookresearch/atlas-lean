/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC NUMBER for line graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER, the unrestricted problem);
I. Holyer, "The NP-completeness of edge-coloring", SIAM Journal on Computing 10(4) (1981),
718-720, doi:10.1137/0210055 (deciding whether a cubic graph has chromatic index 3 is
NP-complete);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "Edge (or line)", column CHROMATIC
NUMBER);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (row EDGE (OR LINE), column CHR NUM: "N [OG]").
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticNumberLineGraphs

open MetaMathlibExt.Complexity.NPComplete.GraphColoring
  (GraphColoringInstance Graph GraphColoringFeasible)

/-- Well-formedness of an instance: a well-formed GRAPH COLORING instance (simple edge list) whose
graph is a line graph, with `0 < K ≤ |V|`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ MetaMathlibExt.SimpleGraph.IsLineGraph (Graph i) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- CHROMATIC NUMBER for line graphs as a decision problem over bitstrings. -/
noncomputable def chromaticNumberLineGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChromaticNumberLineGraphs
