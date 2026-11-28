/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY OF (C4,TRIANGLE)-FREE GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
M. Kamiński and V. V. Lozin, "Coloring edges and vertices of graphs without short or long
cycles", Contributions to Discrete Mathematics 2 (2007), 61-66,
doi:10.55016/ojs/cdm.v2i1.61890, Theorem 2.3 and Corollary 2.4.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ChromaticNumberHFreeGraphsDefs
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KColorabilityC4TriangleFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance)

/-- Well-formedness of an instance: a well-formed CHROMATIC NUMBER OF H-FREE GRAPHS instance for
`H = C_4` (a simple edge list, a positive bound `K`, and no induced `C_4` in the graph) whose graph
also has no triangle (no 3-clique). -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  ChromaticNumberHFreeGraphs.WellFormed (SimpleGraph.cycleGraph 4) i ∧
    (GraphColoring.Graph i).CliqueFree 3

open Classical in
/-- GRAPH K-COLORABILITY OF (C4,TRIANGLE)-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def kColorabilityC4TriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KColorabilityC4TriangleFree
