/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY ON (C₄, C₅)-FREE GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
D. Král', J. Kratochvíl, Zs. Tuza, and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
M. Kamiński and V. V. Lozin, "Coloring edges and vertices of graphs without short or long
cycles", Contributions to Discrete Mathematics 2 (2007), 61-66, doi:10.55016/ojs/cdm.v2i1.61890;
P. A. Golovach, M. Johnson, D. Paulusma, and J. Song, "A survey on the computational complexity
of coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, arXiv:1407.1482, Theorem 21 (i) 1.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringCFourCFiveFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with
`0 < K ≤ |V|` whose graph has no induced `C₄` and no induced `C₅`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ (0 < i.2.2 ∧ i.2.2 ≤ i.1) ∧
    ¬ (SimpleGraph.cycleGraph 4).IsIndContained (Graph i) ∧
    ¬ (SimpleGraph.cycleGraph 5).IsIndContained (Graph i)

open Classical in
/-- GRAPH K-COLORABILITY ON (C₄, C₅)-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def graphColoringCFourCFiveFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphColoringCFourCFiveFree
