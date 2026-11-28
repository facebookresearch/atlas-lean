/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF C4-FREE GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY, the problem
restricted here;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
T. Emden-Weinert, S. Hougardy and B. Kreuter, "Uniquely colourable graphs and the hardness of
colouring graphs of large girth", Combinatorics, Probability and Computing 7 (1998), 375-386,
doi:10.1017/S0963548398003678.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ChromaticNumberHFreeGraphsDefs
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityC4Free

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance)

/-- Well-formedness of an instance: a well-formed CHROMATIC NUMBER OF H-FREE GRAPHS instance for
`H = C_4` (a simple edge list, a positive bound, and no induced `C_4` in the graph) whose bound
is `K = 3`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  ChromaticNumberHFreeGraphs.WellFormed (SimpleGraph.cycleGraph 4) i ∧ i.2.2 = 3

open Classical in
/-- 3-COLORABILITY OF C4-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityC4FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityC4Free
