/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF GRAPHS OF GIRTH AT LEAST 9: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
M. Kamiński and V. V. Lozin, "Coloring edges and vertices of graphs without short or long
cycles", Contributions to Discrete Mathematics 2 (2007), 61-66, doi:10.55016/ojs/cdm.v2i1.61890,
Theorem 2.3;
T. Emden-Weinert, S. Hougardy and B. Kreuter, "Uniquely colourable graphs and the hardness of
colouring graphs of large girth", Combinatorics, Probability and Computing 7 (1998), 375-386,
doi:10.1017/S0963548398003678;
P. A. Golovach, M. Johnson, D. Paulusma and J. Song, "A survey on the computational complexity of
coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, Section 2.1 and Theorem 4 (arXiv:1407.1482v8);
ISGCI (Information System on Graph Classes and their Inclusions), class girth >=9 (gc_1225),
problem 3-Colourability: NP-complete.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Girth
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityGirthNine

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `K = 3`
whose graph has girth at least 9 (every cycle has length at least 9). -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ 9 ≤ (Graph i).egirth

open Classical in
/-- 3-COLORABILITY OF GRAPHS OF GIRTH AT LEAST 9 as a decision problem over bitstrings. -/
noncomputable def threeColorabilityGirthNineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityGirthNine
