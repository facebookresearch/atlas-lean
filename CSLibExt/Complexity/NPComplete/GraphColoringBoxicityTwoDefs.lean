/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY ON GRAPHS OF BOXICITY AT MOST 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
H. Imai and T. Asano, "Finding the connected components and a maximum clique of an intersection
graph of rectangles in the plane", Journal of Algorithms 4 (1983), 310-323,
doi:10.1016/0196-6774(83)90012-3 (coloring rectangle intersection graphs is NP-complete);
D. Catanzaro, S. Chaplick, S. Felsner, B. V. Halldórsson, M. M. Halldórsson, T. Hixon, and
J. Stacho, "Max point-tolerance graphs", Discrete Applied Mathematics 216 (2017), 84-97,
doi:10.1016/j.dam.2015.08.019, arXiv:1508.03810 (records the result for boxicity-2 graphs).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BoxicityTwoDefs
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringBoxicityTwo

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `0 < K ≤ |V|`
whose graph has boxicity at most `2` (`BoxicityTwo.BoxicityTwoFeasible` on its vertex count and
edge list). -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ (0 < i.2.2 ∧ i.2.2 ≤ i.1) ∧
    BoxicityTwo.BoxicityTwoFeasible (i.1, i.2.1)

open Classical in
/-- GRAPH K-COLORABILITY ON GRAPHS OF BOXICITY AT MOST 2 as a decision problem over bitstrings. -/
noncomputable def graphColoringBoxicityTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphColoringBoxicityTwo
