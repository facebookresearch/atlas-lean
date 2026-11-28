/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF GRAPHS OF DIAMETER AT MOST 3: definitions

Source:
G. B. Mertzios and P. G. Spirakis, "Algorithms and almost tight results for 3-colorability of
small diameter graphs", Algorithmica 74(1) (2016), 385-414, doi:10.1007/s00453-014-9949-6
(Theorem 6: 3-coloring is NP-complete on triangle-free graphs with diameter 3 and radius 2).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import Mathlib.Combinatorics.SimpleGraph.Diam

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityDiameterThree

open GraphColoring (GraphColoringInstance Graph GraphColoringFeasible)

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev ThreeColorabilityDiameterThreeInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH COLORING instance with the same graph and bound `K = 3`. -/
abbrev withThreeColors (i : ThreeColorabilityDiameterThreeInstance) : GraphColoringInstance :=
  (i.1, i.2, 3)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (GRAPH
COLORING's well-formedness), the graph has at least one vertex, and it has diameter at most 3. -/
def WellFormed (i : ThreeColorabilityDiameterThreeInstance) : Prop :=
  GraphColoring.WellFormed (withThreeColors i) ∧ 0 < i.1 ∧
    (Graph (withThreeColors i)).ediam ≤ 3

/-- The graph is properly 3-colorable. -/
def ThreeColorabilityDiameterThreeFeasible (i : ThreeColorabilityDiameterThreeInstance) : Prop :=
  GraphColoringFeasible (withThreeColors i)

open Classical in
/-- 3-COLORABILITY OF GRAPHS OF DIAMETER AT MOST 3 as a decision problem over bitstrings. -/
noncomputable def threeColorabilityDiameterThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeColorabilityDiameterThreeInstance) x with
  | some i => decide (WellFormed i ∧ ThreeColorabilityDiameterThreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityDiameterThree
