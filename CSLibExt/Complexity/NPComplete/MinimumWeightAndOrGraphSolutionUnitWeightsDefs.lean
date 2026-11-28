/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM WEIGHT AND/OR GRAPH SOLUTION with unit weights: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS16] MINIMUM WEIGHT
AND/OR GRAPH SOLUTION (p. 283), comment "Remains NP-complete even if w(a) = 1 for all a ∈ A"
(credited there to Garey and Johnson, unpublished).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolutionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolutionUnitWeights

open MetaMathlibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolution
  (MinimumWeightAndOrGraphSolutionInstance)

/-- Well-formedness of an instance: the parent's (`s < n`; arcs join vertices below `n`, have
positive weights and distinct `(tail, head)` pairs; the graph is acyclic; `s` is the only vertex
of in-degree `0`; one label per vertex; `0 < K`), and every arc `(tail, head, weight)` has
weight `1`. -/
def WellFormed (i : MinimumWeightAndOrGraphSolutionInstance) : Prop :=
  MinimumWeightAndOrGraphSolution.WellFormed i ∧ ∀ a ∈ i.2.2.1, a.2.2 = 1

open Classical in
/-- MINIMUM WEIGHT AND/OR GRAPH SOLUTION with unit weights as a decision problem over
bitstrings. -/
noncomputable def minimumWeightAndOrGraphSolutionUnitWeightsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumWeightAndOrGraphSolutionInstance) x with
  | some i =>
    decide (WellFormed i ∧
      MinimumWeightAndOrGraphSolution.MinimumWeightAndOrGraphSolutionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolutionUnitWeights
