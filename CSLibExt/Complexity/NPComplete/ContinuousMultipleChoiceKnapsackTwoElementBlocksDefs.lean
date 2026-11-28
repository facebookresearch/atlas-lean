/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONTINUOUS MULTIPLE CHOICE KNAPSACK with blocks of at most two elements: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP11] CONTINUOUS MULTIPLE CHOICE
KNAPSACK, comment (p. 247): "Solvable in pseudo-polynomial time, but remains NP-complete even
if `|Uᵢ| ≤ 2`, `1 ≤ i ≤ m`" (reference of the entry: [Ibaraki, 1978]; transformation from
PARTITION);
T. Ibaraki, "Approximate algorithms for the multiple-choice continuous knapsack problems",
Journal of the Operations Research Society of Japan 23 (1980), 28-63,
doi:10.15807/jorsj.23.28.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsackDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsackTwoElementBlocks

open ContinuousMultipleChoiceKnapsack (ContinuousMultipleChoiceKnapsackInstance
  ContinuousMultipleChoiceKnapsackFeasible)

/-- Well-formedness of an instance: a well-formed CONTINUOUS MULTIPLE CHOICE KNAPSACK instance
whose blocks have at most two elements. -/
def WellFormed (i : ContinuousMultipleChoiceKnapsackInstance) : Prop :=
  ContinuousMultipleChoiceKnapsack.WellFormed i ∧ ∀ g ∈ i.1, g.length ≤ 2

open Classical in
/-- CONTINUOUS MULTIPLE CHOICE KNAPSACK with blocks of at most two elements as a decision
problem over bitstrings. -/
noncomputable def continuousMultipleChoiceKnapsackTwoElementBlocksDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ContinuousMultipleChoiceKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ ContinuousMultipleChoiceKnapsackFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsackTwoElementBlocks
