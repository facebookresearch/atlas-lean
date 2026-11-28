/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST with costs in {-1, 0, 1}: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS7] SEQUENCING TO MINIMIZE
MAXIMUM CUMULATIVE COST, p. 238 (comment: "Remains NP-complete even if `c(t) ∈ {-1, 0, 1}` for
all `t ∈ T`"; reference: [Abdel-Wahab, 1976], transformation from REGISTER SUFFICIENCY);
H. M. Abdel-Wahab, *Scheduling with Applications to Register Allocation and Deadlock Problems*,
Ph.D. thesis, University of Waterloo (1976) (not available to this formalization).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCostDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCostTernaryCosts

open MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCost
  (SequencingToMinimizeMaximumCumulativeCostInstance Task cost
    SequencingToMinimizeMaximumCumulativeCostFeasible)

/-- Well-formedness of an instance: a well-formed SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST
instance in which every cost is `-1`, `0` or `1`. -/
def WellFormed (i : SequencingToMinimizeMaximumCumulativeCostInstance) : Prop :=
  SequencingToMinimizeMaximumCumulativeCost.WellFormed i ∧
    ∀ t : Task i, cost i t = -1 ∨ cost i t = 0 ∨ cost i t = 1

open Classical in
/-- SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST with costs in `{-1, 0, 1}` as a decision
problem over bitstrings. -/
noncomputable def sequencingToMinimizeMaximumCumulativeCostTernaryCostsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SequencingToMinimizeMaximumCumulativeCostInstance) x with
  | some i => decide (WellFormed i ∧ SequencingToMinimizeMaximumCumulativeCostFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCostTernaryCosts
