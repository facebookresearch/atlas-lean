/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING with one resource and three processors: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS10] RESOURCE CONSTRAINED
SCHEDULING, comment: NP-complete in the strong sense, even if `r = 1` and `m = 3`;
M. R. Garey and D. S. Johnson, "Complexity results for multiprocessor scheduling under resource
constraints", SIAM Journal on Computing 4 (1975), 397-411, doi:10.1137/0204035.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ResourceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOneResourceScheduling

/-- Well-formedness of an instance: it is a well-formed RESOURCE CONSTRAINED SCHEDULING instance
(`0 < m`, `0 < r`, `r` positive bounds, every task has `r` requirements with `R_k(t) ≤ B_k`,
`0 < D`), with `m = 3` processors and `r = 1` resource. -/
def WellFormed (i : ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance) :
    Prop :=
  ResourceConstrainedScheduling.WellFormed i ∧ i.1 = 3 ∧ i.2.1 = 1

open Classical in
/-- RESOURCE CONSTRAINED SCHEDULING with one resource and three processors as a decision problem
over bitstrings. -/
noncomputable def threeProcessorOneResourceSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧
      ResourceConstrainedScheduling.ResourceConstrainedSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOneResourceScheduling
