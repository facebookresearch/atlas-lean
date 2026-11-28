/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING with three processors and unit resources: definitions

Source:
J. Błażewicz, J. K. Lenstra and A. H. G. Rinnooy Kan, "Scheduling subject to resource
constraints: classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24,
doi:10.1016/0166-218X(83)90012-4 (the problem `P3 | res·11, p_j = 1 | C_max`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problems [SS10] RESOURCE CONSTRAINED SCHEDULING (parent
problem) and [GT11] PARTITION INTO TRIANGLES (source problem of the reduction below).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ResourceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitResourceScheduling

/-- Well-formedness of an instance: a well-formed RESOURCE CONSTRAINED SCHEDULING instance
(`0 < m`, `0 < r`, `r` positive bounds, `r` requirements per task with `R_k(t) ≤ B_k`,
`0 < D`) with `m = 3` processors and every resource bound equal to `1`. -/
def WellFormed (i : ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance) :
    Prop :=
  ResourceConstrainedScheduling.WellFormed i ∧ i.1 = 3 ∧ ∀ b ∈ i.2.2.1, b = 1

open Classical in
/-- RESOURCE CONSTRAINED SCHEDULING with three processors and unit resources as a decision
problem over bitstrings. -/
noncomputable def threeProcessorUnitResourceSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧
      ResourceConstrainedScheduling.ResourceConstrainedSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitResourceScheduling
