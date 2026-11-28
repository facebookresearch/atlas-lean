/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE COPY FILE ALLOCATION with uniform usages and storage costs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR6] MULTIPLE COPY FILE ALLOCATION,
p. 227, comment: "NP-complete in the strong sense, even if all v ∈ V have the same value of
u(v) and the same value of s(v)", credited there to [Van Sickle and Chandy, 1977], "The
complexity of computer network design problems", listed in the book's bibliography as an
unpublished manuscript.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipleCopyFileAllocationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocationUniformCosts

open MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocation
  (MultipleCopyFileAllocationInstance usage storage MultipleCopyFileAllocationFeasible)

/-- Well-formedness of an instance: the instance is well-formed for MULTIPLE COPY FILE
ALLOCATION, and all vertices have the same usage `u(v)` and the same storage cost `s(v)`. -/
def WellFormed (i : MultipleCopyFileAllocationInstance) : Prop :=
  MultipleCopyFileAllocation.WellFormed i ∧
    ∀ v w : Fin i.1, usage i v = usage i w ∧ storage i v = storage i w

open Classical in
/-- MULTIPLE COPY FILE ALLOCATION with uniform usages and storage costs as a decision problem
over bitstrings. -/
noncomputable def multipleCopyFileAllocationUniformCostsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleCopyFileAllocationInstance) x with
  | some i => decide (WellFormed i ∧ MultipleCopyFileAllocationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocationUniformCosts
