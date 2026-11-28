/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DYNAMIC STORAGE ALLOCATION with sizes 1 and 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR2] DYNAMIC STORAGE ALLOCATION,
p. 226 (comment: NP-complete in the strong sense, even if `s(a) ∈ {1, 2}` for all `a ∈ A`;
the entry's reference is [Stockmeyer, 1976b], listed by Garey and Johnson as a private
communication, which was not available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DynamicStorageAllocationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DynamicStorageAllocationSizesOneTwo

/-- An instance, as in `DynamicStorageAllocationWanted`: the items `(s(a), r(a), d(a))` (size,
arrival time, departure time) and the storage size `D`. -/
abbrev DynamicStorageAllocationSizesOneTwoInstance :=
  DynamicStorageAllocation.DynamicStorageAllocationInstance

/-- Well-formedness of an instance: the instance of DYNAMIC STORAGE ALLOCATION is well-formed,
and every item has size `1` or `2`. -/
def WellFormed (i : DynamicStorageAllocationSizesOneTwoInstance) : Prop :=
  DynamicStorageAllocation.WellFormed i ∧ ∀ a ∈ i.1, a.1 = 1 ∨ a.1 = 2

/-- A feasible allocation of storage, exactly as in `DynamicStorageAllocationWanted`. -/
def DynamicStorageAllocationSizesOneTwoFeasible
    (i : DynamicStorageAllocationSizesOneTwoInstance) : Prop :=
  DynamicStorageAllocation.DynamicStorageAllocationFeasible i

open Classical in
/-- DYNAMIC STORAGE ALLOCATION with sizes 1 and 2 as a decision problem over bitstrings. -/
noncomputable def dynamicStorageAllocationSizesOneTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DynamicStorageAllocationSizesOneTwoInstance) x with
  | some i => decide (WellFormed i ∧ DynamicStorageAllocationSizesOneTwoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DynamicStorageAllocationSizesOneTwo
