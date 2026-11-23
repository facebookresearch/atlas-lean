/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DYNAMIC STORAGE ALLOCATION with sizes 1 and 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR2] DYNAMIC STORAGE ALLOCATION,
p. 226 (comment: NP-complete in the strong sense, even if `s(a) ∈ {1, 2}` for all `a ∈ A`;
the entry's reference is [Stockmeyer, 1976b], listed by Garey and Johnson as a private
communication, which was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DynamicStorageAllocationWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DynamicStorageAllocationSizesOneTwo

/-!
# DYNAMIC STORAGE ALLOCATION with sizes 1 and 2 is NP-complete

INSTANCE: a set `A` of items to be stored, each `a ∈ A` having a size `s(a) ∈ {1, 2}`, an
arrival time `r(a) ∈ ℤ₀⁺`, and a departure time `d(a) ∈ ℤ⁺`, and a positive integer storage
size `D`.
QUESTION: is there a feasible allocation of storage for `A`, i.e., a function
`σ : A → {1, 2, ..., D}` such that for every `a ∈ A` the allocated storage interval
`I(a) = [σ(a), σ(a) + s(a) - 1]` is contained in `[1, D]` and such that, for all `a, a' ∈ A`,
if `I(a) ∩ I(a')` is nonempty then either `d(a) ≤ r(a')` or `d(a') ≤ r(a)`?

This is the restriction of [SR2] DYNAMIC STORAGE ALLOCATION
(`WantedExt.Complexity.NPComplete.DynamicStorageAllocationWanted`) to item sizes `1` and `2`.
The instance type, the base well-formedness, the storage intervals and the question are those
of the parent, reused unchanged (items are a list of records `(s(a), r(a), d(a))`, the last
condition is required for distinct items, and `r(a) < d(a)` is not required, as in the source);
this module adds only the restriction `s(a) ∈ {1, 2}` to `WellFormed`. Garey and Johnson state
the problem NP-complete in the strong sense under this restriction, so the binary encoding of
the times and of `D` does not matter.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **DYNAMIC STORAGE ALLOCATION with sizes 1 and 2 is NP-complete.** Source: Garey and Johnson
(1979), [SR2], comment (the entry cites Stockmeyer, private communication). -/
public theorem_wanted dynamicStorageAllocationSizesOneTwo_npComplete :
    dynamicStorageAllocationSizesOneTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dynamicStorageAllocationSizesOneTwoDec

end MetaMathlibExt.Complexity.NPComplete.DynamicStorageAllocationSizesOneTwo
