/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DYNAMIC STORAGE ALLOCATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR2] DYNAMIC STORAGE ALLOCATION,
p. 226 (reference: [Stockmeyer, 1976b], a private communication; transformation from
3-PARTITION).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DynamicStorageAllocation

/-- An instance: the items `(s(a), r(a), d(a))` (size, arrival time, departure time) and the
storage size `D`. -/
abbrev DynamicStorageAllocationInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every size and every departure time is positive, and `D` is
positive. -/
def WellFormed (i : DynamicStorageAllocationInstance) : Prop :=
  (∀ a ∈ i.1, 0 < a.1 ∧ 0 < a.2.2) ∧ 0 < i.2

/-- The storage interval `I(a) = [σ(a), σ(a) + s(a) - 1]` of item `a` under the allocation
`σ`. -/
def storageInterval (i : DynamicStorageAllocationInstance) (σ : Fin i.1.length → ℕ)
    (a : Fin i.1.length) : Finset ℕ :=
  Finset.Icc (σ a) (σ a + (i.1.get a).1 - 1)

/-- Some allocation `σ : A → {1, ..., D}` places every storage interval inside `[1, D]` and
gives distinct items intersecting storage intervals only if one departs no later than the
other arrives. -/
def DynamicStorageAllocationFeasible (i : DynamicStorageAllocationInstance) : Prop :=
  ∃ σ : Fin i.1.length → ℕ, (∀ a, σ a ∈ Finset.Icc 1 i.2) ∧
    (∀ a, storageInterval i σ a ⊆ Finset.Icc 1 i.2) ∧
    ∀ a a', a ≠ a' → (storageInterval i σ a ∩ storageInterval i σ a').Nonempty →
      (i.1.get a).2.2 ≤ (i.1.get a').2.1 ∨ (i.1.get a').2.2 ≤ (i.1.get a).2.1

open Classical in
/-- DYNAMIC STORAGE ALLOCATION as a decision problem over bitstrings. -/
noncomputable def dynamicStorageAllocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DynamicStorageAllocationInstance) x with
  | some i => decide (WellFormed i ∧ DynamicStorageAllocationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DynamicStorageAllocation
