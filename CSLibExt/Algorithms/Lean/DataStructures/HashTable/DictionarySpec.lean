/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DictionarySpec
public import CSLibExt.Algorithms.Lean.DataStructures.HashTable.EraseCost

/-!
# Hash-table adapter for the finite-map specification record

Separate-chaining hash tables refine `FiniteMapSpec`, with the provider's
bucket-concatenation abstraction as the finite-map abstraction and its
bucket-placement validity as the invariant.
-/

set_option autoImplicit false

universe u v

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace DictionarySpec

/-- Separate-chaining hash tables refine the finite-map record, with the
provider's bucket-concatenation abstraction and its bucket-placement
validity as the invariant. The empty table fixes the hash function and a
positive bucket count. -/
public def hashSpec {α : Type u} {β : Type v} [DecidableEq α] (hash : α → Nat)
    (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount) :
    FiniteMapSpec α β (HashTable α β hash) where
  empty := HashTable.empty hash bucketCount bucketCount_pos
  insert := HashTable.insert
  erase := HashTable.erase
  lookup := HashTable.lookup
  inv := HashTable.Valid
  toFinmap := HashTable.abstraction
  inv_empty := by exact HashTable.valid_empty hash bucketCount bucketCount_pos
  inv_insert := by intro x v s hs; exact HashTable.valid_insert x v s hs
  inv_erase := by intro x s hs; exact HashTable.valid_erase x s hs
  toFinmap_empty := by
    exact HashTable.abstraction_empty hash bucketCount bucketCount_pos
  toFinmap_insert := by
    intro x v s hs; exact HashTable.abstraction_insert x v s hs
  toFinmap_erase := by intro x s hs; exact HashTable.abstraction_erase x s hs
  lookup_eq_toFinmap := by
    intro x s hs; exact (HashTable.lookup_abstraction x s hs).symm

end DictionarySpec
end Cslib.Algorithms.Lean
end
