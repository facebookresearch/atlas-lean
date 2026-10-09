/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.HashTable

/-!
# Tests for separate-chaining hash tables

These client examples exercise the smallest bucket count, empty lookup, insertion, replacement,
colliding and noncolliding keys, validity preservation, and the finite-map abstraction. The final
commands audit the transitive axioms of every public theorem.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.HashTableTests

open HashTable

private def identityHash (key : Nat) : Nat := key

private def oneBucket : HashTable Nat String identityHash :=
  empty identityHash 1 (by decide)

private def twoBuckets : HashTable Nat String identityHash :=
  empty identityHash 2 (by decide)

example : lookup 0 oneBucket = none := by decide
example (k : Nat) :
    lookup k (empty identityHash 1 (by decide) : HashTable Nat String identityHash) = none := by
  simp
example : abstraction oneBucket = ∅ := by simp [oneBucket]
example : lookup 7 (insert 7 "first" oneBucket) = some "first" := by decide
example : lookup 7 (insert 7 "second" (insert 7 "first" oneBucket)) = some "second" := by decide

private def collisionTable : HashTable Nat String identityHash :=
  insert 3 "three" (insert 1 "one" twoBuckets)

example : lookup 1 collisionTable = some "one" := by decide
example : lookup 3 collisionTable = some "three" := by decide

private def noncollisionTable : HashTable Nat String identityHash :=
  insert 1 "one" (insert 0 "zero" twoBuckets)

example : lookup 0 noncollisionTable = some "zero" := by decide
example : lookup 1 noncollisionTable = some "one" := by decide

example : Valid oneBucket := valid_empty identityHash 1 (by decide)

example : Valid collisionTable := by
  exact valid_insert 3 "three" (insert 1 "one" twoBuckets)
    (valid_insert 1 "one" twoBuckets (valid_empty identityHash 2 (by decide)))

example : Finmap.lookup 3 (abstraction collisionTable) = some "three" := by
  rw [lookup_abstraction 3 collisionTable]
  · rfl
  · exact valid_insert 3 "three" (insert 1 "one" twoBuckets)
      (valid_insert 1 "one" twoBuckets (valid_empty identityHash 2 (by decide)))

example : abstraction collisionTable =
    Finmap.insert 3 "three" (abstraction (insert 1 "one" twoBuckets)) := by
  exact abstraction_insert 3 "three" (insert 1 "one" twoBuckets)
    (valid_insert 1 "one" twoBuckets (valid_empty identityHash 2 (by decide)))

end Cslib.Algorithms.Lean.HashTableTests

#print axioms Cslib.Algorithms.Lean.HashTable.valid_empty
#print axioms Cslib.Algorithms.Lean.HashTable.lookup_empty
#print axioms Cslib.Algorithms.Lean.HashTable.lookup_insert
#print axioms Cslib.Algorithms.Lean.HashTable.lookup_insert_of_ne
#print axioms Cslib.Algorithms.Lean.HashTable.valid_insert
#print axioms Cslib.Algorithms.Lean.HashTable.lookup_abstraction
#print axioms Cslib.Algorithms.Lean.HashTable.abstraction_empty
#print axioms Cslib.Algorithms.Lean.HashTable.abstraction_insert
