/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.HashTable.DictionarySpec

/-!
# Examples for the hash-table finite-map adapter

Small examples exercising `hashSpec` through the `FiniteMapSpec` interface.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.HashDictionarySpecTest

open Cslib.Algorithms.Lean.DictionarySpec

private abbrev natSpec : FiniteMapSpec Nat Nat (HashTable Nat Nat (fun n => n)) :=
  hashSpec (fun n => n) 4 (by decide)

example (x v : Nat) {s} (hs : natSpec.inv s) :
    natSpec.lookup x (natSpec.insert x v s) = some v :=
  natSpec.lookup_insert_self x v hs

example (x : Nat) {s} (hs : natSpec.inv s) :
    natSpec.lookup x (natSpec.erase x s) = none :=
  natSpec.lookup_erase_self x hs

example : natSpec.toFinmap natSpec.empty = ∅ := natSpec.toFinmap_empty

example : natSpec.lookup 1 (natSpec.insert 1 2 natSpec.empty) = some 2 :=
  natSpec.lookup_insert_self 1 2 natSpec.inv_empty

example (x : Nat) {s} (hs : natSpec.inv s) :
    natSpec.lookup x s = Finmap.lookup x (natSpec.toFinmap s) :=
  natSpec.lookup_eq_toFinmap x hs

end Cslib.Algorithms.Lean.HashDictionarySpecTest
end
