/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BloomFilter

/-!
# Tests for Bloom filters

Client examples exercise empty lookup, insertion, collisions/false positives, and the
zero-hash boundary, and check that the public theorems apply without unfolding the
implementation. The final commands audit the transitive axioms of every public theorem.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BloomFilterTests

open Cslib.Algorithms.Lean

private def hId : Nat → Fin 7 := fun x => ⟨x % 7, Nat.mod_lt _ (by decide)⟩
private def hAlt : Nat → Fin 7 := fun x => ⟨(x + 3) % 7, Nat.mod_lt _ (by decide)⟩

private def emptyTwo : BloomFilter Nat 7 := BloomFilter.empty [hId, hAlt]

-- Empty filter reports absent when there is at least one hash.
example : emptyTwo.mayContain 1 = false := by decide
example (x : Nat) : emptyTwo.mayContain x = false :=
  BloomFilter.mayContain_empty (by decide) x

-- Inserted element is reported present (no false negative).
example : (emptyTwo.insert 1).mayContain 1 = true := by decide
example (x : Nat) : (emptyTwo.insert x).mayContain x = true :=
  BloomFilter.mayContain_insert_self emptyTwo x

-- A different element whose hash bits are disjoint is reported absent.
example : (emptyTwo.insert 0).mayContain 1 = false := by decide

-- Collision / false positive: 8 collides with 1 under both hashes mod 7.
example : (emptyTwo.insert 1).mayContain 8 = true := by decide

-- Monotonicity: later inserts preserve earlier positives.
example (x y : Nat) (h : emptyTwo.mayContain x = true) :
    (emptyTwo.insert y).mayContain x = true :=
  BloomFilter.mayContain_insert_mono emptyTwo x y h

-- Bit characterization through the public theorem.
example (x : Nat) (i : Fin 7) :
    (emptyTwo.insert x).bits[i] = true ↔
      emptyTwo.bits[i] = true ∨ ∃ h ∈ emptyTwo.hashes, h x = i :=
  BloomFilter.bit_insert_iff emptyTwo x i

example (x : Nat) :
    emptyTwo.mayContain x = true ↔ ∀ h ∈ emptyTwo.hashes, emptyTwo.bits[h x] = true :=
  BloomFilter.mayContain_iff emptyTwo x

-- Zero-hash boundary: with no hashes, `mayContain` is vacuously true and
-- `insert` changes nothing.
example : (BloomFilter.empty ([] : List (Nat → Fin 3)) : BloomFilter Nat 3).mayContain 5 = true := by decide
example : ((BloomFilter.empty ([] : List (Nat → Fin 3)) : BloomFilter Nat 3).insert 5).mayContain 7 = true := by decide

-- Zero-bit boundary typechecks (Fin 0 admits no hash target, so hashes must be empty).
example : (BloomFilter.empty ([] : List (Nat → Fin 0)) : BloomFilter Nat 0).mayContain 0 = true := by decide

-- Single hash: non-colliding miss and colliding false positive (9 % 5 = 4).
private def hMod5 : Nat → Fin 5 := fun x => ⟨x % 5, Nat.mod_lt _ (by decide)⟩
private def emptyOne : BloomFilter Nat 5 := BloomFilter.empty [hMod5]
example : (emptyOne.insert 4).mayContain 4 = true := by decide
example : (emptyOne.insert 4).mayContain 3 = false := by decide
example : (emptyOne.insert 4).mayContain 9 = true := by decide

end Cslib.Algorithms.Lean.BloomFilterTests

#print axioms Cslib.Algorithms.Lean.BloomFilter.bit_insert_iff
#print axioms Cslib.Algorithms.Lean.BloomFilter.mayContain_iff
#print axioms Cslib.Algorithms.Lean.BloomFilter.mayContain_insert_self
#print axioms Cslib.Algorithms.Lean.BloomFilter.mayContain_insert_mono
#print axioms Cslib.Algorithms.Lean.BloomFilter.mayContain_empty
