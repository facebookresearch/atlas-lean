/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.CuckooHashing

/-!
# Tests for cuckoo hashing

Client examples exercise empty lookup, direct placement, an eviction chain, zero-fuel
and cycle failure, replacement in each table, and the duplicate-copy replacement
regression: a key stored in both slots must not keep a stale value in the other slot
after replacement. The final commands audit the transitive axioms of every public
theorem.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.CuckooHashingTests

open Cslib.Algorithms.Lean

private def hh : Nat → Fin 2 := fun k => ⟨k % 2, Nat.mod_lt _ (by decide)⟩

private def e2 : CuckooHashing Nat Nat 2 hh hh := CuckooHashing.empty

-- Empty lookup misses; the eviction path with zero fuel fails.
example : e2.lookup 0 = none := by decide
example : e2.insert 0 10 0 = none := by decide

-- Direct placement into the vacant first slot.
example : (e2.insert 0 10 5).map (fun t => (t.lookup 0, t.lookup 1)) =
    some (some 10, none) := by decide

-- Collision eviction chain: keys 0 and 2 share slot 0 in both tables, so inserting 2
-- evicts 0 into the second table; both keys remain findable.
example : ((e2.insert 0 10 5).bind (fun t => t.insert 2 20 5)).map
      (fun t => (t.lookup 0, t.lookup 2, t.table1.get (hh 0), t.table2.get (hh 0))) =
    some (some 10, some 20, some (2, 20), some (0, 10)) := by decide

-- Replacement in the second table: key 0 lives in table2 after the eviction above.
example : (((e2.insert 0 10 5).bind (fun t => t.insert 2 20 5)).bind
      (fun t => t.insert 0 99 5)).map (fun t => (t.lookup 0, t.lookup 2)) =
    some (some 99, some 20) := by decide

-- Replacement in the first table with no duplicate elsewhere.
example : ((e2.insert 0 10 5).bind (fun t => t.insert 0 11 5)).map
      (fun t => t.lookup 0) = some (some 11) := by decide

private def hOne : Nat → Fin 1 := fun _ => ⟨0, by decide⟩

-- Regression: the same binding in both candidate slots (allowed by `Valid`/`KeyDet`
-- for m = 1 with equal hashes). Replacement must clear the stale copy.
private def dupTable : CuckooHashing Nat Nat 1 hOne hOne :=
  ⟨#v[some (0, 0)], #v[some (0, 0)]⟩

private theorem dupValid : dupTable.Valid := by
  constructor <;> intro i k v h
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    change some (0, 0) = some (k, v) at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    rfl
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    change some (0, 0) = some (k, v) at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    rfl

private theorem dupKeyDet : dupTable.KeyDet := by
  intro k v₁ v₂ h1 h2
  have key : ∀ v, dupTable.Stored k v → v = 0 := by
    intro v hv
    rcases hv with ⟨i, hi⟩ | ⟨i, hi⟩
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      change some (0, 0) = some (k, v) at hi
      exact (Prod.mk.inj (Option.some.inj hi)).2.symm
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      change some (0, 0) = some (k, v) at hi
      exact (Prod.mk.inj (Option.some.inj hi)).2.symm
  rw [key v₁ h1, key v₂ h2]

example : (dupTable.insert 0 1 0).map
      (fun t => (t.lookup 0, t.table1.get (0 : Fin 1), t.table2.get (0 : Fin 1))) =
    some (some 1, some (0, 1), none) := by decide

example (u : CuckooHashing Nat Nat 1 hOne hOne) (h : dupTable.insert 0 1 0 = some u) :
    u.KeyDet :=
  CuckooHashing.keyDet_insert dupTable 0 1 0 u h dupValid dupKeyDet

-- Cycle/fuel failure: three keys for two slots (m = 1) can never all be placed.
private def e1 : CuckooHashing Nat Nat 1 hOne hOne := CuckooHashing.empty
example : (((e1.insert 0 10 5).bind (fun t => t.insert 1 11 5)).bind
    (fun t => t.insert 2 12 10)) = none := by decide

-- Public API theorems through the client surface.
example : (CuckooHashing.empty : CuckooHashing Nat Nat 2 hh hh).Valid :=
  CuckooHashing.valid_empty
example : (CuckooHashing.empty : CuckooHashing Nat Nat 2 hh hh).KeyDet :=
  CuckooHashing.keyDet_empty
example (t u : CuckooHashing Nat Nat 2 hh hh) (h : t.insert 3 30 4 = some u) :
    u.Stored 3 30 := CuckooHashing.stored_insert t 3 30 4 u h
example (t u : CuckooHashing Nat Nat 2 hh hh) (h : t.insert 3 30 4 = some u)
    (hv : t.Valid) : u.Valid := CuckooHashing.valid_insert t 3 30 4 u h hv
example (t u : CuckooHashing Nat Nat 2 hh hh) (h : t.insert 3 30 4 = some u)
    (hv : t.Valid) (hd : t.KeyDet) : u.KeyDet :=
  CuckooHashing.keyDet_insert t 3 30 4 u h hv hd
example (t u : CuckooHashing Nat Nat 2 hh hh) (hv : t.Valid) (hd : t.KeyDet)
    (h : t.insert 3 30 4 = some u) : u.lookup 3 = some 30 :=
  CuckooHashing.lookup_insert t hv hd 3 30 4 u h

-- Preservation of unrelated bindings, generic form.
example (t u : CuckooHashing Nat Nat 2 hh hh) (hv : t.Valid)
    (h : t.insert 3 30 4 = some u) (v : Nat) :
    u.Stored 5 v ↔ t.Stored 5 v :=
  CuckooHashing.stored_insert_iff_of_ne t hv 3 30 4 u h (by decide)
example (t u : CuckooHashing Nat Nat 2 hh hh) (hv : t.Valid) (hd : t.KeyDet)
    (h : t.insert 3 30 4 = some u) : u.lookup 5 = t.lookup 5 :=
  CuckooHashing.lookup_insert_of_ne t hv hd 3 30 4 u h (by decide)

-- Eviction path: inserting 2 evicts 0 to the second table; lookups for the
-- unrelated keys 0 and 1 are preserved by the generic law and by computation.
example : ((e2.insert 0 10 5).bind (fun t => t.insert 2 20 5)).map
      (fun t => (t.lookup 0, t.lookup 1)) = some (some 10, none) := by decide
example (t u : CuckooHashing Nat Nat 2 hh hh) (hv : t.Valid) (hd : t.KeyDet)
    (h : t.insert 2 20 5 = some u) : u.lookup 0 = t.lookup 0 :=
  CuckooHashing.lookup_insert_of_ne t hv hd 2 20 5 u h (by decide)

-- Replacement path: replacing key 0 (in whichever table it occupies) keeps
-- the unrelated binding for key 2, by the generic law and by computation.
example : (((e2.insert 0 10 5).bind (fun t => t.insert 2 20 5)).bind
      (fun t => t.insert 0 99 5)).map (fun t => t.lookup 2) =
    some (some 20) := by decide
example (t u : CuckooHashing Nat Nat 2 hh hh) (hv : t.Valid) (hd : t.KeyDet)
    (h : t.insert 0 99 5 = some u) : u.lookup 2 = t.lookup 2 :=
  CuckooHashing.lookup_insert_of_ne t hv hd 0 99 5 u h (by decide)

end Cslib.Algorithms.Lean.CuckooHashingTests

#print axioms Cslib.Algorithms.Lean.CuckooHashing.valid_empty
#print axioms Cslib.Algorithms.Lean.CuckooHashing.keyDet_empty
#print axioms Cslib.Algorithms.Lean.CuckooHashing.lookup_empty
#print axioms Cslib.Algorithms.Lean.CuckooHashing.lookup_sound
#print axioms Cslib.Algorithms.Lean.CuckooHashing.lookup_isSome_of_stored
#print axioms Cslib.Algorithms.Lean.CuckooHashing.lookup_eq_some_of_stored
#print axioms Cslib.Algorithms.Lean.CuckooHashing.lookup_eq_some_iff_stored
#print axioms Cslib.Algorithms.Lean.CuckooHashing.stored_insert
#print axioms Cslib.Algorithms.Lean.CuckooHashing.valid_insert
#print axioms Cslib.Algorithms.Lean.CuckooHashing.keyDet_insert
#print axioms Cslib.Algorithms.Lean.CuckooHashing.lookup_insert
#print axioms Cslib.Algorithms.Lean.CuckooHashing.stored_insert_iff_of_ne
#print axioms Cslib.Algorithms.Lean.CuckooHashing.lookup_insert_of_ne
