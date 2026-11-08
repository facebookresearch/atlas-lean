/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.OpenAddressing
public import Mathlib.Data.List.Sort

/-!
# Tests for the open-addressing hash table API

These client examples exercise linear probing with collisions, exact
replacement of an existing binding (the key-uniqueness part of `Valid`),
the distinct-key frame theorem for insertion on colliding keys,
insertion failure on a full probe sequence and on a non-permuting probe,
validity preservation, and the value-level lookup characterization. A
hand-built table holding one key in two slots is the negative example:
it is probe-closed but not `Valid`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.OpenAddressingTests

open OpenAddressing

/-- Five slots, identity hash, linear probing: keys collide modulo `5`. -/
public def probe5 : Nat → Nat → Fin 5 := linearProbe (fun k => k) 5 (by decide)

public def empty5 : OpenAddressing Nat Nat 5 probe5 := empty

public def put {probe : Nat → Nat → Fin 5}
    (table : OpenAddressing Nat Nat 5 probe) (k v : Nat) :
    OpenAddressing Nat Nat 5 probe :=
  (insert table k v).getD table

/-- Keys `1` and `6` collide (both hash to slot `1`); `6` lands in slot `2`. -/
public def table3 : OpenAddressing Nat Nat 5 probe5 :=
  put (put (put empty5 1 10) 6 60) 3 30

private theorem valid_put {probe : Nat → Nat → Fin 5}
    {table : OpenAddressing Nat Nat 5 probe} (hv : Valid table) {k v : Nat}
    (h : (insert table k v).isSome) : Valid (put table k v) := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
  have hput : put table k v = u := by simp [put, hu]
  rw [hput]
  exact valid_insert _ _ _ _ hv hu

private theorem table3_valid : Valid table3 :=
  valid_put
    (valid_put (valid_put valid_empty (by decide)) (by decide))
    (by decide)

example : Valid empty5 := valid_empty

example : lookup empty5 1 = none := lookup_empty 1

example : lookup table3 1 = some 10 := by decide

/-- The colliding key is found by probing past the first slot. -/
example : lookup table3 6 = some 60 := by decide

example : lookup table3 3 = some 30 := by decide

example : lookup table3 4 = none := by decide

/-- Probing for an absent key that collides stops at the first empty slot. -/
example : lookup table3 11 = none := by decide

/-! ### Replacement is exact under key uniqueness -/

/-- One key stored in two slots: probe-closed, but not `Valid`. This is
the stale-binding configuration that the uniqueness clause excludes. -/
public def dupTable : OpenAddressing Nat Nat 5 probe5 :=
  ⟨#v[some (1, 10), some (1, 20), none, none, none]⟩

example : ¬ Valid dupTable := by
  intro h
  have h01 : (⟨0, by decide⟩ : Fin 5) = ⟨1, by decide⟩ :=
    h.2 _ _ 1 10 20 rfl rfl
  exact absurd (Fin.ext_iff.mp h01) (by decide)

/-- In a valid table the binding for a key is unique, so after replacing
`1 ↦ 10` by `1 ↦ 11` the old value is stored nowhere. -/
example : lookup (put table3 1 11) 1 = some 11 := by decide

example : ∀ updated : OpenAddressing Nat Nat 5 probe5,
    insert table3 1 11 = some updated →
      lookup updated 1 = some 11 ∧ ¬ Stored updated 1 10 := by
  intro updated hins
  have hValid3 : Valid table3 := table3_valid
  have hValidU := valid_insert _ _ _ _ hValid3 hins
  have hlookup := lookup_insert _ _ _ _ hins
  refine ⟨hlookup, fun hstored => ?_⟩
  have h10 := (lookup_eq_some_iff updated 1 10 hValidU).mpr hstored
  rw [hlookup] at h10
  exact absurd h10 (by decide)

example : Stored table3 6 60 :=
  (lookup_eq_some_iff table3 6 60 table3_valid).mp (by decide)

/-! ### Distinct keys are unaffected by an insert (frame theorem) -/

/-- Replacing the colliding key `1` leaves the lookup of `6`, which probes
past slot `1`, at its old value. -/
example : ∀ updated : OpenAddressing Nat Nat 5 probe5,
    insert table3 1 11 = some updated → lookup updated 6 = some 60 := by
  intro updated hins
  rw [lookup_insert_of_ne table3 1 11 updated table3_valid hins (by decide)]
  decide

/-- Inserting the new colliding key `11` (which probes slots `1, 2, 3`
before landing in slot `4`) leaves the lookups and stored bindings of the
keys already on that probe sequence unchanged. -/
example : ∀ updated : OpenAddressing Nat Nat 5 probe5,
    insert table3 11 110 = some updated →
      lookup updated 6 = lookup table3 6 ∧
        (Stored updated 3 30 ↔ Stored table3 3 30) := by
  intro updated hins
  exact ⟨lookup_insert_of_ne table3 11 110 updated table3_valid hins
      (by decide),
    stored_insert_of_ne table3 11 110 updated hins (by decide)⟩

/-! ### Insertion failure -/

/-- A full table: every further insert fails. -/
public def fullTable : OpenAddressing Nat Nat 5 probe5 :=
  put (put (put (put (put empty5 0 0) 1 10) 2 20) 3 30) 4 40

example : insert fullTable 7 70 = none := by decide

/-- Replacing an existing key in a full table still succeeds. -/
example : (insert fullTable 2 22).isSome := by decide

/-- A non-permuting probe: every key only ever probes slot `0`, so the
second distinct insert fails even though other slots are empty. -/
public def constProbe : Nat → Nat → Fin 5 := fun _ _ => ⟨0, by decide⟩

example : insert (put (empty : OpenAddressing Nat Nat 5 constProbe) 1 10)
    2 20 = none := by decide

/-- Failure means every probed slot holds another key (public spec). -/
example : ∀ attempts < 5, ∃ otherKey otherValue : Nat,
    fullTable.slots.get (probe5 7 attempts) = some (otherKey, otherValue) ∧
      otherKey ≠ 7 :=
  occupied_of_insert_eq_none fullTable 7 70 (by decide)

#print axioms lookup_eq_some_iff
#print axioms lookup_insert_of_ne
#print axioms valid_insert
#print axioms stored_unique

end Cslib.Algorithms.Lean.OpenAddressingTests
