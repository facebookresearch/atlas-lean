/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing

import Mathlib.Tactic.FinCases

/-!
# Tests for perfect (two-level) hashing

These client examples build a concrete nonempty valid table (identity
hashes, two buckets of four slots: even keys in bucket `0`, odd keys in
bucket `1`, slot `k % 4` within the bucket) and exercise lookup in its
matching-key, mismatching-key, vacant-slot, and empty-bucket branches,
plus `entries`, uniqueness, and the FKS sizing counters.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.PerfectHashingTests

open PerfectHashing

/-- Identity primary hash. -/
public def idHash : Nat → Nat := fun k => k

/-- Four keys: `0 ↦ 100` and `2 ↦ 102` in bucket `0`; `1 ↦ 101` and
`3 ↦ 103` in bucket `1`. -/
public def table4 : PerfectHashing Nat Nat idHash where
  bucketCount := 2
  bucketCount_pos := by decide
  secondarySize := fun _ => 4
  secondaryHash := fun _ k => k
  secondaryTable := fun i =>
    if i.val = 0 then
      #v[some (0, 100), none, some (2, 102), none]
    else
      #v[none, some (1, 101), none, some (3, 103)]

private theorem table4_valid : Valid table4 := by
  apply Valid.mk_of_placed
  intro i j key value h
  fin_cases i <;> fin_cases j <;> simp_all [table4, idHash, Vector.get] <;> omega

example : Valid table4 := table4_valid

/-! ### Lookup branches -/

/-- Matching key at the probed slot, in each bucket. -/
example : lookup 0 table4 = some 100 := by decide

example : lookup 2 table4 = some 102 := by decide

example : lookup 1 table4 = some 101 := by decide

example : lookup 3 table4 = some 103 := by decide

/-- Mismatching key at the probed slot: `4` probes the slot of `0`,
`5` probes the slot of `1`. -/
example : lookup 4 table4 = none := by decide

example : lookup 5 table4 = none := by decide

/-- One bucket of two slots with only slot `0` occupied, so that key `1`
probes the in-range but vacant slot `1`. -/
public def tableVacant : PerfectHashing Nat Nat idHash where
  bucketCount := 1
  bucketCount_pos := by decide
  secondarySize := fun _ => 2
  secondaryHash := fun _ k => k
  secondaryTable := fun _ => #v[some (0, 100), none]

private theorem tableVacant_valid : Valid tableVacant := by
  apply Valid.mk_of_placed
  intro i j key value h
  fin_cases i <;> fin_cases j <;> simp_all [tableVacant, idHash, Vector.get] <;> omega

example : Valid tableVacant := tableVacant_valid

/-- Vacant-slot branch: `1` probes in-range slot `1`, which is empty. -/
example : lookup 1 tableVacant = none := by decide

/-- Occupied slot in the same table still resolves. -/
example : lookup 0 tableVacant = some 100 := by decide

/-- The same facts through the public specifications. -/
example : lookup 2 table4 = some 102 :=
  lookup_eq_some_of_stored table4_valid ⟨⟨0, by decide⟩, ⟨2, by decide⟩, rfl⟩

example : Stored table4 3 103 :=
  stored_of_lookup_eq_some (by decide : lookup 3 table4 = some 103)

example : ¬ Stored table4 4 100 := fun hstored => by
  have h := lookup_eq_some_of_stored table4_valid hstored
  rw [show lookup 4 table4 = none by decide] at h
  exact absurd h (by simp)

example : lookup 4 table4 = none :=
  (lookup_eq_none_iff table4_valid 4).mpr (fun v hv => by
    have h := lookup_eq_some_of_stored table4_valid hv
    rw [show lookup 4 table4 = none by decide] at h
    exact absurd h (by simp))

/-- Empty secondary tables (`secondarySize = 0`): lookup takes the
no-slot branch. -/
example : lookup 1 ((empty idHash 2 (by decide) (fun _ => 0) (fun _ k => k) :
    PerfectHashing Nat Nat idHash)) = none :=
  lookup_empty _ _ _ _ _

example : Valid ((empty idHash 2 (by decide) (fun _ => 0) (fun _ k => k) :
    PerfectHashing Nat Nat idHash)) :=
  valid_empty _ _ _ _

example : entries ((empty idHash 2 (by decide) (fun _ => 4) (fun _ k => k) :
    PerfectHashing Nat Nat idHash)) = [] :=
  entries_empty _ _ _ _

/-! ### Contents and uniqueness -/

example : entries table4 = [(0, 100), (2, 102), (1, 101), (3, 103)] := by
  decide

example : (2, 102) ∈ table4.entries :=
  (mem_entries_iff table4 2 102).mpr ⟨⟨0, by decide⟩, ⟨2, by decide⟩, rfl⟩

example : (2, 999) ∉ table4.entries := by
  decide

/-- `stored_unique` needs no `DecidableEq` on keys. -/
example {α β : Type} {primaryHash : α → Nat}
    {table : PerfectHashing α β primaryHash} (valid : Valid table)
    {key : α} {v₁ v₂ : β} (h₁ : Stored table key v₁)
    (h₂ : Stored table key v₂) : v₁ = v₂ :=
  stored_unique valid h₁ h₂

example : ∀ v : Nat, Stored table4 2 v → v = 102 :=
  fun v hv => stored_unique table4_valid hv ⟨⟨0, by decide⟩, ⟨2, by decide⟩, rfl⟩

/-! ### Sizing counters -/

example : bucketSize table4 ⟨0, by decide⟩ = 2 := by decide

example : bucketSize table4 ⟨1, by decide⟩ = 2 := by decide

example : totalKeys table4 = 4 := by decide

example : totalSecondarySpace table4 = 8 := by decide

/-- Each bucket has `4 = 2²` slots for its `2` keys: the FKS rule. -/
example : SquareSized table4 := by
  intro i
  fin_cases i <;> decide

example : totalSecondarySpace table4 =
    ∑ i : Fin table4.bucketCount, (bucketSize table4 i) ^ 2 :=
  totalSecondarySpace_eq_sum_sq (by
    intro i
    fin_cases i <;> decide)

example : totalSecondarySpace table4 ≤ (totalKeys table4) ^ 2 :=
  totalSecondarySpace_le_totalKeys_sq (by
    intro i
    fin_cases i <;> decide)

example : ∀ i : Fin table4.bucketCount,
    bucketSize table4 i ≤ table4.secondarySize i :=
  fun i => bucketSize_le_secondarySize table4 i

#print axioms lookup_eq_some_of_stored
#print axioms stored_unique
#print axioms totalSecondarySpace_le_totalKeys_sq

end Cslib.Algorithms.Lean.PerfectHashingTests
