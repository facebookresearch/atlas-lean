/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.HashTable
public import Cslib.Algorithms.Lean.TimeM

/-!
# Hash-table erasure and scan-event bounds

Lookup and erasure return the result of their actual chain scan together with a `TimeM Nat`
event count. An empty terminus costs one event, a successful comparison costs one, and an
unsuccessful comparison costs one plus the recursive scan. Hash computation, modulus, bucket
access/update, and comparator internals are unpriced. These are declared scan events, not CPU,
bit, or Turing-machine time. An absent query costs exactly the chain length plus one; a present
query costs at most the chain length. No expected-time or bucket-cardinality claim is made.

The erased list agrees with `List.kerase`, the erased bucket with `AList.erase`, and deletion
of a valid table with `Finmap.erase`. Raw lists lose only their first matching entry; `AList`
supplies the distinct-key invariant needed for complete absence after deletion.

The scan algorithms and deletion API are adapted from fairinternal/formal-math PR #6201
(head `d5cebc9629a37d99e6e586b2ec398c9e63f169df`). Canonical erasure bridges replace its
auxiliary membership and nodup inductions; the absent/present bounds refine its length-plus-one
bound without changing the event convention.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cslib.Algorithms.Lean.HashTable

universe u v

/-- The literal hash-selected index used by the core table operations. -/
public def selectedBucket {α : Type u} {β : Type v} {hash : α → Nat}
    (table : HashTable α β hash) (key : α) : Fin table.bucketCount :=
  ⟨hash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩

/-- The selected chain's canonical lookup is the ordinary table lookup. -/
public theorem lookup_selectedBucket {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (table : HashTable α β hash) :
    AList.lookup key (table.buckets (selectedBucket table key)) = lookup key table := rfl

/--
Scans a chain for lookup. The counter records one event at an empty terminus or at a successful
comparison, and one event for each unsuccessful comparison before recursion.
-/
public def lookupChainWithCost {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) : List (Sigma β) → TimeM Nat (Option (β key))
  | [] => ⟨none, 1⟩
  | entry :: rest =>
      if same : key = entry.1 then
        ⟨some (same.symm ▸ entry.2), 1⟩
      else
        let result := lookupChainWithCost key rest
        ⟨result.ret, result.time + 1⟩

/-- Deletion's chain scan returns the retained entries and its comparison/terminal-event count. -/
public def eraseChainWithCost {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) : List (Sigma β) → TimeM Nat (List (Sigma β))
  | [] => ⟨[], 1⟩
  | entry :: rest =>
      if key = entry.1 then
        ⟨rest, 1⟩
      else
        let result := eraseChainWithCost key rest
        ⟨entry :: result.ret, result.time + 1⟩

/-- The empty lookup scan records its terminal event. -/
@[simp]
public theorem lookupChainWithCost_nil {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) : lookupChainWithCost (β := β) key [] = ⟨none, 1⟩ := rfl

/-- A head hit returns its dependent value after one event. -/
@[simp]
public theorem lookupChainWithCost_cons_eq {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (value : β key) (rest : List (Sigma β)) :
    lookupChainWithCost key (⟨key, value⟩ :: rest) = ⟨some value, 1⟩ := by
  simp [lookupChainWithCost]

/-- A head miss adds one event to the scan that supplies the result. -/
public theorem lookupChainWithCost_cons_ne {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (entry : Sigma β) (rest : List (Sigma β)) (different : key ≠ entry.1) :
    lookupChainWithCost key (entry :: rest) =
      ⟨(lookupChainWithCost key rest).ret, (lookupChainWithCost key rest).time + 1⟩ := by
  simp [lookupChainWithCost, different]

/-- The empty erasure scan records its terminal event. -/
@[simp]
public theorem eraseChainWithCost_nil {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) : eraseChainWithCost (β := β) key [] = ⟨[], 1⟩ := rfl

/-- A head hit removes only that entry after one event. -/
@[simp]
public theorem eraseChainWithCost_cons_eq {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (value : β key) (rest : List (Sigma β)) :
    eraseChainWithCost key (⟨key, value⟩ :: rest) = ⟨rest, 1⟩ := by
  simp [eraseChainWithCost]

/-- A head miss retains that entry and adds one event to the recursive erasure. -/
public theorem eraseChainWithCost_cons_ne {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (entry : Sigma β) (rest : List (Sigma β)) (different : key ≠ entry.1) :
    eraseChainWithCost key (entry :: rest) =
      ⟨entry :: (eraseChainWithCost key rest).ret, (eraseChainWithCost key rest).time + 1⟩ := by
  simp [eraseChainWithCost, different]

/-- Lookup performs at most one terminal event plus one comparison per chain entry. -/
public theorem lookupChainWithCost_cost_le {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (entries : List (Sigma β)) :
    (lookupChainWithCost key entries).time ≤ entries.length + 1 := by
  induction entries with
  | nil => simp
  | cons entry rest inductionHypothesis =>
      simp only [lookupChainWithCost]
      split
      · simp
      · dsimp
        omega

/-- The actual lookup scan returns the canonical dependent-list lookup. -/
public theorem lookupChainWithCost_result {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (entries : List (Sigma β)) :
    (lookupChainWithCost key entries).ret = List.dlookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      rcases entry with ⟨entryKey, entryValue⟩
      by_cases same : key = entryKey
      · subst entryKey
        simp [lookupChainWithCost, List.dlookup]
      · have reverse : entryKey ≠ key := fun equal => same equal.symm
        simp [lookupChainWithCost, List.dlookup, same, reverse, inductionHypothesis]

/-- The actual erasure scan removes the first matching entry, exactly as `List.kerase`. -/
public theorem eraseChainWithCost_result {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (entries : List (Sigma β)) :
    (eraseChainWithCost key entries).ret = List.kerase key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      by_cases same : key = entry.1
      · simp [eraseChainWithCost, same]
      · simp [eraseChainWithCost, same, inductionHypothesis]

/-- Lookup and erasure follow the same comparisons and terminal event. -/
public theorem eraseChainWithCost_time_eq {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (entries : List (Sigma β)) :
    (eraseChainWithCost key entries).time = (lookupChainWithCost key entries).time := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      by_cases same : key = entry.1
      · simp [eraseChainWithCost, lookupChainWithCost, same]
      · simp [eraseChainWithCost, lookupChainWithCost, same, inductionHypothesis]

/-- Deletion performs at most one terminal event plus one comparison per chain entry. -/
public theorem eraseChainWithCost_cost_le {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (entries : List (Sigma β)) :
    (eraseChainWithCost key entries).time ≤ entries.length + 1 := by
  rw [eraseChainWithCost_time_eq]
  exact lookupChainWithCost_cost_le key entries

/-- An absent query compares every entry and then records the empty terminus. -/
public theorem lookupChainWithCost_time_of_not_mem {α : Type u} {β : α → Type v}
    [DecidableEq α] (key : α) (entries : List (Sigma β))
    (absent : key ∉ entries.keys) :
    (lookupChainWithCost key entries).time = entries.length + 1 := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      have different : key ≠ entry.1 := fun same => absent (List.mem_cons.mpr (Or.inl same))
      have absentRest : key ∉ rest.keys := fun present =>
        absent (List.mem_cons.mpr (Or.inr present))
      rw [lookupChainWithCost_cons_ne key entry rest different]
      change (lookupChainWithCost key rest).time + 1 = (rest.length + 1) + 1
      rw [inductionHypothesis absentRest]

/-- A present query stops at a comparison, without an additional terminal event. -/
public theorem lookupChainWithCost_time_le_of_mem {α : Type u} {β : α → Type v}
    [DecidableEq α] (key : α) (entries : List (Sigma β)) (present : key ∈ entries.keys) :
    (lookupChainWithCost key entries).time ≤ entries.length := by
  induction entries with
  | nil => simp at present
  | cons entry rest inductionHypothesis =>
      by_cases same : key = entry.1
      · simp [lookupChainWithCost, same]
      · have presentRest : key ∈ rest.keys := (List.mem_cons.mp present).resolve_left same
        simpa only [lookupChainWithCost_cons_ne key entry rest same, List.length_cons] using
          Nat.add_le_add_right (inductionHypothesis presentRest) 1

/-- Erasing an absent raw key visits the full chain and its empty terminus. -/
public theorem eraseChainWithCost_time_of_not_mem {α : Type u} {β : α → Type v}
    [DecidableEq α] (key : α) (entries : List (Sigma β)) (absent : key ∉ entries.keys) :
    (eraseChainWithCost key entries).time = entries.length + 1 := by
  rw [eraseChainWithCost_time_eq]
  exact lookupChainWithCost_time_of_not_mem key entries absent

/-- Erasing a present raw key stops by the last entry, even if keys repeat. -/
public theorem eraseChainWithCost_time_le_of_mem {α : Type u} {β : α → Type v}
    [DecidableEq α] (key : α) (entries : List (Sigma β)) (present : key ∈ entries.keys) :
    (eraseChainWithCost key entries).time ≤ entries.length := by
  rw [eraseChainWithCost_time_eq]
  exact lookupChainWithCost_time_le_of_mem key entries present

/-- Erases a canonical chain, retaining the entries and time produced by the counted scan. -/
public def eraseBucketWithCost {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (bucket : AList β) : TimeM Nat (AList β) :=
  match bucket with
  | ⟨entries, nodup⟩ =>
      let result := eraseChainWithCost key entries
      ⟨⟨result.ret, by
          rw [eraseChainWithCost_result]
          exact List.NodupKeys.kerase key nodup⟩, result.time⟩

/-- The counted bucket erasure agrees with canonical `AList.erase`. -/
public theorem eraseBucketWithCost_result {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (bucket : AList β) :
    (eraseBucketWithCost key bucket).ret = AList.erase key bucket := by
  rcases bucket with ⟨entries, nodup⟩
  apply AList.ext
  exact eraseChainWithCost_result key entries

/-- Lookup in the erased bucket removes this key and preserves every other key. -/
public theorem lookup_eraseBucketWithCost {α : Type u} {β : α → Type v}
    [DecidableEq α] (key other : α) (bucket : AList β) :
    AList.lookup other (eraseBucketWithCost key bucket).ret =
      if other = key then none else AList.lookup other bucket := by
  rw [eraseBucketWithCost_result]
  by_cases same : other = key
  · subst other
    simp
  · simp [same]

/-- Bucket erasure has exactly the event count of lookup in the same entries. -/
public theorem eraseBucketWithCost_time_eq {α : Type u} {β : α → Type v} [DecidableEq α]
    (key : α) (bucket : AList β) :
    (eraseBucketWithCost key bucket).time = (lookupChainWithCost key bucket.entries).time := by
  rcases bucket with ⟨entries, nodup⟩
  exact eraseChainWithCost_time_eq key entries

/-- Costed bucket erasure costs at most one plus the bucket length. -/
public theorem eraseBucketWithCost_cost_le {α : Type u} {β : α → Type v}
    [DecidableEq α] (key : α) (bucket : AList β) :
    (eraseBucketWithCost key bucket).time ≤ bucket.entries.length + 1 := by
  rw [eraseBucketWithCost_time_eq]
  exact lookupChainWithCost_cost_le key bucket.entries

/-- Looks up a key and counts the branch events in the traversal that computes the result. -/
public def lookupWithCost {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (key : α) (table : HashTable α β hash) : TimeM Nat (Option β) :=
  lookupChainWithCost key (table.buckets (selectedBucket table key)).entries

/-- Deletes a key and counts the branch events in the traversal that computes the new bucket. -/
public def eraseWithCost {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (key : α) (table : HashTable α β hash) : TimeM Nat (HashTable α β hash) :=
  let selected := selectedBucket table key
  let result := eraseBucketWithCost key (table.buckets selected)
  ⟨{ bucketCount := table.bucketCount
     bucketCount_pos := table.bucketCount_pos
     buckets := Function.update table.buckets selected result.ret }, result.time⟩

/-- Deletes a key by scanning only its hash-selected chain. -/
public def erase {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (key : α) (table : HashTable α β hash) : HashTable α β hash :=
  (eraseWithCost key table).ret

/-- The costed lookup computes the original lookup result. -/
public theorem lookupWithCost_result {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (table : HashTable α β hash) :
    (lookupWithCost key table).ret = lookup key table := by
  exact lookupChainWithCost_result key (table.buckets (selectedBucket table key)).entries

/-- Costed lookup is bounded by one plus the selected bucket length. -/
public theorem lookupWithCost_cost_le {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (table : HashTable α β hash) :
    (lookupWithCost key table).time ≤
      (table.buckets
        ⟨hash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩).entries.length + 1 := by
  exact lookupChainWithCost_cost_le key (table.buckets (selectedBucket table key)).entries

/-- Lookup and erasure of the same table key have the same scan-event count. -/
public theorem eraseWithCost_time_eq {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (table : HashTable α β hash) :
    (eraseWithCost key table).time = (lookupWithCost key table).time := by
  exact eraseBucketWithCost_time_eq key (table.buckets (selectedBucket table key))

/-- Costed deletion is bounded by one plus the selected bucket length. -/
public theorem eraseWithCost_cost_le {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (table : HashTable α β hash) :
    (eraseWithCost key table).time ≤
      (table.buckets
        ⟨hash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩).entries.length + 1 := by
  rw [eraseWithCost_time_eq]
  exact lookupWithCost_cost_le key table

/-- An unsuccessful table lookup scans every selected entry and the empty terminus. -/
public theorem lookupWithCost_time_of_lookup_eq_none {α : Type u} {β : Type v}
    {hash : α → Nat} [DecidableEq α] (key : α) (table : HashTable α β hash)
    (absent : lookup key table = none) :
    (lookupWithCost key table).time =
      (table.buckets (selectedBucket table key)).entries.length + 1 := by
  apply lookupChainWithCost_time_of_not_mem
  exact List.dlookup_eq_none.mp absent

/-- A successful table lookup stops within the selected chain, with no terminal event. -/
public theorem lookupWithCost_time_le_of_isSome {α : Type u} {β : Type v}
    {hash : α → Nat} [DecidableEq α] (key : α) (table : HashTable α β hash)
    (present : (lookup key table).isSome) :
    (lookupWithCost key table).time ≤
      (table.buckets (selectedBucket table key)).entries.length := by
  apply lookupChainWithCost_time_le_of_mem
  exact List.dlookup_isSome.mp present

/-- Erasing an absent table key includes the selected chain's terminal event. -/
public theorem eraseWithCost_time_of_lookup_eq_none {α : Type u} {β : Type v}
    {hash : α → Nat} [DecidableEq α] (key : α) (table : HashTable α β hash)
    (absent : lookup key table = none) :
    (eraseWithCost key table).time =
      (table.buckets (selectedBucket table key)).entries.length + 1 := by
  rw [eraseWithCost_time_eq]
  exact lookupWithCost_time_of_lookup_eq_none key table absent

/-- Erasing a present table key stops within the selected chain. -/
public theorem eraseWithCost_time_le_of_isSome {α : Type u} {β : Type v}
    {hash : α → Nat} [DecidableEq α] (key : α) (table : HashTable α β hash)
    (present : (lookup key table).isSome) :
    (eraseWithCost key table).time ≤
      (table.buckets (selectedBucket table key)).entries.length := by
  rw [eraseWithCost_time_eq]
  exact lookupWithCost_time_le_of_isSome key table present

/-- The table returned by costed deletion is the ordinary deletion result. -/
public theorem eraseWithCost_result {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (table : HashTable α β hash) :
    (eraseWithCost key table).ret = erase key table := rfl

/-- The selected bucket is canonically erased; the bucket count is definitionally unchanged. -/
public theorem buckets_erase_selected {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (table : HashTable α β hash) :
    (erase key table).buckets (selectedBucket table key) =
      AList.erase key (table.buckets (selectedBucket table key)) := by
  change Function.update table.buckets (selectedBucket table key)
    (eraseBucketWithCost key (table.buckets (selectedBucket table key))).ret
    (selectedBucket table key) = _
  rw [Function.update_self, eraseBucketWithCost_result]

/-- Looking up a deleted key returns `none`. -/
public theorem lookup_erase {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (key : α) (table : HashTable α β hash) : lookup key (erase key table) = none := by
  simp only [erase, eraseWithCost]
  change AList.lookup key
    (Function.update table.buckets (selectedBucket table key)
      (eraseBucketWithCost key (table.buckets (selectedBucket table key))).ret
      (selectedBucket table key)) = none
  rw [Function.update_self, lookup_eraseBucketWithCost]
  simp

/-- Deleting one key leaves lookup of every distinct key unchanged, including collisions. -/
public theorem lookup_erase_of_ne {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key other : α) (table : HashTable α β hash)
    (different : other ≠ key) : lookup other (erase key table) = lookup other table := by
  simp only [erase, eraseWithCost]
  by_cases sameBucket : selectedBucket table other = selectedBucket table key
  · change AList.lookup other
      (Function.update table.buckets (selectedBucket table key)
        (eraseBucketWithCost key (table.buckets (selectedBucket table key))).ret
        (selectedBucket table other)) =
          AList.lookup other (table.buckets (selectedBucket table other))
    rw [sameBucket, Function.update_self, lookup_eraseBucketWithCost]
    simp [different]
  · change AList.lookup other
      (Function.update table.buckets (selectedBucket table key)
        (eraseBucketWithCost key (table.buckets (selectedBucket table key))).ret
        (selectedBucket table other)) =
          AList.lookup other (table.buckets (selectedBucket table other))
    rw [Function.update_of_ne sameBucket]

/-- Deletion preserves canonical bucket placement. -/
public theorem valid_erase {α : Type u} {β : Type v} {hash : α → Nat} [DecidableEq α]
    (key : α) (table : HashTable α β hash) (valid : Valid table) :
    Valid (erase key table) := by
  simp only [erase, eraseWithCost]
  change ∀ (index : Fin table.bucketCount) (other : α),
    (AList.lookup other
      (Function.update table.buckets (selectedBucket table key)
        (eraseBucketWithCost key (table.buckets (selectedBucket table key))).ret index)).isSome →
      selectedBucket table other = index
  intro index other present
  by_cases updated : index = selectedBucket table key
  · subst index
    rw [Function.update_self, lookup_eraseBucketWithCost] at present
    by_cases sameKey : other = key
    · simp [sameKey] at present
    · have oldPresent :
          (AList.lookup other (table.buckets (selectedBucket table key))).isSome := by
        simpa [sameKey] using present
      exact valid (selectedBucket table key) other oldPresent
  · have oldPresent : (AList.lookup other (table.buckets index)).isSome := by
      rw [Function.update_of_ne updated] at present
      exact present
    exact valid index other oldPresent

/-- Every bucket other than the hash-selected bucket is unchanged by deletion. -/
public theorem buckets_erase_of_ne {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (table : HashTable α β hash) (index : Fin table.bucketCount)
    (different : index ≠
      ⟨hash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩) :
    (erase key table).buckets index = table.buckets index := by
  simp only [erase, eraseWithCost]
  apply Function.update_of_ne
  simpa [selectedBucket] using different

/-- Abstracting deletion is finite-map deletion, provided bindings have valid bucket placement. -/
public theorem abstraction_erase {α : Type u} {β : Type v} {hash : α → Nat}
    [DecidableEq α] (key : α) (table : HashTable α β hash) (valid : Valid table) :
    abstraction (erase key table) = Finmap.erase key (abstraction table) := by
  apply Finmap.ext_lookup
  intro other
  rw [lookup_abstraction other (erase key table) (valid_erase key table valid)]
  by_cases same : other = key
  · subst other
    rw [lookup_erase, Finmap.lookup_erase]
  · rw [lookup_erase_of_ne key other table same]
    rw [Finmap.lookup_erase_ne same]
    exact (lookup_abstraction other table valid).symm

end Cslib.Algorithms.Lean.HashTable
