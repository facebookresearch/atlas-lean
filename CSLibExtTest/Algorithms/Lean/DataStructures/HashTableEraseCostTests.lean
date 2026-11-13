/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.HashTable.EraseCost

/-!
# Stored consumers of hash-table erasure and scan-event bounds

The identity-hash, one/two-bucket and collision fixtures adapt PR #6201's HashTableTests
and HashTableRuntime (head `d5cebc9629a37d99e6e586b2ec398c9e63f169df`). Only erasure/scan
consumers are retained, as named private declarations. Additional consumers exercise canonical
list/bucket bridges, exact absent and sharp present bounds, dependent values, raw duplicate keys,
and the validity guard on the finite-map refinement. Counts include the absent terminal event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cslib.Algorithms.Lean.HashTableEraseCostTests

open HashTable

private def identityHash (key : Nat) : Nat := key

private def oneBucket : HashTable Nat String identityHash :=
  empty identityHash 1 (by decide)

private def twoBuckets : HashTable Nat String identityHash :=
  empty identityHash 2 (by decide)

private def collisionTable : HashTable Nat String identityHash :=
  insert 3 "three" (insert 1 "one" twoBuckets)

private def noncollisionTable : HashTable Nat String identityHash :=
  insert 1 "one" (insert 0 "zero" twoBuckets)

private def oneBucketCollisionTable : HashTable Nat String identityHash :=
  insert 2 "two" (insert 1 "one" oneBucket)

private theorem collisionTable_valid : Valid collisionTable := by
  exact valid_insert 3 "three" (insert 1 "one" twoBuckets)
    (valid_insert 1 "one" twoBuckets (valid_empty identityHash 2 (by decide)))

private theorem empty_lookup :
    (lookupWithCost 1 twoBuckets).ret = none ∧ (lookupWithCost 1 twoBuckets).time = 1 := by
  constructor <;> decide

private theorem empty_erase :
    lookup 1 (eraseWithCost 1 twoBuckets).ret = none ∧
      (eraseWithCost 1 twoBuckets).time = 1 := by
  constructor <;> decide

private theorem singleton_hit :
    (lookupWithCost 7 (insert 7 "seven" oneBucket)).ret = some "seven" ∧
      (lookupWithCost 7 (insert 7 "seven" oneBucket)).time = 1 := by
  constructor <;> decide

private theorem singleton_absent :
    (lookupWithCost 9 (insert 7 "seven" oneBucket)).ret = none ∧
      (lookupWithCost 9 (insert 7 "seven" oneBucket)).time = 2 := by
  constructor <;> decide

private theorem singleton_erase :
    lookup 7 (erase 7 (insert 7 "seven" oneBucket)) = none ∧
      (eraseWithCost 7 (insert 7 "seven" oneBucket)).time = 1 := by
  constructor <;> decide

private theorem collision_hit_head :
    (lookupWithCost 3 collisionTable).ret = some "three" ∧
      (lookupWithCost 3 collisionTable).time = 1 := by
  constructor <;> decide

private theorem collision_hit_tail :
    (lookupWithCost 1 collisionTable).ret = some "one" ∧
      (lookupWithCost 1 collisionTable).time = 2 := by
  constructor <;> decide

private theorem collision_absent :
    (lookupWithCost 5 collisionTable).ret = none ∧
      (lookupWithCost 5 collisionTable).time = 3 := by
  constructor <;> decide

private theorem replacement_scan :
    (lookupWithCost 3 (insert 3 "new" collisionTable)).ret = some "new" ∧
      (lookupWithCost 3 (insert 3 "new" collisionTable)).time = 1 := by
  constructor <;> decide

private theorem erase_head :
    lookup 3 (eraseWithCost 3 collisionTable).ret = none ∧
      (eraseWithCost 3 collisionTable).time = 1 := by
  constructor <;> decide

private theorem erase_tail :
    lookup 1 (eraseWithCost 1 collisionTable).ret = none ∧
      (eraseWithCost 1 collisionTable).time = 2 := by
  constructor <;> decide

private theorem erase_head_preserves_tail :
    lookup 1 (erase 3 collisionTable) = some "one" := by decide

private theorem erase_tail_preserves_head :
    lookup 3 (erase 1 collisionTable) = some "three" := by decide

private theorem erase_absent_time : (eraseWithCost 5 collisionTable).time = 3 := by decide

private theorem erase_absent_preserves_bucket :
    (erase 5 collisionTable).buckets (1 : Fin 2) = collisionTable.buckets (1 : Fin 2) := by
  apply AList.ext
  decide

private theorem erase_middle :
    (eraseWithCost 3 (insert 5 "five" collisionTable)).time = 2 ∧
      ((erase 3 (insert 5 "five" collisionTable)).buckets (1 : Fin 2)).entries =
        [⟨5, "five"⟩, ⟨1, "one"⟩] := by
  constructor <;> decide

private theorem repeated_erase_absent :
    lookup 2 (erase 2 (erase 2 oneBucketCollisionTable)) = none := by decide

private theorem repeated_erase_preserves_other :
    lookup 1 (erase 2 (erase 2 oneBucketCollisionTable)) = some "one" := by decide

private theorem repeated_erase_time :
    (eraseWithCost 2 (erase 2 oneBucketCollisionTable)).time = 2 := by decide

private theorem erase_preserves_other_bucket_lookup :
    lookup 0 (erase 1 noncollisionTable) = some "zero" := by decide

private theorem erase_preserves_other_bucket :
    (erase 1 noncollisionTable).buckets (0 : Fin 2) =
      noncollisionTable.buckets (0 : Fin 2) := by
  exact buckets_erase_of_ne 1 noncollisionTable (0 : Fin 2)
    (by change (0 : Fin 2) ≠ 1; decide)

private theorem collision_abstraction_erase :
    abstraction (erase 3 collisionTable) = Finmap.erase 3 (abstraction collisionTable) := by
  exact abstraction_erase 3 collisionTable collisionTable_valid

private def dependentEntries : List (Sigma fun n : Nat => Fin (n + 1)) :=
  [⟨1, ⟨1, by decide⟩⟩, ⟨2, ⟨2, by decide⟩⟩]

private def dependentBucket : AList (fun n : Nat => Fin (n + 1)) :=
  ⟨dependentEntries, by
    change ([1, 2] : List Nat).Nodup
    decide⟩

private theorem dependent_lookup_tail :
    (lookupChainWithCost 2 dependentEntries).ret = some (2 : Fin 3) ∧
      (lookupChainWithCost 2 dependentEntries).time = 2 := by
  constructor <;> decide

private theorem dependent_erase_head :
    (eraseChainWithCost 1 dependentEntries).ret = [⟨2, (2 : Fin 3)⟩] ∧
      (eraseChainWithCost 1 dependentEntries).time = 1 := by
  constructor <;> decide

private theorem dependent_erase_tail :
    (eraseChainWithCost 2 dependentEntries).ret = [⟨1, (1 : Fin 2)⟩] ∧
      (eraseChainWithCost 2 dependentEntries).time = 2 := by
  constructor <;> decide

private theorem dependent_bucket_preserves_other :
    AList.lookup 2 (eraseBucketWithCost 1 dependentBucket).ret = some (2 : Fin 3) := by
  decide

private theorem dependent_bucket_canonical :
    (eraseBucketWithCost 1 dependentBucket).ret = AList.erase 1 dependentBucket := by
  exact eraseBucketWithCost_result 1 dependentBucket

private def duplicateEntries : List (Sigma fun _ : Nat => String) :=
  [⟨1, "a"⟩, ⟨1, "b"⟩]

private theorem duplicate_survives_first_erase :
    List.dlookup 1 (eraseChainWithCost 1 duplicateEntries).ret = some "b" := by decide

private theorem duplicate_not_nodup : ¬ duplicateEntries.NodupKeys := by
  change ¬ ([1, 1] : List Nat).Nodup
  decide

/-- Each bucket is an AList, but key 1 is also incorrectly stored in bucket 0. -/
private def misplacedTable : HashTable Nat String identityHash where
  bucketCount := 2
  bucketCount_pos := by decide
  buckets := fun _ => AList.singleton 1 "stray"

private theorem misplaced_not_valid : ¬ Valid misplacedTable := by
  intro valid
  have wrong := valid (0 : Fin 2) 1 (by decide)
  change (1 : Fin 2) = 0 at wrong
  exact (by decide : (1 : Fin 2) ≠ 0) wrong

private theorem misplaced_erase_lookup_absent : lookup 1 (erase 1 misplacedTable) = none := by
  exact lookup_erase 1 misplacedTable

private theorem misplaced_abstraction_retains_key :
    Finmap.lookup 1 (abstraction (erase 1 misplacedTable)) = some "stray" := by
  rw [abstraction, Finmap.dlookup_list_toFinmap]
  decide

private theorem misplaced_refinement_fails :
    abstraction (erase 1 misplacedTable) ≠ Finmap.erase 1 (abstraction misplacedTable) := by
  intro equality
  have observed := congrArg (Finmap.lookup 1) equality
  simp only [misplaced_abstraction_retains_key, Finmap.lookup_erase, reduceCtorEq] at observed

section Generic

universe u v

variable {α : Type u} {β : α → Type v} [DecidableEq α]

private theorem chain_lookup_result (key : α) (entries : List (Sigma β)) :
    (lookupChainWithCost key entries).ret = List.dlookup key entries := by
  exact lookupChainWithCost_result key entries

private theorem chain_erase_canonical (key : α) (entries : List (Sigma β)) :
    (eraseChainWithCost key entries).ret = List.kerase key entries := by
  exact eraseChainWithCost_result key entries

private theorem chain_erase_nodup (key : α) (entries : List (Sigma β))
    (nodup : entries.NodupKeys) : (eraseChainWithCost key entries).ret.NodupKeys := by
  rw [eraseChainWithCost_result]
  exact List.NodupKeys.kerase key nodup

private theorem chain_erase_absence (key : α) (entries : List (Sigma β))
    (nodup : entries.NodupKeys) : List.dlookup key (eraseChainWithCost key entries).ret = none := by
  rw [eraseChainWithCost_result]
  exact List.dlookup_kerase key nodup

private theorem chain_absent_exact (key : α) (entries : List (Sigma β))
    (absent : key ∉ entries.keys) :
    (lookupChainWithCost key entries).time = entries.length + 1 := by
  exact lookupChainWithCost_time_of_not_mem key entries absent

private theorem chain_present_bound (key : α) (entries : List (Sigma β))
    (present : key ∈ entries.keys) : (lookupChainWithCost key entries).time ≤ entries.length := by
  exact lookupChainWithCost_time_le_of_mem key entries present

private theorem chain_erase_absent_exact (key : α) (entries : List (Sigma β))
    (absent : key ∉ entries.keys) : (eraseChainWithCost key entries).time = entries.length + 1 := by
  exact eraseChainWithCost_time_of_not_mem key entries absent

private theorem chain_erase_present_bound (key : α) (entries : List (Sigma β))
    (present : key ∈ entries.keys) : (eraseChainWithCost key entries).time ≤ entries.length := by
  exact eraseChainWithCost_time_le_of_mem key entries present

private theorem bucket_erase_canonical (key : α) (bucket : AList β) :
    (eraseBucketWithCost key bucket).ret = AList.erase key bucket := by
  exact eraseBucketWithCost_result key bucket

private theorem bucket_erase_lookup (key : α) (bucket : AList β) :
    AList.lookup key (eraseBucketWithCost key bucket).ret = none := by
  rw [lookup_eraseBucketWithCost]
  simp

private theorem bucket_erase_bound (key : α) (bucket : AList β) :
    (eraseBucketWithCost key bucket).time ≤ bucket.entries.length + 1 := by
  exact eraseBucketWithCost_cost_le key bucket

private theorem bucket_erase_scan_time (key : α) (bucket : AList β) :
    (eraseBucketWithCost key bucket).time = (lookupChainWithCost key bucket.entries).time := by
  exact eraseBucketWithCost_time_eq key bucket

variable {γ : Type v} {hash : α → Nat}

omit [DecidableEq α] in
private theorem selectedBucket_literal (key : α) (table : HashTable α γ hash) :
    selectedBucket table key =
      ⟨hash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩ := rfl

private theorem selected_lookup (key : α) (table : HashTable α γ hash) :
    AList.lookup key (table.buckets (selectedBucket table key)) = lookup key table := by
  exact lookup_selectedBucket key table

private theorem table_lookup_result (key : α) (table : HashTable α γ hash) :
    (lookupWithCost key table).ret = lookup key table := by
  exact lookupWithCost_result key table

private theorem table_erase_result (key : α) (table : HashTable α γ hash) :
    (eraseWithCost key table).ret = erase key table := by
  exact eraseWithCost_result key table

private theorem table_erase_bucket_count (key : α) (table : HashTable α γ hash) :
    (erase key table).bucketCount = table.bucketCount := rfl

private theorem table_selected_erase (key : α) (table : HashTable α γ hash) :
    (erase key table).buckets (selectedBucket table key) =
      AList.erase key (table.buckets (selectedBucket table key)) := by
  exact buckets_erase_selected key table

private theorem table_valid_erase (key : α) (table : HashTable α γ hash) (valid : Valid table) :
    Valid (erase key table) := by
  exact valid_erase key table valid

private theorem table_abstraction_erase (key : α) (table : HashTable α γ hash)
    (valid : Valid table) :
    abstraction (erase key table) = Finmap.erase key (abstraction table) := by
  exact abstraction_erase key table valid

private theorem table_lookup_bound (key : α) (table : HashTable α γ hash) :
    (lookupWithCost key table).time ≤
      (table.buckets (selectedBucket table key)).entries.length + 1 := by
  exact lookupWithCost_cost_le key table

private theorem table_erase_bound (key : α) (table : HashTable α γ hash) :
    (eraseWithCost key table).time ≤
      (table.buckets (selectedBucket table key)).entries.length + 1 := by
  exact eraseWithCost_cost_le key table

private theorem table_absent_exact (key : α) (table : HashTable α γ hash)
    (absent : lookup key table = none) :
    (lookupWithCost key table).time =
      (table.buckets (selectedBucket table key)).entries.length + 1 := by
  exact lookupWithCost_time_of_lookup_eq_none key table absent

private theorem table_present_bound (key : α) (table : HashTable α γ hash)
    (present : (lookup key table).isSome) :
    (lookupWithCost key table).time ≤
      (table.buckets (selectedBucket table key)).entries.length := by
  exact lookupWithCost_time_le_of_isSome key table present

private theorem table_erase_absent_exact (key : α) (table : HashTable α γ hash)
    (absent : lookup key table = none) :
    (eraseWithCost key table).time =
      (table.buckets (selectedBucket table key)).entries.length + 1 := by
  exact eraseWithCost_time_of_lookup_eq_none key table absent

private theorem table_erase_present_bound (key : α) (table : HashTable α γ hash)
    (present : (lookup key table).isSome) :
    (eraseWithCost key table).time ≤ (table.buckets (selectedBucket table key)).entries.length := by
  exact eraseWithCost_time_le_of_isSome key table present

end Generic

end Cslib.Algorithms.Lean.HashTableEraseCostTests
