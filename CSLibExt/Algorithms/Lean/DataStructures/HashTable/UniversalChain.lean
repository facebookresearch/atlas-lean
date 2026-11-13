/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.HashTable.EraseCost
public import CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing

/-!
# Universal hashing bounds for actual chain scans

The selected bucket of a valid table has exactly as many entries as there are colliding keys
in its finite-map inventory. Applying indexed universality to this equality bounds the event
counts of the existing `lookupWithCost` and `eraseWithCost` runs; no new scan is defined.

The inventory and query are fixed before the index is chosen. The finite-uniform average is
the sum over indices divided by their positive cardinality. Since `IsUniversalOn` supplies
both a nonempty index set and a positive bucket count, dividing the scaled inequalities by
these positive denominators gives averages at most `1 + |S| / m` for an absent query and
`1 + (|S| - 1) / m` for a present query. Repeated functions retain their index multiplicity.

These are scan events: an absent scan includes one terminal event, whereas a successful scan
stops at its successful comparison. Hash computation, modulus, bucket operations and equality
internals are unpriced. No machine-time bound or `1 + |S| / (2 * m)` bound is asserted.

`buildTable` uses canonical insertion in list order, including duplicate-key replacement.
The mod-prime corollaries discharge every structural hypothesis from this construction.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cslib.Algorithms.Lean

universe u v w

namespace UniversalHashing

variable {α : Type u} {ι : Type v} {m : Nat}
  {s : Finset ι} {h : ι → α → Fin m}

private theorem sum_card_collide_swap (S : Finset α) (k : α) :
    (∑ i ∈ s, (S.filter fun x => h i x = h i k).card) =
      ∑ x ∈ S, (s.filter fun i => h i x = h i k).card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- The sum of bucket collision counts for a fixed absent query, scaled by the range size. -/
public theorem sum_card_collide_mul_le_of_not_mem (hu : IsUniversalOn s h)
    (S : Finset α) (k : α) (hk : k ∉ S) :
    (∑ i ∈ s, (S.filter fun x => h i x = h i k).card) * m ≤ s.card * S.card := by
  rw [sum_card_collide_swap, Finset.sum_mul]
  calc
    (∑ x ∈ S, (s.filter fun i => h i x = h i k).card * m)
        ≤ ∑ _x ∈ S, s.card := by
          apply Finset.sum_le_sum
          intro x hx
          exact hu.2.2 x k (fun same => hk (same ▸ hx))
    _ = s.card * S.card := by simp [Nat.mul_comm]

/-- A fixed stored query contributes its self-collision once for each index. -/
public theorem sum_card_collide_mul_le_of_mem (hu : IsUniversalOn s h)
    (S : Finset α) (k : α) (hk : k ∈ S) :
    (∑ i ∈ s, (S.filter fun x => h i x = h i k).card) * m ≤
      s.card * (m + (S.card - 1)) := by
  classical
  have bound := sum_card_collide_mul_le_of_not_mem hu (S.erase k) k
    (Finset.notMem_erase k S)
  rw [sum_card_collide_swap] at bound ⊢
  rw [← Finset.sum_erase_add _ _ hk]
  simpa [Finset.card_erase_of_mem hk, Nat.add_mul, Nat.mul_add, Nat.add_comm] using
    Nat.add_le_add_right bound (s.card * m)

end UniversalHashing

namespace HashTable

variable {α : Type u} {β : Type v} [DecidableEq α]

private theorem mem_selectedBucket_keys {hash : α → Nat} (table : HashTable α β hash)
    (valid : Valid table) (key other : α) :
    other ∈ (table.buckets (selectedBucket table key)).keys ↔
      other ∈ (abstraction table).keys ∧
        hash other % table.bucketCount = hash key % table.bucketCount := by
  constructor
  · intro present
    have found := AList.lookup_isSome.mpr present
    have placed : selectedBucket table other = selectedBucket table key :=
      valid (selectedBucket table key) other found
    refine ⟨?_, congrArg Fin.val placed⟩
    rw [Finmap.mem_keys, ← Finmap.lookup_isSome, lookup_abstraction other table valid]
    change (AList.lookup other (table.buckets (selectedBucket table other))).isSome
    rwa [placed]
  · rintro ⟨present, collision⟩
    have placed : selectedBucket table other = selectedBucket table key := Fin.ext collision
    apply AList.lookup_isSome.mp
    rw [← placed, lookup_selectedBucket, ← lookup_abstraction other table valid,
      Finmap.lookup_isSome, ← Finmap.mem_keys]
    exact present

/-- The actual selected chain counts precisely the colliding keys in a valid fixed inventory. -/
public theorem chain_length_eq_card_filter {hash : α → Nat} (table : HashTable α β hash)
    (valid : Valid table) {S : Finset α} (keys : (abstraction table).keys = S) (key : α) :
    (table.buckets (selectedBucket table key)).entries.length =
      (S.filter fun x => hash x % table.bucketCount = hash key % table.bucketCount).card := by
  have inventory : (table.buckets (selectedBucket table key)).keys.toFinset =
      S.filter (fun x => hash x % table.bucketCount = hash key % table.bucketCount) := by
    ext other
    simp only [List.mem_toFinset, Finset.mem_filter, mem_selectedBucket_keys table valid, keys]
  rw [← inventory, List.toFinset_card_of_nodup (AList.keys_nodup _)]
  simp [AList.keys, List.keys]

private theorem chain_length_eq_card_filter_fin {m : Nat} (hash : α → Fin m)
    (table : HashTable α β (fun x => (hash x).val)) (valid : Valid table)
    (count : table.bucketCount = m) {S : Finset α} (keys : (abstraction table).keys = S)
    (key : α) :
    (table.buckets (selectedBucket table key)).entries.length =
      (S.filter fun x => hash x = hash key).card := by
  rw [chain_length_eq_card_filter table valid keys key]
  congr 1
  apply Finset.filter_congr
  intro x _
  simp [count, Nat.mod_eq_of_lt, Fin.ext_iff]

section Family

variable {ι : Type w} {m : Nat} {s : Finset ι} {h : ι → α → Fin m}
  (hu : UniversalHashing.IsUniversalOn s h)
  (tables : (i : ι) → HashTable α β (fun x => (h i x).val))
  (valid : ∀ i ∈ s, Valid (tables i)) (count : ∀ i ∈ s, (tables i).bucketCount = m)
  {S : Finset α} (keys : ∀ i ∈ s, (abstraction (tables i)).keys = S)

include hu valid count keys

/-- Uniform-index absent lookup costs at most one terminal event plus the load factor. -/
public theorem sum_lookupWithCost_time_mul_le_of_not_mem (key : α) (absent : key ∉ S) :
    (∑ i ∈ s, (lookupWithCost key (tables i)).time) * m ≤ s.card * (m + S.card) := by
  have bound : (∑ i ∈ s, (lookupWithCost key (tables i)).time) ≤
      ∑ i ∈ s, ((S.filter fun x => h i x = h i key).card + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    have run := lookupWithCost_cost_le key (tables i)
    rw [← chain_length_eq_card_filter_fin (h i) (tables i) (valid i hi) (count i hi)
      (keys i hi) key]
    exact run
  calc
    (∑ i ∈ s, (lookupWithCost key (tables i)).time) * m
        ≤ (∑ i ∈ s, ((S.filter fun x => h i x = h i key).card + 1)) * m :=
          Nat.mul_le_mul_right m bound
    _ = (∑ i ∈ s, (S.filter fun x => h i x = h i key).card) * m + s.card * m := by
      simp [Finset.sum_add_distrib, Nat.add_mul]
    _ ≤ s.card * S.card + s.card * m := Nat.add_le_add_right
      (UniversalHashing.sum_card_collide_mul_le_of_not_mem hu S key absent) _
    _ = s.card * (m + S.card) := by simp [Nat.mul_add, Nat.add_comm]

/-- A fixed present query costs at most its self-comparison plus the other keys' load factor. -/
public theorem sum_lookupWithCost_time_mul_le_of_mem (key : α) (present : key ∈ S) :
    (∑ i ∈ s, (lookupWithCost key (tables i)).time) * m ≤
      s.card * (m + (S.card - 1)) := by
  have bound : (∑ i ∈ s, (lookupWithCost key (tables i)).time) ≤
      ∑ i ∈ s, (S.filter fun x => h i x = h i key).card := by
    apply Finset.sum_le_sum
    intro i hi
    rw [← chain_length_eq_card_filter_fin (h i) (tables i) (valid i hi) (count i hi)
      (keys i hi) key]
    apply lookupWithCost_time_le_of_isSome
    rw [← lookup_abstraction key (tables i) (valid i hi), Finmap.lookup_isSome,
      ← Finmap.mem_keys, keys i hi]
    exact present
  exact (Nat.mul_le_mul_right m bound).trans
    (UniversalHashing.sum_card_collide_mul_le_of_mem hu S key present)

/-- Erasure inherits the absent-query average from the identical lookup scan events. -/
public theorem sum_eraseWithCost_time_mul_le_of_not_mem (key : α) (absent : key ∉ S) :
    (∑ i ∈ s, (eraseWithCost key (tables i)).time) * m ≤ s.card * (m + S.card) := by
  simp_rw [eraseWithCost_time_eq]
  exact sum_lookupWithCost_time_mul_le_of_not_mem hu tables valid count keys key absent

/-- Erasure inherits the present-query average from the identical lookup scan events. -/
public theorem sum_eraseWithCost_time_mul_le_of_mem (key : α) (present : key ∈ S) :
    (∑ i ∈ s, (eraseWithCost key (tables i)).time) * m ≤
      s.card * (m + (S.card - 1)) := by
  simp_rw [eraseWithCost_time_eq]
  exact sum_lookupWithCost_time_mul_le_of_mem hu tables valid count keys key present

end Family

/-- Inserts the list in order into an empty table; later duplicate keys replace earlier values. -/
public def buildTable (hash : α → Nat) (m : Nat) (positive : 0 < m)
    (entries : List (α × β)) : HashTable α β hash :=
  entries.foldl (fun table entry => insert entry.1 entry.2 table) (empty hash m positive)

/-- Building from no entries is the canonical empty table. -/
@[simp]
public theorem buildTable_nil (hash : α → Nat) (m : Nat) (positive : 0 < m) :
    buildTable (β := β) hash m positive [] = empty hash m positive := rfl

/-- Appending one binding to the input performs one canonical insertion, including replacement. -/
public theorem buildTable_append_singleton (hash : α → Nat) (m : Nat) (positive : 0 < m)
    (entries : List (α × β)) (entry : α × β) :
    buildTable hash m positive (entries ++ [entry]) =
      insert entry.1 entry.2 (buildTable hash m positive entries) := by
  simp [buildTable, List.foldl_append]

private theorem foldl_insert_valid {hash : α → Nat} (entries : List (α × β))
    (table : HashTable α β hash) (valid : Valid table) :
    Valid (entries.foldl (fun t entry => insert entry.1 entry.2 t) table) := by
  induction entries generalizing table with
  | nil => exact valid
  | cons entry rest ih => exact ih _ (valid_insert entry.1 entry.2 table valid)

/-- Tables constructed by insertion satisfy canonical bucket placement. -/
public theorem valid_buildTable (hash : α → Nat) (m : Nat) (positive : 0 < m)
    (entries : List (α × β)) : Valid (buildTable hash m positive entries) :=
  foldl_insert_valid entries _ (valid_empty hash m positive)

private theorem foldl_insert_bucketCount {hash : α → Nat} (entries : List (α × β))
    (table : HashTable α β hash) :
    (entries.foldl (fun t entry => insert entry.1 entry.2 t) table).bucketCount =
      table.bucketCount := by
  induction entries generalizing table with
  | nil => rfl
  | cons entry rest ih => exact ih (insert entry.1 entry.2 table)

/-- Construction never resizes the specified bucket array. -/
@[simp]
public theorem bucketCount_buildTable (hash : α → Nat) (m : Nat) (positive : 0 < m)
    (entries : List (α × β)) : (buildTable hash m positive entries).bucketCount = m :=
  foldl_insert_bucketCount entries _

private theorem foldl_insert_keys {hash : α → Nat} (entries : List (α × β))
    (table : HashTable α β hash) (valid : Valid table) :
    (abstraction (entries.foldl (fun t entry => insert entry.1 entry.2 t) table)).keys =
      (abstraction table).keys ∪ (entries.map Prod.fst).toFinset := by
  induction entries generalizing table with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.toFinset_cons]
      rw [ih _ (valid_insert entry.1 entry.2 table valid)]
      have inserted : (abstraction (insert entry.1 entry.2 table)).keys =
          Insert.insert entry.1 (abstraction table).keys := by
        rw [abstraction_insert entry.1 entry.2 table valid]
        ext key
        simp only [Finmap.mem_keys, Finmap.mem_insert, Finset.mem_insert]
      rw [inserted]
      simp only [Finset.insert_union, Finset.union_insert]

/-- The constructed inventory contains exactly the input keys, counting replacements only once. -/
@[simp]
public theorem keys_buildTable (hash : α → Nat) (m : Nat) (positive : 0 < m)
    (entries : List (α × β)) :
    (abstraction (buildTable hash m positive entries)).keys = (entries.map Prod.fst).toFinset := by
  simpa [buildTable] using foldl_insert_keys entries (empty hash m positive)
    (valid_empty hash m positive)

section BuiltFamily

variable {ι : Type w} {m : Nat} {s : Finset ι} {h : ι → α → Fin m}

/-- A fixed input list discharges every structural premise of the absent-query bound. -/
public theorem sum_lookupWithCost_buildTable_time_mul_le_of_not_mem
    (hu : UniversalHashing.IsUniversalOn s h) (entries : List (α × β))
    (key : α) (absent : key ∉ (entries.map Prod.fst).toFinset) :
    (∑ i ∈ s, (lookupWithCost key
      (buildTable (fun x => (h i x).val) m hu.1 entries)).time) * m ≤
      s.card * (m + (entries.map Prod.fst).toFinset.card) :=
  sum_lookupWithCost_time_mul_le_of_not_mem hu
    (fun i => buildTable (fun x => (h i x).val) m hu.1 entries)
    (fun _ _ => valid_buildTable _ _ _ _) (fun _ _ => bucketCount_buildTable _ _ _ _)
    (fun _ _ => keys_buildTable _ _ _ _) key absent

/-- A fixed input list discharges every structural premise of the present-query bound. -/
public theorem sum_lookupWithCost_buildTable_time_mul_le_of_mem
    (hu : UniversalHashing.IsUniversalOn s h) (entries : List (α × β))
    (key : α) (present : key ∈ (entries.map Prod.fst).toFinset) :
    (∑ i ∈ s, (lookupWithCost key
      (buildTable (fun x => (h i x).val) m hu.1 entries)).time) * m ≤
      s.card * (m + ((entries.map Prod.fst).toFinset.card - 1)) :=
  sum_lookupWithCost_time_mul_le_of_mem hu
    (fun i => buildTable (fun x => (h i x).val) m hu.1 entries)
    (fun _ _ => valid_buildTable _ _ _ _) (fun _ _ => bucketCount_buildTable _ _ _ _)
    (fun _ _ => keys_buildTable _ _ _ _) key present

end BuiltFamily

/-- The indexed mod-prime construction bounds absent scans of tables built from a fixed list. -/
public theorem sum_lookupWithCost_modPrime_time_mul_le_of_not_mem {p m : Nat} [Fact p.Prime]
    (positive : 0 < m) (entries : List (ZMod p × β)) (key : ZMod p)
    (absent : key ∉ (entries.map Prod.fst).toFinset) :
    (∑ i : UniversalHashing.ModPrimeIndex p, (lookupWithCost key
      (buildTable (fun x => (UniversalHashing.modPrimeHashes p m positive i x).val)
        m positive entries)).time) * m ≤
      (p * (p - 1)) * (m + (entries.map Prod.fst).toFinset.card) := by
  simpa only [Finset.card_univ, UniversalHashing.modPrimeIndex_card] using
    sum_lookupWithCost_buildTable_time_mul_le_of_not_mem
      (UniversalHashing.modPrime_isUniversalOn positive) entries key absent

/-- The indexed mod-prime construction bounds present scans of tables built from a fixed list. -/
public theorem sum_lookupWithCost_modPrime_time_mul_le_of_mem {p m : Nat} [Fact p.Prime]
    (positive : 0 < m) (entries : List (ZMod p × β)) (key : ZMod p)
    (present : key ∈ (entries.map Prod.fst).toFinset) :
    (∑ i : UniversalHashing.ModPrimeIndex p, (lookupWithCost key
      (buildTable (fun x => (UniversalHashing.modPrimeHashes p m positive i x).val)
        m positive entries)).time) * m ≤
      (p * (p - 1)) * (m + ((entries.map Prod.fst).toFinset.card - 1)) := by
  simpa only [Finset.card_univ, UniversalHashing.modPrimeIndex_card] using
    sum_lookupWithCost_buildTable_time_mul_le_of_mem
      (UniversalHashing.modPrime_isUniversalOn positive) entries key present

end HashTable

end Cslib.Algorithms.Lean
