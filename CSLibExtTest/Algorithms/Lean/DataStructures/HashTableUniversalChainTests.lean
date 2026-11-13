/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.HashTable.UniversalChain

/-! Stored clients and adversarial checks for fixed-inventory universal chain bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cslib.Algorithms.Lean.HashTable

private theorem generic_bucket_client {α β : Type} [DecidableEq α] {hash : α → Nat}
    (table : HashTable α β hash) (valid : Valid table) {S : Finset α}
    (keys : (abstraction table).keys = S) (key : α) :
    (table.buckets (selectedBucket table key)).entries.length =
      (S.filter fun x => hash x % table.bucketCount = hash key % table.bucketCount).card :=
  chain_length_eq_card_filter table valid keys key

private theorem generic_absent_client {α β ι : Type} [DecidableEq α] {m : Nat}
    {s : Finset ι} {h : ι → α → Fin m} (hu : UniversalHashing.IsUniversalOn s h)
    (tables : (i : ι) → HashTable α β (fun x => (h i x).val))
    (valid : ∀ i ∈ s, Valid (tables i)) (count : ∀ i ∈ s, (tables i).bucketCount = m)
    {S : Finset α} (keys : ∀ i ∈ s, (abstraction (tables i)).keys = S)
    (key : α) (absent : key ∉ S) :
    (∑ i ∈ s, (lookupWithCost key (tables i)).time) * m ≤ s.card * (m + S.card) ∧
    (∑ i ∈ s, (eraseWithCost key (tables i)).time) * m ≤ s.card * (m + S.card) :=
  ⟨sum_lookupWithCost_time_mul_le_of_not_mem hu tables valid count keys key absent,
    sum_eraseWithCost_time_mul_le_of_not_mem hu tables valid count keys key absent⟩

private theorem generic_present_client {α β ι : Type} [DecidableEq α] {m : Nat}
    {s : Finset ι} {h : ι → α → Fin m} (hu : UniversalHashing.IsUniversalOn s h)
    (tables : (i : ι) → HashTable α β (fun x => (h i x).val))
    (valid : ∀ i ∈ s, Valid (tables i)) (count : ∀ i ∈ s, (tables i).bucketCount = m)
    {S : Finset α} (keys : ∀ i ∈ s, (abstraction (tables i)).keys = S)
    (key : α) (present : key ∈ S) :
    (∑ i ∈ s, (lookupWithCost key (tables i)).time) * m ≤ s.card * (m + (S.card - 1)) ∧
    (∑ i ∈ s, (eraseWithCost key (tables i)).time) * m ≤ s.card * (m + (S.card - 1)) :=
  ⟨sum_lookupWithCost_time_mul_le_of_mem hu tables valid count keys key present,
    sum_eraseWithCost_time_mul_le_of_mem hu tables valid count keys key present⟩

private theorem generic_build_client {α β : Type} [DecidableEq α] (hash : α → Nat)
    (m : Nat) (positive : 0 < m) (entries : List (α × β)) :
    Valid (buildTable hash m positive entries) ∧
    (buildTable hash m positive entries).bucketCount = m ∧
    (abstraction (buildTable hash m positive entries)).keys = (entries.map Prod.fst).toFinset :=
  ⟨valid_buildTable hash m positive entries, bucketCount_buildTable hash m positive entries,
    keys_buildTable hash m positive entries⟩

private def oneBucket : HashTable Nat Nat id := buildTable id 1 (by decide) [(0, 10), (1, 20)]

private theorem one_bucket_bridge :
    (oneBucket.buckets (selectedBucket oneBucket 9)).entries.length =
      (({0, 1} : Finset Nat).filter fun x => id x % oneBucket.bucketCount =
        id 9 % oneBucket.bucketCount).card := by
  apply chain_length_eq_card_filter oneBucket (valid_buildTable _ _ _ _)
  simp [oneBucket]

private theorem one_bucket_boundary :
    (lookupWithCost 9 oneBucket).time = 3 ∧ (lookupWithCost 0 oneBucket).time = 2 := by
  decide

private theorem singleton_construction :
    (lookupWithCost 1 (buildTable id 1 (by decide) [(1, (7 : Nat))])).time = 1 ∧
    (lookupWithCost 2 (buildTable id 1 (by decide) [(1, (7 : Nat))])).time = 2 := by
  decide

private theorem replacement_inventory :
    (abstraction (buildTable id 1 (by decide) [(1, (7 : Nat)), (1, 9)])).keys = {1} := by
  simp

private theorem replacement_value_and_time :
    (lookupWithCost 1 (buildTable id 1 (by decide) [(1, (7 : Nat)), (1, 9)])).ret = some 9 ∧
    (lookupWithCost 1 (buildTable id 1 (by decide) [(1, (7 : Nat)), (1, 9)])).time = 1 ∧
    (lookupWithCost 2 (buildTable id 1 (by decide) [(1, (7 : Nat)), (1, 9)])).time = 2 := by
  decide

/-! Each four-coordinate index is one function, not a quotient of repeated functions. -/

private abbrev HashIndex := Fin 2 × Fin 2 × Fin 2 × Fin 2

private def allHashes (i : HashIndex) (key : Fin 4) : Fin 2 :=
  if key = 0 then i.1 else if key = 1 then i.2.1 else if key = 2 then i.2.2.1 else i.2.2.2

private theorem allHashes_bijective : Function.Bijective allHashes := by
  constructor
  · intro i j same
    exact Prod.ext (congrFun same 0)
      (Prod.ext (congrFun same 1) (Prod.ext (congrFun same 2) (congrFun same 3)))
  · intro f
    refine ⟨(f 0, f 1, f 2, f 3), ?_⟩
    funext key
    fin_cases key <;> rfl

private theorem allHashes_universal : UniversalHashing.IsUniversalOn Finset.univ allHashes := by
  unfold UniversalHashing.IsUniversalOn
  decide

private theorem allHashes_card : (Finset.univ : Finset HashIndex).card = 16 := by decide

private theorem allHashes_nonvacuous :
    0 < (Finset.univ : Finset HashIndex).card ∧ 0 < (2 : Nat) := by decide

private def fixedEntries : List (Fin 4 × Nat) := [(0, 10), (1, 20)]

private def fixedTable (i : HashIndex) : HashTable (Fin 4) Nat (fun x => (allHashes i x).val) :=
  buildTable (fun x => (allHashes i x).val) 2 (by decide) fixedEntries

private theorem fixedTable_hypotheses (i : HashIndex) :
    Valid (fixedTable i) ∧ (fixedTable i).bucketCount = 2 ∧
    (abstraction (fixedTable i)).keys = {0, 1} := by
  refine ⟨valid_buildTable _ _ _ _, bucketCount_buildTable _ _ _ _, ?_⟩
  simp [fixedTable, fixedEntries]

private theorem fixed_queries_membership :
    (2 : Fin 4) ∉ ({0, 1} : Finset (Fin 4)) ∧ (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)) := by
  decide

private theorem fixed_absent_sum : (∑ i : HashIndex, (lookupWithCost 2 (fixedTable i)).time) = 32 := by
  decide

private theorem fixed_present_sum : (∑ i : HashIndex, (lookupWithCost 0 (fixedTable i)).time) = 24 := by
  decide

private theorem fixed_absent_sharp :
    (∑ i : HashIndex, (lookupWithCost 2 (fixedTable i)).time) * 2 =
      (Finset.univ : Finset HashIndex).card * (2 + ({0, 1} : Finset (Fin 4)).card) := by
  rw [fixed_absent_sum, allHashes_card]
  decide

private theorem fixed_present_sharp :
    (∑ i : HashIndex, (lookupWithCost 0 (fixedTable i)).time) * 2 =
      (Finset.univ : Finset HashIndex).card * (2 + (({0, 1} : Finset (Fin 4)).card - 1)) := by
  rw [fixed_present_sum, allHashes_card]
  decide

private theorem fixed_absent_bound :
    (∑ i : HashIndex, (lookupWithCost 2 (fixedTable i)).time) * 2 ≤ 64 := by
  simpa [fixedTable, fixedEntries] using
    sum_lookupWithCost_buildTable_time_mul_le_of_not_mem allHashes_universal fixedEntries 2
      (by decide)

private theorem fixed_present_bound :
    (∑ i : HashIndex, (lookupWithCost 0 (fixedTable i)).time) * 2 ≤ 48 := by
  simpa [fixedTable, fixedEntries] using
    sum_lookupWithCost_buildTable_time_mul_le_of_mem allHashes_universal fixedEntries 0 (by decide)

private theorem empty_inventory_boundary :
    (∑ i : HashIndex, (lookupWithCost 2
      (buildTable (β := Nat) (fun x => (allHashes i x).val) 2 (by decide) [])).time) = 16 := by
  decide

private theorem empty_inventory_bound :
    (∑ i : HashIndex, (lookupWithCost 2
      (buildTable (β := Nat) (fun x => (allHashes i x).val) 2 (by decide) [])).time) * 2 ≤ 32 := by
  simpa using sum_lookupWithCost_buildTable_time_mul_le_of_not_mem
    allHashes_universal ([] : List (Fin 4 × Nat)) 2 (by simp)

/-! Universality is necessary even when every table is structurally valid. -/

private def badHash (_i : Unit) (_key : Fin 4) : Fin 2 := 0

private def badEntries : List (Fin 4 × Nat) := [(0, 10), (1, 20), (2, 30)]

private theorem badHash_not_universal :
    ¬ UniversalHashing.IsUniversalOn (Finset.univ : Finset Unit) badHash := by
  unfold UniversalHashing.IsUniversalOn
  decide

private theorem badHash_structural_hypotheses (i : Unit) :
    Valid (buildTable (fun x => (badHash i x).val) 2 (by decide) badEntries) ∧
    (buildTable (fun x => (badHash i x).val) 2 (by decide) badEntries).bucketCount = 2 ∧
    (abstraction (buildTable (fun x => (badHash i x).val) 2 (by decide) badEntries)).keys =
      {0, 1, 2} := by
  refine ⟨valid_buildTable _ _ _ _, bucketCount_buildTable _ _ _ _, ?_⟩
  simp [badEntries]

private theorem badHash_absent_bound_fails :
    (∑ i : Unit, (lookupWithCost 3
      (buildTable (fun x => (badHash i x).val) 2 (by decide) badEntries)).time) * 2 >
      (Finset.univ : Finset Unit).card * (2 + ({0, 1, 2} : Finset (Fin 4)).card) := by
  decide

private theorem badHash_query_absent : (3 : Fin 4) ∉ ({0, 1, 2} : Finset (Fin 4)) := by decide

/-! Adapting only the absent query to the chosen function invalidates the bound. -/

private def adaptiveQuery (i : HashIndex) : Fin 4 :=
  if (({0, 1} : Finset (Fin 4)).filter fun x => allHashes i x = allHashes i 2).card <
      (({0, 1} : Finset (Fin 4)).filter fun x => allHashes i x = allHashes i 3).card
    then 3 else 2

private theorem adaptiveQuery_absent :
    ∀ i, adaptiveQuery i ∈ ({2, 3} : Finset (Fin 4)) ∧
      adaptiveQuery i ∉ ({0, 1} : Finset (Fin 4)) := by decide

private theorem adaptiveQuery_maximizes :
    ∀ (i : HashIndex) (key : Fin 4), key ∈ ({2, 3} : Finset (Fin 4)) →
      (lookupWithCost key (fixedTable i)).time ≤
        (lookupWithCost (adaptiveQuery i) (fixedTable i)).time := by decide

private theorem adaptiveQuery_structural_hypotheses (i : HashIndex) :
    Valid (fixedTable i) ∧ (fixedTable i).bucketCount = 2 ∧
    (abstraction (fixedTable i)).keys = {0, 1} ∧
    adaptiveQuery i ∉ (abstraction (fixedTable i)).keys := by
  obtain ⟨valid, count, keys⟩ := fixedTable_hypotheses i
  exact ⟨valid, count, keys, keys ▸ (adaptiveQuery_absent i).2⟩

private theorem adaptiveQuery_sum :
    (∑ i : HashIndex, (lookupWithCost (adaptiveQuery i) (fixedTable i)).time) = 36 := by decide

private theorem adaptiveQuery_bound_fails :
    (∑ i : HashIndex, (lookupWithCost (adaptiveQuery i) (fixedTable i)).time) * 2 >
      (Finset.univ : Finset HashIndex).card * (2 + ({0, 1} : Finset (Fin 4)).card) := by
  rw [adaptiveQuery_sum, allHashes_card]
  decide

/-! With query 3 fixed, prefer colliders among 0, 1, 2, then take exactly two keys. -/

private def adaptiveKeys (i : HashIndex) : List (Fin 4) :=
  (([0, 1, 2] : List (Fin 4)).filter (fun x => allHashes i x = allHashes i 3) ++
    ([0, 1, 2] : List (Fin 4)).filter (fun x => allHashes i x ≠ allHashes i 3)).take 2

private def adaptiveTable (i : HashIndex) : HashTable (Fin 4) Nat
    (fun x => (allHashes i x).val) :=
  buildTable (fun x => (allHashes i x).val) 2 (by decide)
    ((adaptiveKeys i).map fun x => (x, x.val))

private theorem adaptiveKeys_boundary :
    ∀ i, (adaptiveKeys i).Nodup ∧ (adaptiveKeys i).toFinset.card = 2 ∧
      (3 : Fin 4) ∉ (adaptiveKeys i).toFinset ∧
      (adaptiveKeys i).toFinset ⊆ ({0, 1, 2} : Finset (Fin 4)) := by decide

private theorem adaptiveTable_keys (i : HashIndex) :
    (abstraction (adaptiveTable i)).keys = (adaptiveKeys i).toFinset := by
  simp [adaptiveTable, List.map_map, Function.comp_def]

private theorem adaptiveInventory_structural_hypotheses (i : HashIndex) :
    Valid (adaptiveTable i) ∧ (adaptiveTable i).bucketCount = 2 ∧
    (abstraction (adaptiveTable i)).keys = (adaptiveKeys i).toFinset ∧
    (abstraction (adaptiveTable i)).keys.card = 2 ∧
    (3 : Fin 4) ∉ (abstraction (adaptiveTable i)).keys := by
  refine ⟨valid_buildTable _ _ _ _, bucketCount_buildTable _ _ _ _, adaptiveTable_keys i, ?_⟩
  rw [adaptiveTable_keys]
  exact ⟨(adaptiveKeys_boundary i).2.1, (adaptiveKeys_boundary i).2.2.1⟩

private theorem adaptiveInventory_sum :
    (∑ i : HashIndex, (lookupWithCost 3 (adaptiveTable i)).time) = 38 := by decide

private theorem adaptiveInventory_bound_fails :
    (∑ i : HashIndex, (lookupWithCost 3 (adaptiveTable i)).time) * 2 >
      (Finset.univ : Finset HashIndex).card * (2 + 2) := by
  rw [adaptiveInventory_sum, allHashes_card]
  decide

/-! Without Valid, the actual selected chain need not count the colliding abstract keys. -/

private def misplacedTable : HashTable Nat Nat id where
  bucketCount := 2
  bucketCount_pos := by decide
  buckets := fun index => if index = 1 then AList.singleton 0 7 else ∅

private theorem misplaced_inventory : (abstraction misplacedTable).keys = {0} := by decide

private theorem misplaced_invalid : ¬ Valid misplacedTable := by
  intro valid
  have wrong : (0 : Fin 2) = 1 := valid (1 : Fin 2) 0 (by decide)
  exact (by decide : (0 : Fin 2) ≠ 1) wrong

private theorem misplaced_bucket_bridge_fails :
    (misplacedTable.buckets (selectedBucket misplacedTable 1)).entries.length ≠
      (({0} : Finset Nat).filter fun x => id x % misplacedTable.bucketCount =
        id 1 % misplacedTable.bucketCount).card := by decide

/-! Mod-prime consumers build actual tables, with structural hypotheses discharged. -/

private theorem generic_modPrime_client {p m : Nat} [Fact p.Prime]
    (positive : 0 < m) (entries : List (ZMod p × Nat)) (key : ZMod p)
    (absent : key ∉ (entries.map Prod.fst).toFinset) :
    (∑ i : UniversalHashing.ModPrimeIndex p, (lookupWithCost key
      (buildTable (fun x => (UniversalHashing.modPrimeHashes p m positive i x).val)
        m positive entries)).time) * m ≤
      (p * (p - 1)) * (m + (entries.map Prod.fst).toFinset.card) :=
  sum_lookupWithCost_modPrime_time_mul_le_of_not_mem positive entries key absent

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def primeEntries : List (ZMod 3 × Nat) := [(0, 10), (1, 20)]

private def primeTable (i : UniversalHashing.ModPrimeIndex 3) : HashTable (ZMod 3) Nat
    (fun x => (UniversalHashing.modPrimeHashes 3 2 (by decide) i x).val) :=
  buildTable (fun x => (UniversalHashing.modPrimeHashes 3 2 (by decide) i x).val)
    2 (by decide) primeEntries

private theorem modPrime_absent_client :
    (∑ i : UniversalHashing.ModPrimeIndex 3, (lookupWithCost 2 (primeTable i)).time) * 2 ≤ 24 := by
  simpa [primeTable, primeEntries] using
    sum_lookupWithCost_modPrime_time_mul_le_of_not_mem (by decide : 0 < 2) primeEntries 2 (by decide)

private theorem modPrime_present_client :
    (∑ i : UniversalHashing.ModPrimeIndex 3, (lookupWithCost 0 (primeTable i)).time) * 2 ≤ 18 := by
  simpa [primeTable, primeEntries] using
    sum_lookupWithCost_modPrime_time_mul_le_of_mem (by decide : 0 < 2) primeEntries 0 (by decide)

private theorem modPrime_actual_sums :
    (∑ i : UniversalHashing.ModPrimeIndex 3, (lookupWithCost 2 (primeTable i)).time) = 10 ∧
    (∑ i : UniversalHashing.ModPrimeIndex 3, (lookupWithCost 0 (primeTable i)).time) = 8 := by decide

private theorem modPrime_one_bucket_multiplicity :
    (∑ i : UniversalHashing.ModPrimeIndex 3, (lookupWithCost 2
      (buildTable (fun x => (UniversalHashing.modPrimeHashes 3 1 (by decide) i x).val)
        1 (by decide) primeEntries)).time) = 18 := by decide

private theorem modPrime_one_bucket_bound :
    (∑ i : UniversalHashing.ModPrimeIndex 3, (lookupWithCost 2
      (buildTable (fun x => (UniversalHashing.modPrimeHashes 3 1 (by decide) i x).val)
        1 (by decide) primeEntries)).time) * 1 ≤ 18 := by
  simpa [primeEntries] using sum_lookupWithCost_modPrime_time_mul_le_of_not_mem
    (by decide : 0 < 1) primeEntries 2 (by decide)

end Cslib.Algorithms.Lean.HashTable
