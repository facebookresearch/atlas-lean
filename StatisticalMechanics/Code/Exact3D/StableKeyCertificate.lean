/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.PolymerEnumeration










namespace StatMech
namespace Exact3D
namespace BoundedPolymerCase




structure StableKeyRecord where
  support : List (List ℤ)
  degree : ℕ
  range : ℕ
deriving DecidableEq, Repr

namespace StableKeyRecord


def toKey {maxDegree maxRange : ℕ} (r : StableKeyRecord)
    (hdegree : r.degree ≤ maxDegree) (hrange : r.range ≤ maxRange) :
    StableKey maxDegree maxRange :=
  toLex (r.support,
    toLex (⟨r.degree, Nat.lt_succ_of_le hdegree⟩,
      ⟨r.range, Nat.lt_succ_of_le hrange⟩))


def ofKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) : StableKeyRecord :=
  let p := ofLex k
  let q := ofLex p.2
  { support := p.1
    degree := q.1.1
    range := q.2.1 }

theorem ofKey_degree_le {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    (ofKey k).degree ≤ maxDegree := by
  dsimp [ofKey]
  exact Nat.le_of_lt_succ (ofLex (ofLex k).2).1.2

theorem ofKey_range_le {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    (ofKey k).range ≤ maxRange := by
  dsimp [ofKey]
  exact Nat.le_of_lt_succ (ofLex (ofLex k).2).2.2

@[simp] theorem ofKey_stableKey_support {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    (ofKey (stableKey c)).support = supportKey c.support := by
  simp [ofKey, stableKey]

@[simp] theorem ofKey_stableKey_degree {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    (ofKey (stableKey c)).degree = c.degree := by
  simp [ofKey, stableKey]

@[simp] theorem ofKey_stableKey_range {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    (ofKey (stableKey c)).range = c.range := by
  simp [ofKey, stableKey]

@[simp] theorem toKey_ofKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    (ofKey k).toKey (ofKey_degree_le k) (ofKey_range_le k) = k := by
  simp [toKey, ofKey]

@[simp] theorem ofKey_toKey {maxDegree maxRange : ℕ} (r : StableKeyRecord)
    (hdegree : r.degree ≤ maxDegree) (hrange : r.range ≤ maxRange) :
    ofKey (r.toKey hdegree hrange) = r := by
  cases r
  simp [toKey, ofKey]

end StableKeyRecord



structure ValidStableKeyRecord (maxDegree maxRange : ℕ) where
  record : StableKeyRecord
  degree_le : record.degree ≤ maxDegree
  range_le : record.range ≤ maxRange

namespace ValidStableKeyRecord


def toKey {maxDegree maxRange : ℕ}
    (r : ValidStableKeyRecord maxDegree maxRange) : StableKey maxDegree maxRange :=
  r.record.toKey r.degree_le r.range_le


def ofKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    ValidStableKeyRecord maxDegree maxRange where
  record := StableKeyRecord.ofKey k
  degree_le := StableKeyRecord.ofKey_degree_le k
  range_le := StableKeyRecord.ofKey_range_le k

@[simp] theorem toKey_mk {maxDegree maxRange : ℕ}
    (record : StableKeyRecord) (degree_le : record.degree ≤ maxDegree)
    (range_le : record.range ≤ maxRange) :
    toKey (ValidStableKeyRecord.mk record degree_le range_le) =
      record.toKey degree_le range_le :=
  rfl

@[simp] theorem toKey_ofKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    (ofKey k).toKey = k := by
  simp [ofKey, toKey]

end ValidStableKeyRecord


def validRecordKeyList {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange)) :
    List (StableKey maxDegree maxRange) :=
  records.map ValidStableKeyRecord.toKey


def validRecordKeyFinset {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange)) :
    Finset (StableKey maxDegree maxRange) :=
  (validRecordKeyList records).toFinset

@[simp] theorem validRecordKeyFinset_nil {maxDegree maxRange : ℕ} :
    validRecordKeyFinset
      ([] : List (ValidStableKeyRecord maxDegree maxRange)) = ∅ := by
  classical
  ext k
  simp [validRecordKeyFinset, validRecordKeyList]

@[simp] theorem mem_validRecordKeyFinset_cons {maxDegree maxRange : ℕ}
    (record : ValidStableKeyRecord maxDegree maxRange)
    (records : List (ValidStableKeyRecord maxDegree maxRange))
    (k : StableKey maxDegree maxRange) :
    k ∈ validRecordKeyFinset (record :: records) ↔
      record.toKey = k ∨ k ∈ validRecordKeyFinset records := by
  classical
  constructor
  · intro hk
    have hk' : k = record.toKey ∨ k ∈ validRecordKeyFinset records := by
      simpa [validRecordKeyFinset, validRecordKeyList] using hk
    rcases hk' with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · intro hk
    have hk' : k = record.toKey ∨ k ∈ validRecordKeyFinset records := by
      rcases hk with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    simpa [validRecordKeyFinset, validRecordKeyList] using hk'



noncomputable def externalStableKeyIntervalTable {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    RatInterval.CaseTable (StableKey maxDegree maxRange) where
  cases := validRecordKeyFinset records
  interval := intervalOf

@[simp] theorem externalStableKeyIntervalTable_cases {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    (externalStableKeyIntervalTable records intervalOf).cases =
      validRecordKeyFinset records :=
  rfl

@[simp] theorem externalStableKeyIntervalTable_interval
    {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    (externalStableKeyIntervalTable records intervalOf).interval k =
      intervalOf k :=
  rfl




theorem externalStableKeyIntervalTable_covers_and_sound_of_keyValue
    {α : Type*} {maxDegree maxRange : ℕ}
    (records : List (ValidStableKeyRecord maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (classifier : α → StableKey maxDegree maxRange)
    (value : α → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hcover : ∀ a, classifier a ∈ validRecordKeyFinset records)
    (hvalue : ∀ a, value a = keyValue (classifier a))
    (hkey : ∀ k, k ∈ validRecordKeyFinset records →
      (intervalOf k).MemR (keyValue k)) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalTable records intervalOf) classifier ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalTable records intervalOf) classifier value := by
  constructor
  · intro a
    exact hcover a
  · intro a
    rw [hvalue a]
    exact hkey (classifier a) (hcover a)



structure StableKeyIntervalRow (maxDegree maxRange : ℕ) where
  key : ValidStableKeyRecord maxDegree maxRange
  interval : RatInterval


def stableKeyIntervalRowRecords {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange)) :
    List (ValidStableKeyRecord maxDegree maxRange) :=
  rows.map StableKeyIntervalRow.key


def stableKeyIntervalRowKeyFinset {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange)) :
    Finset (StableKey maxDegree maxRange) :=
  validRecordKeyFinset (stableKeyIntervalRowRecords rows)

@[simp] theorem mem_stableKeyIntervalRowKeyFinset {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset rows ↔
      ∃ row, row ∈ rows ∧ row.key.toKey = k := by
  classical
  simp [stableKeyIntervalRowKeyFinset, stableKeyIntervalRowRecords,
    validRecordKeyFinset, validRecordKeyList]

namespace StableKeyIntervalRow



def ofKeyInterval {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    StableKeyIntervalRow maxDegree maxRange where
  key := ValidStableKeyRecord.ofKey k
  interval := intervalOf k


def ofKey {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    StableKeyIntervalRow maxDegree maxRange :=
  ofKeyInterval intervalOf k

@[simp] theorem ofKeyInterval_key_toKey {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    (ofKeyInterval intervalOf k).key.toKey = k := by
  simp [ofKeyInterval]

@[simp] theorem ofKeyInterval_interval {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    (ofKeyInterval intervalOf k).interval = intervalOf k :=
  rfl

@[simp] theorem ofKey_key_toKey {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    (ofKey intervalOf k).key.toKey = k := by
  simp [ofKey]

@[simp] theorem ofKey_interval {maxDegree maxRange : ℕ}
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    (ofKey intervalOf k).interval = intervalOf k :=
  rfl


noncomputable def rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    List (StableKeyIntervalRow maxDegree maxRange) :=
  s.toList.map (ofKey intervalOf)



theorem mem_keyFinset_map_ofKeyInterval {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset
        (s.toList.map (ofKeyInterval intervalOf)) ↔
      k ∈ s := by
  classical
  simp [stableKeyIntervalRowKeyFinset, stableKeyIntervalRowRecords,
    validRecordKeyFinset, validRecordKeyList, ofKeyInterval]

@[simp] theorem mem_keyFinset_rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset (rowsOfKeys s intervalOf) ↔
      k ∈ s := by
  simpa [rowsOfKeys, ofKey] using
    mem_keyFinset_map_ofKeyInterval s intervalOf k


theorem interval_eq_of_mem_map_ofKeyInterval {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ s.toList.map (ofKeyInterval intervalOf)) :
    row.interval = intervalOf row.key.toKey := by
  rcases List.mem_map.mp hrow with ⟨k, _hk, rfl⟩
  simp [ofKeyInterval]


theorem interval_eq_of_mem_rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ rowsOfKeys s intervalOf) :
    row.interval = intervalOf row.key.toKey := by
  exact interval_eq_of_mem_map_ofKeyInterval s intervalOf
    (by simpa [rowsOfKeys, ofKey] using hrow)



theorem memR_of_mem_map_ofKeyInterval {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hmem :
      ∀ k, k ∈ s → (intervalOf k).MemR (keyValue k))
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ s.toList.map (ofKeyInterval intervalOf)) :
    row.interval.MemR (keyValue row.key.toKey) := by
  classical
  rcases List.mem_map.mp hrow with ⟨k, hk, rfl⟩
  simpa [ofKeyInterval] using hmem k (by simpa using hk)



theorem memR_of_mem_rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hmem :
      ∀ k, k ∈ s → (intervalOf k).MemR (keyValue k))
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ rowsOfKeys s intervalOf) :
    row.interval.MemR (keyValue row.key.toKey) :=
  memR_of_mem_map_ofKeyInterval s intervalOf keyValue hmem
    (by simpa [rowsOfKeys, ofKey] using hrow)



theorem upper_le_of_mem_map_ofKeyInterval {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    {bound : ℝ}
    (hupper :
      ∀ k, k ∈ s → (((intervalOf k).upper : ℚ) : ℝ) ≤ bound)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ s.toList.map (ofKeyInterval intervalOf)) :
    ((row.interval.upper : ℚ) : ℝ) ≤ bound := by
  classical
  rcases List.mem_map.mp hrow with ⟨k, hk, rfl⟩
  simpa [ofKeyInterval] using hupper k (by simpa using hk)



theorem upper_le_of_mem_rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval)
    {bound : ℝ}
    (hupper :
      ∀ k, k ∈ s → (((intervalOf k).upper : ℚ) : ℝ) ≤ bound)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ rowsOfKeys s intervalOf) :
    ((row.interval.upper : ℚ) : ℝ) ≤ bound :=
  upper_le_of_mem_map_ofKeyInterval s intervalOf hupper
    (by simpa [rowsOfKeys, ofKey] using hrow)




def ExactKeySet {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (expected : Finset (StableKey maxDegree maxRange)) : Prop :=
  stableKeyIntervalRowKeyFinset rows = expected



theorem exactKeySet_map_ofKeyInterval {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    ExactKeySet (s.toList.map (ofKeyInterval intervalOf)) s := by
  classical
  ext k
  exact mem_keyFinset_map_ofKeyInterval s intervalOf k



theorem exactKeySet_rowsOfKeys {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (intervalOf : StableKey maxDegree maxRange → RatInterval) :
    ExactKeySet (rowsOfKeys s intervalOf) s := by
  classical
  ext k
  exact mem_keyFinset_rowsOfKeys s intervalOf k

theorem exactKeySet_iff {maxDegree maxRange : ℕ}
    {rows : List (StableKeyIntervalRow maxDegree maxRange)}
    {expected : Finset (StableKey maxDegree maxRange)} :
    ExactKeySet rows expected ↔
      ∀ k, k ∈ stableKeyIntervalRowKeyFinset rows ↔ k ∈ expected := by
  classical
  constructor
  · intro h k
    change stableKeyIntervalRowKeyFinset rows = expected at h
    rw [h]
  · intro h
    ext k
    exact h k


theorem mem_expected_of_exactKeySet {maxDegree maxRange : ℕ}
    {rows : List (StableKeyIntervalRow maxDegree maxRange)}
    {expected : Finset (StableKey maxDegree maxRange)}
    (h : ExactKeySet rows expected)
    {k : StableKey maxDegree maxRange}
    (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
    k ∈ expected := by
  change stableKeyIntervalRowKeyFinset rows = expected at h
  rwa [h] at hk


theorem mem_rows_of_exactKeySet {maxDegree maxRange : ℕ}
    {rows : List (StableKeyIntervalRow maxDegree maxRange)}
    {expected : Finset (StableKey maxDegree maxRange)}
    (h : ExactKeySet rows expected)
    {k : StableKey maxDegree maxRange}
    (hk : k ∈ expected) :
    k ∈ stableKeyIntervalRowKeyFinset rows := by
  change stableKeyIntervalRowKeyFinset rows = expected at h
  rw [h]
  exact hk


theorem row_key_mem_expected_of_exactKeySet {maxDegree maxRange : ℕ}
    {rows : List (StableKeyIntervalRow maxDegree maxRange)}
    {expected : Finset (StableKey maxDegree maxRange)}
    (h : ExactKeySet rows expected)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ rows) :
    row.key.toKey ∈ expected := by
  exact mem_expected_of_exactKeySet h
    ((mem_stableKeyIntervalRowKeyFinset rows row.key.toKey).2
      ⟨row, hrow, rfl⟩)



theorem classifier_mem_rows_of_exactKeySet {α : Type*}
    {maxDegree maxRange : ℕ}
    {rows : List (StableKeyIntervalRow maxDegree maxRange)}
    {expected : Finset (StableKey maxDegree maxRange)}
    (h : ExactKeySet rows expected)
    (classifier : α → StableKey maxDegree maxRange)
    (hclassifier : ∀ a, classifier a ∈ expected)
    (a : α) :
    classifier a ∈ stableKeyIntervalRowKeyFinset rows :=
  mem_rows_of_exactKeySet h (hclassifier a)

end StableKeyIntervalRow

@[simp] theorem stableKeyIntervalRowKeyFinset_nil {maxDegree maxRange : ℕ} :
    stableKeyIntervalRowKeyFinset
      ([] : List (StableKeyIntervalRow maxDegree maxRange)) = ∅ := by
  classical
  ext k
  simp

@[simp] theorem mem_stableKeyIntervalRowKeyFinset_cons
    {maxDegree maxRange : ℕ}
    (row : StableKeyIntervalRow maxDegree maxRange)
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset (row :: rows) ↔
      row.key.toKey = k ∨ k ∈ stableKeyIntervalRowKeyFinset rows := by
  classical
  simp




noncomputable def intervalOfRows {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) (k : StableKey maxDegree maxRange) : RatInterval :=
  if h : ∃ row, row ∈ rows ∧ row.key.toKey = k then
    h.choose.interval
  else
    fallback

theorem intervalOfRows_eq_fallback_of_not_mem_keyFinset
    {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) {k : StableKey maxDegree maxRange}
    (hk : k ∉ stableKeyIntervalRowKeyFinset rows) :
    intervalOfRows rows fallback k = fallback := by
  classical
  rw [intervalOfRows, dif_neg]
  intro hex
  exact hk ((mem_stableKeyIntervalRowKeyFinset rows k).2 hex)

theorem exists_row_intervalOfRows_eq_of_mem_keyFinset
    {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) {k : StableKey maxDegree maxRange}
    (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
    ∃ row, row ∈ rows ∧ row.key.toKey = k ∧
      intervalOfRows rows fallback k = row.interval := by
  classical
  have hex : ∃ row, row ∈ rows ∧ row.key.toKey = k :=
    (mem_stableKeyIntervalRowKeyFinset rows k).mp hk
  refine ⟨Classical.choose hex, ?_, ?_, ?_⟩
  · exact (Classical.choose_spec hex).1
  · exact (Classical.choose_spec hex).2
  · rw [intervalOfRows, dif_pos hex]

theorem intervalOfRows_memR_of_mem_keyFinset {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) (keyValue : StableKey maxDegree maxRange → ℝ)
    (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey))
    {k : StableKey maxDegree maxRange}
    (hk : k ∈ stableKeyIntervalRowKeyFinset rows) :
    (intervalOfRows rows fallback k).MemR (keyValue k) := by
  classical
  have hex : ∃ row, row ∈ rows ∧ row.key.toKey = k :=
    (mem_stableKeyIntervalRowKeyFinset rows k).mp hk
  rw [intervalOfRows, dif_pos hex]
  have hspec := Classical.choose_spec hex
  simpa [hspec.2] using hrow (Classical.choose hex) hspec.1



noncomputable def externalStableKeyIntervalRowTable {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) :
    RatInterval.CaseTable (StableKey maxDegree maxRange) :=
  externalStableKeyIntervalTable (stableKeyIntervalRowRecords rows)
    (intervalOfRows rows fallback)

@[simp] theorem externalStableKeyIntervalRowTable_cases
    {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) :
    (externalStableKeyIntervalRowTable rows fallback).cases =
      stableKeyIntervalRowKeyFinset rows :=
  rfl

@[simp] theorem externalStableKeyIntervalRowTable_interval
    {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval) (k : StableKey maxDegree maxRange) :
    (externalStableKeyIntervalRowTable rows fallback).interval k =
      intervalOfRows rows fallback k :=
  rfl




theorem externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue
    {α : Type*} {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (classifier : α → StableKey maxDegree maxRange)
    (value : α → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hcover : ∀ a, classifier a ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ a, value a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalRowTable rows fallback) classifier ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalRowTable rows fallback) classifier value := by
  exact externalStableKeyIntervalTable_covers_and_sound_of_keyValue
    (stableKeyIntervalRowRecords rows) (intervalOfRows rows fallback)
    classifier value keyValue hcover hvalue
    (fun k hk => intervalOfRows_memR_of_mem_keyFinset rows fallback keyValue hrow hk)





theorem externalStableKeyIntervalRowTable_covers_and_sound_of_exactKeySet
    {α : Type*} {maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (expected : Finset (StableKey maxDegree maxRange))
    (classifier : α → StableKey maxDegree maxRange)
    (value : α → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hexact : StableKeyIntervalRow.ExactKeySet rows expected)
    (hcover : ∀ a, classifier a ∈ expected)
    (hvalue : ∀ a, value a = keyValue (classifier a))
    (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalRowTable rows fallback) classifier ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalRowTable rows fallback) classifier value := by
  exact externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue
    rows fallback classifier value keyValue
    (StableKeyIntervalRow.classifier_mem_rows_of_exactKeySet
      hexact classifier hcover)
    hvalue hrow




theorem externalStableKeyIntervalRows_covers_and_sound_boundedLocal_of_keyValue
    {d R maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hcover : ∀ c : BoundedPolymerCase d R maxDegree maxRange,
      stableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      value c = keyValue (stableKey (classifyBoundedLocalCoordinate c)))
    (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalRowTable rows fallback)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          stableKey (classifyBoundedLocalCoordinate c)) ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalRowTable rows fallback)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          stableKey (classifyBoundedLocalCoordinate c)) value := by
  exact externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue
    rows fallback
    (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
      stableKey (classifyBoundedLocalCoordinate c))
    value keyValue
    (fun c => hcover (classifyBoundedLocalCoordinate c))
    hvalue hrow




theorem externalStableKeyIntervalRows_covers_and_sound_minimalCubicBoundedLocal_of_keyValue
    {d R maxDegree maxRange : ℕ}
    (rows : List (StableKeyIntervalRow maxDegree maxRange))
    (fallback : RatInterval)
    (value : BoundedLocalCoordinate d R maxDegree maxRange → ℝ)
    (keyValue : StableKey maxDegree maxRange → ℝ)
    (hcover : ∀ c : BoundedPolymerCase d R maxDegree maxRange,
      classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset rows)
    (hvalue : ∀ c,
      value c =
        keyValue (classifyByMinimalCubicStableKey
          (classifyBoundedLocalCoordinate c)))
    (hrow : ∀ row, row ∈ rows → row.interval.MemR (keyValue row.key.toKey)) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalRowTable rows fallback)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalRowTable rows fallback)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) value := by
  exact externalStableKeyIntervalRowTable_covers_and_sound_of_keyValue
    rows fallback
    (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
      classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c))
    value keyValue
    (fun c => hcover (classifyBoundedLocalCoordinate c))
    hvalue hrow

end BoundedPolymerCase
end Exact3D
end StatMech
