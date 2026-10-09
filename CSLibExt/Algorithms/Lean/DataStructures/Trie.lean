/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Finite tries

This file defines a finite trie whose keys are lists over a decidable alphabet. A node stores an
optional value independently of its children, so a key may end at an internal prefix. Child keys
are unique in a valid trie; lookup-equivalence is the semantic abstraction when sibling order
differs. The order of `entries` follows the stored sibling order. Children use a raw association
list because Lean cannot nest recursively valued tries in `AList`; `Valid` records key uniqueness.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

/-- A finite trie from list keys over `α` to values in `β`. -/
inductive Trie (α : Type u) (β : Type v) where
  | node : Option β → List (α × Trie α β) → Trie α β

namespace Trie

/-- The trie containing no key-value entries. -/
def empty {α : Type u} {β : Type v} : Trie α β :=
  .node none []

/-- Looks up a list key in a trie. -/
def lookup {α : Type u} {β : Type v} [DecidableEq α]
    (trie : Trie α β) : List α → Option β
  | [] =>
      match trie with
      | .node value _ => value
  | key :: keys =>
      match trie with
      | .node _ children =>
          match children.lookup key with
          | none => none
          | some child => lookup child keys

/-- Inserts or replaces the value at a list key. -/
def insert {α : Type u} {β : Type v} [DecidableEq α]
    (trie : Trie α β) : List α → β → Trie α β
  | [], value =>
      match trie with
      | .node _ children => .node (some value) children
  | key :: keys, value =>
      match trie with
      | .node current children =>
          let child := (children.lookup key).getD empty
          .node current (childInsert key (insert child keys value) children)
where
  childInsert (key : α) (child : Trie α β) :
      List (α × Trie α β) → List (α × Trie α β)
    | [] => [(key, child)]
    | (key', child') :: children =>
        if key = key' then (key, child) :: children
        else (key', child') :: childInsert key child children

/-- The invariant that every node has distinct child keys and valid child tries. -/
inductive Valid {α : Type u} {β : Type v} : Trie α β → Prop where
  | node {value : Option β} {children : List (α × Trie α β)}
      (distinct : (children.map Prod.fst).Nodup)
      (childrenValid : ∀ child ∈ children, Valid child.2) :
      Valid (.node value children)

/-- Enumerates the key-value entries of a trie in stored sibling order. -/
def entries {α : Type u} {β : Type v} : Trie α β → List (List α × β)
  | .node value children =>
      (match value with
       | none => []
       | some result => [([], result)]) ++ childEntries children
where
  childEntries : List (α × Trie α β) → List (List α × β)
    | [] => []
    | (key, child) :: children =>
        child.entries.map (fun (keys, result) => (key :: keys, result)) ++
          childEntries children

/-- Every lookup in the empty trie fails. -/
@[simp]
theorem lookup_empty {α : Type u} {β : Type v} [DecidableEq α]
    (keys : List α) : (empty : Trie α β).lookup keys = none := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp [lookup, empty, List.lookup]

private theorem lookup_childInsert_same {α : Type u} {β : Type v}
    [DecidableEq α] (key : α) (child : Trie α β)
    (children : List (α × Trie α β)) :
    (insert.childInsert key child children).lookup key = some child := by
  induction children with
  | nil => simp [insert.childInsert]
  | cons head children ih =>
      rcases head with ⟨key', child'⟩
      by_cases h : key = key'
      · subst key'
        simp [insert.childInsert]
      · have hb : (key == key') = false := by simp [h]
        simp [insert.childInsert, List.lookup, h, hb, ih]

private theorem lookup_childInsert_ne {α : Type u} {β : Type v}
    [DecidableEq α] {key insertedKey : α} (h : key ≠ insertedKey)
    (child : Trie α β) (children : List (α × Trie α β)) :
    (insert.childInsert insertedKey child children).lookup key =
      children.lookup key := by
  induction children with
  | nil =>
      have hb : (key == insertedKey) = false := by simp [h]
      simp [insert.childInsert, List.lookup, hb]
  | cons head children ih =>
      rcases head with ⟨key', child'⟩
      by_cases hi : insertedKey = key'
      · subst key'
        have hb : (key == insertedKey) = false := by simp [h]
        simp [insert.childInsert, List.lookup, hb]
      · by_cases hk : key = key'
        · subst key'
          simp [insert.childInsert, List.lookup, hi]
        · have hb : (key == key') = false := by simp [hk]
          simp [insert.childInsert, List.lookup, hi, hb, ih]

/-- Looking up an inserted key returns its new value. -/
@[simp]
theorem lookup_insert_same {α : Type u} {β : Type v} [DecidableEq α]
    (trie : Trie α β) (keys : List α) (value : β) :
    (trie.insert keys value).lookup keys = some value := by
  induction keys generalizing trie with
  | nil =>
      cases trie
      rfl
  | cons key keys ih =>
      cases trie with
      | node current children =>
          simp only [insert, lookup]
          rw [lookup_childInsert_same]
          exact ih _

/-- Inserting one key does not change the lookup result for a distinct key. -/
@[simp]
theorem lookup_insert_of_ne {α : Type u} {β : Type v} [DecidableEq α]
    (trie : Trie α β) {insertedKeys keys : List α} (value : β)
    (h : keys ≠ insertedKeys) :
    (trie.insert insertedKeys value).lookup keys = trie.lookup keys := by
  induction insertedKeys generalizing trie keys with
  | nil =>
      cases keys with
      | nil => exact (h rfl).elim
      | cons key keys =>
          cases trie
          rfl
  | cons insertedKey insertedKeys ih =>
      cases keys with
      | nil =>
          cases trie
          rfl
      | cons key keys =>
          cases trie with
          | node current children =>
              by_cases hk : key = insertedKey
              · subst insertedKey
                simp only [insert, lookup]
                rw [lookup_childInsert_same]
                cases hlookup : children.lookup key with
                | none =>
                    simp only [Option.getD_none]
                    rw [ih empty]
                    · exact lookup_empty keys
                    · intro hkeys
                      apply h
                      cases hkeys
                      rfl
                | some child =>
                    simp only [Option.getD_some]
                    apply ih
                    intro hkeys
                    apply h
                    cases hkeys
                    rfl
              · simp only [insert, lookup]
                rw [lookup_childInsert_ne hk]

/-- A valid node has no duplicate child keys. -/
theorem Valid.nodup_child_keys {α : Type u} {β : Type v}
    {value : Option β} {children : List (α × Trie α β)}
    (h : Valid (.node value children)) :
    (children.map Prod.fst).Nodup := by
  cases h with
  | node distinct _ => exact distinct

/-- The empty trie is valid. -/
theorem Valid.empty {α : Type u} {β : Type v} :
    Valid (empty : Trie α β) :=
  .node (by simp) (by simp)

private theorem childInsert_preserves_not_mem {α : Type u} {β : Type v}
    [DecidableEq α] {key insertedKey : α} (h : key ≠ insertedKey)
    (child : Trie α β) (children : List (α × Trie α β))
    (hnot : key ∉ children.map Prod.fst) :
    key ∉ (insert.childInsert insertedKey child children).map Prod.fst := by
  induction children with
  | nil => simp [insert.childInsert, h]
  | cons head children ih =>
      rcases head with ⟨key', child'⟩
      have hhead : key ≠ key' := by
        intro hEq
        apply hnot
        simp [hEq]
      have htail : key ∉ children.map Prod.fst := by
        intro hmem
        apply hnot
        simp [hmem]
      by_cases hi : insertedKey = key'
      · subst key'
        simp [insert.childInsert, h, htail]
      · simp [insert.childInsert, hi, hhead, ih htail]

private theorem childInsert_valid {α : Type u} {β : Type v}
    [DecidableEq α] {key : α} {child : Trie α β}
    {children : List (α × Trie α β)}
    (hkeys : (children.map Prod.fst).Nodup)
    (hchildren : ∀ entry ∈ children, Valid entry.2)
    (hchild : Valid child) :
    ((insert.childInsert key child children).map Prod.fst).Nodup ∧
      ∀ entry ∈ insert.childInsert key child children, Valid entry.2 := by
  induction children with
  | nil => simp [insert.childInsert, hchild]
  | cons head children ih =>
      rcases head with ⟨key', child'⟩
      have hchild' : Valid child' := hchildren (key', child') (by simp)
      have htail : ∀ entry ∈ children, Valid entry.2 := by
        intro entry hentry
        exact hchildren entry (by simp [hentry])
      have htailKeys : (children.map Prod.fst).Nodup := by
        exact (List.nodup_cons.mp hkeys).2
      by_cases h : key = key'
      · subst key'
        constructor
        · simpa [insert.childInsert] using hkeys
        · intro entry hentry
          simp only [insert.childInsert] at hentry
          rw [ite_true] at hentry
          rcases List.mem_cons.mp hentry with hEq | hentry
          · subst entry
            exact hchild
          · exact htail entry hentry
      · have hi := ih htailKeys htail
        have hnot : key' ∉ children.map Prod.fst :=
          (List.nodup_cons.mp hkeys).1
        constructor
        · simp only [insert.childInsert, ite_eq_right h, List.map_cons, List.nodup_cons]
          constructor
          · exact childInsert_preserves_not_mem (fun hEq => h hEq.symm)
              child children hnot
          · exact hi.1
        · intro entry hentry
          simp only [insert.childInsert] at hentry
          rw [ite_eq_right h] at hentry
          rcases List.mem_cons.mp hentry with hEq | hentry
          · subst entry
            exact hchild'
          · exact hi.2 entry hentry

private theorem lookup_eq_some_iff_mem {α : Type u} {β : Type v}
    [DecidableEq α] {key : α} {child : Trie α β}
    {children : List (α × Trie α β)}
    (hkeys : (children.map Prod.fst).Nodup) :
    children.lookup key = some child ↔ (key, child) ∈ children := by
  induction children with
  | nil => simp [List.lookup]
  | cons head children ih =>
      rcases head with ⟨key', child'⟩
      have htail : (children.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hkeys).2
      have hnot : key' ∉ children.map Prod.fst :=
        (List.nodup_cons.mp hkeys).1
      by_cases h : key = key'
      · subst key'
        have hb : (key == key) = true := by simp
        simp only [List.lookup, List.mem_cons, hb]
        constructor
        · intro hEq
          have hEq' : child' = child := Option.some.inj hEq
          subst child
          exact Or.inl rfl
        · intro hor
          rcases hor with hEq | hmem
          · cases hEq
            rfl
          · exact (hnot (List.mem_map.mpr ⟨(key, child), hmem, rfl⟩)).elim
      · have hb : (key == key') = false := by simp [h]
        simp [List.lookup, h, hb, ih htail]

/-- Insertion preserves the trie invariant. -/
theorem Valid.insert {α : Type u} {β : Type v} [DecidableEq α]
    {trie : Trie α β} (h : Valid trie) (keys : List α) (value : β) :
    Valid (trie.insert keys value) := by
  induction keys generalizing trie with
  | nil =>
      cases h with
      | node distinct childrenValid =>
          exact .node distinct childrenValid
  | cons key keys ih =>
      cases h with
      | @node current children distinct childrenValid =>
          let oldChild := (children.lookup key).getD Trie.empty
          have hold : Valid oldChild := by
            simp only [oldChild]
            cases hlookup : children.lookup key with
            | none => exact .node (by simp) (by simp)
            | some child =>
                have hmem : (key, child) ∈ children :=
                  (lookup_eq_some_iff_mem distinct).mp hlookup
                exact childrenValid (key, child) hmem
          have hnew : Valid (oldChild.insert keys value) := ih hold
          have hins := childInsert_valid (key := key) distinct childrenValid hnew
          exact .node hins.1 hins.2

private theorem mem_childEntries_iff_exists {α : Type u} {β : Type v}
    {path : List α} {value : β} {children : List (α × Trie α β)} :
    (path, value) ∈ entries.childEntries children ↔
      ∃ key child keys, (key, child) ∈ children ∧
        (keys, value) ∈ child.entries ∧ path = key :: keys := by
  induction children with
  | nil => simp [entries.childEntries]
  | cons head children ih =>
      rcases head with ⟨key', child'⟩
      rw [entries.childEntries, List.mem_append]
      constructor
      · intro hor
        rcases hor with hhead | htail
        · obtain ⟨entry, hentry, hEq⟩ := List.mem_map.mp hhead
          rcases entry with ⟨keys, result⟩
          have hparts := Prod.mk.inj hEq
          cases hparts.2
          exact ⟨key', child', keys, by simp, hentry, hparts.1.symm⟩
        · obtain ⟨key, child, keys, hmem, hentry, hpath⟩ := ih.mp htail
          exact ⟨key, child, keys, by simp [hmem], hentry, hpath⟩
      · rintro ⟨key, child, keys, hmem, hentry, hpath⟩
        rcases List.mem_cons.mp hmem with hEq | hmem
        · have hparts := Prod.mk.inj hEq
          cases hparts.1
          cases hparts.2
          apply Or.inl
          exact List.mem_map.mpr ⟨(keys, value), hentry, by
            simp only
            exact congrArg (fun path => (path, value)) hpath.symm⟩
        · exact Or.inr (ih.mpr ⟨key, child, keys, hmem, hentry, hpath⟩)

private theorem mem_childEntries_cons_iff {α : Type u} {β : Type v}
    [DecidableEq α] {key : α} {keys : List α} {value : β}
    {children : List (α × Trie α β)}
    (hkeys : (children.map Prod.fst).Nodup) :
    (key :: keys, value) ∈ entries.childEntries children ↔
      ∃ child, children.lookup key = some child ∧
        (keys, value) ∈ child.entries := by
  rw [mem_childEntries_iff_exists]
  constructor
  · rintro ⟨entryKey, child, entryKeys, hmem, hentry, hpath⟩
    have hcons := List.cons.inj hpath
    cases hcons.1
    cases hcons.2
    exact ⟨child, (lookup_eq_some_iff_mem hkeys).mpr hmem, hentry⟩
  · rintro ⟨child, hlookup, hentry⟩
    exact ⟨key, child, keys, (lookup_eq_some_iff_mem hkeys).mp hlookup,
      hentry, rfl⟩

/-- Lookup succeeds with a value exactly when the corresponding pair occurs in `entries`. -/
theorem lookup_eq_some_iff_mem_entries {α : Type u} {β : Type v}
    [DecidableEq α] {trie : Trie α β} (h : Valid trie)
    (keys : List α) (value : β) :
    trie.lookup keys = some value ↔ (keys, value) ∈ trie.entries := by
  induction keys generalizing trie with
  | nil =>
      cases trie with
      | node current children =>
          simp only [lookup, entries, List.mem_append]
          rw [mem_childEntries_iff_exists]
          cases current <;> simp [eq_comm]
  | cons key keys ih =>
      cases trie with
      | node current children =>
        cases h with
        | @node _ _ distinct childrenValid =>
          have hroot : (key :: keys, value) ∉
              (match current with | none => [] | some result => [([], result)]) := by
            cases current <;> simp
          simp only [lookup, entries, List.mem_append, hroot, false_or]
          rw [mem_childEntries_cons_iff distinct]
          cases hlookup : children.lookup key with
          | none => simp
          | some child =>
              have hmem : (key, child) ∈ children :=
                (lookup_eq_some_iff_mem distinct).mp hlookup
              have hvalid : Valid child := childrenValid (key, child) hmem
              simp only
              constructor
              · intro hresult
                exact ⟨child, rfl, (ih hvalid).mp hresult⟩
              · rintro ⟨otherChild, hEq, hentry⟩
                cases Option.some.inj hEq
                exact (ih hvalid).mpr hentry

/-- Semantic equality of tries: every list key has the same lookup result. -/
def LookupEquiv {α : Type u} {β : Type v} [DecidableEq α]
    (left right : Trie α β) : Prop :=
  ∀ keys, left.lookup keys = right.lookup keys

/-- Lookup equivalence is reflexive. -/
theorem LookupEquiv.refl {α : Type u} {β : Type v} [DecidableEq α]
    (trie : Trie α β) : LookupEquiv trie trie := by
  intro keys
  rfl

/-- Lookup equivalence is symmetric. -/
theorem LookupEquiv.symm {α : Type u} {β : Type v} [DecidableEq α]
    {left right : Trie α β} (h : LookupEquiv left right) : LookupEquiv right left := by
  intro keys
  exact (h keys).symm

/-- Lookup equivalence is transitive. -/
theorem LookupEquiv.trans {α : Type u} {β : Type v} [DecidableEq α]
    {first second third : Trie α β}
    (h₁ : LookupEquiv first second) (h₂ : LookupEquiv second third) :
    LookupEquiv first third := by
  intro keys
  exact (h₁ keys).trans (h₂ keys)

/-- Lookup-equivalent valid tries enumerate the same entries, disregarding list order. -/
theorem LookupEquiv.mem_entries_iff {α : Type u} {β : Type v} [DecidableEq α]
    {left right : Trie α β} (h : LookupEquiv left right)
    (hleft : Valid left) (hright : Valid right) (keys : List α) (value : β) :
    (keys, value) ∈ left.entries ↔ (keys, value) ∈ right.entries := by
  rw [← lookup_eq_some_iff_mem_entries hleft keys value,
    ← lookup_eq_some_iff_mem_entries hright keys value, h keys]

/-- Inserting two distinct keys commutes up to lookup equivalence. -/
theorem LookupEquiv.insert_comm {α : Type u} {β : Type v}
    [DecidableEq α] (trie : Trie α β)
    {firstKeys secondKeys : List α} (h : firstKeys ≠ secondKeys)
    (firstValue secondValue : β) :
    LookupEquiv
      ((trie.insert firstKeys firstValue).insert secondKeys secondValue)
      ((trie.insert secondKeys secondValue).insert firstKeys firstValue) := by
  intro keys
  by_cases hfirst : keys = firstKeys
  · subst keys
    calc
      ((trie.insert firstKeys firstValue).insert secondKeys secondValue).lookup firstKeys =
          (trie.insert firstKeys firstValue).lookup firstKeys :=
        lookup_insert_of_ne _ _ h
      _ = some firstValue := lookup_insert_same _ _ _
      _ = ((trie.insert secondKeys secondValue).insert firstKeys firstValue).lookup firstKeys :=
        (lookup_insert_same _ _ _).symm
  · by_cases hsecond : keys = secondKeys
    · subst keys
      calc
        ((trie.insert firstKeys firstValue).insert secondKeys secondValue).lookup secondKeys =
            some secondValue := lookup_insert_same _ _ _
        _ = (trie.insert secondKeys secondValue).lookup secondKeys :=
          (lookup_insert_same _ _ _).symm
        _ = ((trie.insert secondKeys secondValue).insert firstKeys firstValue).lookup secondKeys :=
          (lookup_insert_of_ne _ _ h.symm).symm
    · calc
        ((trie.insert firstKeys firstValue).insert secondKeys secondValue).lookup keys =
            (trie.insert firstKeys firstValue).lookup keys :=
          lookup_insert_of_ne _ _ hsecond
        _ = trie.lookup keys := lookup_insert_of_ne _ _ hfirst
        _ = (trie.insert secondKeys secondValue).lookup keys :=
          (lookup_insert_of_ne _ _ hsecond).symm
        _ = ((trie.insert secondKeys secondValue).insert firstKeys firstValue).lookup keys :=
          (lookup_insert_of_ne _ _ hfirst).symm

end Trie

end Cslib.Algorithms.Lean
