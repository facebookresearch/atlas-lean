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

/-- **Trie.** A trie with keys that are lists over $\alpha$ and values in $\beta$ is a node
consisting of an optional value in $\beta$ and a finite list of children, each child being a pair
of a letter in $\alpha$ and a trie. The letters labelling the children need not be distinct. -/
inductive Trie (α : Type u) (β : Type v) where
  | node : Option β → List (α × Trie α β) → Trie α β

namespace Trie

/-- **Empty trie.** The empty trie is the trie consisting of a single root node that stores no
value and has no children, so it contains no key-value entries. -/
def empty {α : Type u} {β : Type v} : Trie α β :=
  .node none []

/-- **Trie lookup.** The lookup of a key (a list over $\alpha$) in a trie returns an optional
value in $\beta$, by recursion on the key. For the empty key it is the optional value stored at
the root. For a key with first letter $a$ followed by the key $k$, it fails if no child of the
root is labelled $a$, and otherwise it is the lookup of $k$ in the first child labelled $a$. -/
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

/-- **Trie insertion.** Inserting a value $v$ at a key $k$ (a list of letters) in a trie stores $v$
at the node reached by following $k$ from the root, replacing any value stored there. Along the
way, a missing child is created as an empty trie and appended after its siblings, an existing
child is updated in place, and all other values and children are unchanged. -/
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

/-- **Valid trie.** Validity of tries is defined inductively: a trie node with optional value $v$
and child list $c$ is valid when the letters labelling the children in $c$ are pairwise distinct
and every child trie in $c$ is valid. -/
inductive Valid {α : Type u} {β : Type v} : Trie α β → Prop where
  | node {value : Option β} {children : List (α × Trie α β)}
      (distinct : (children.map Prod.fst).Nodup)
      (childrenValid : ∀ child ∈ children, Valid child.2) :
      Valid (.node value children)

/-- **Entries of a trie.** The entries of a trie are the list of its key-value pairs, where a key
is a list of letters. If the root stores a value $v$, the list begins with the pair consisting of
the empty key and $v$; it continues, for each child in the stored sibling order, with the entries
$(k, w)$ of that child, in order, each rewritten as $(a k, w)$, where $a$ is the letter labelling
the child and $a k$ is the key $k$ with $a$ prepended. -/
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

/-- **Lookup in the empty trie.** For every key $k$, looking up $k$ in the empty trie returns no
value. -/
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

/-- **Lookup after insertion in a trie.** Let $\alpha$ be a type with decidable equality. For
every trie $T$ with keys that are lists over $\alpha$ and values in $\beta$, every key $k$ and
every value $v \in \beta$, looking up $k$ in the trie obtained from $T$ by inserting $v$ at $k$
returns $v$. -/
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

/-- **Trie insertion leaves other keys unchanged.** For every trie $T$, all keys $k \ne k'$ and
every value $v$, looking up $k$ in the trie obtained by inserting $v$ at $k'$ in $T$ gives the
same result as looking up $k$ in $T$. -/
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

/-- **Valid trie nodes have distinct child keys.** If a trie node with optional value $v$ and
child list $c$ is valid, then the letters labelling the children in $c$ are pairwise distinct. -/
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

/-- **Insertion preserves trie validity.** If a trie $T$ is valid, then for every key $k$ (a list
of letters) and every value $v$, the trie obtained by inserting $v$ at $k$ in $T$ is valid. -/
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

/-- **Trie lookup agrees with the entries.** For every valid trie $T$, every key $k$ and every
value $v$, looking up $k$ in $T$ returns $v$ if and only if $(k, v)$ is one of the entries of
$T$. -/
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

/-- **Lookup equivalence of tries.** Two tries $T$ and $T'$ are lookup-equivalent when, for every
key $k$, looking up $k$ in $T$ gives the same result as looking up $k$ in $T'$. -/
def LookupEquiv {α : Type u} {β : Type v} [DecidableEq α]
    (left right : Trie α β) : Prop :=
  ∀ keys, left.lookup keys = right.lookup keys

/-- **Reflexivity of trie lookup equivalence.** Every trie is lookup-equivalent to itself. -/
theorem LookupEquiv.refl {α : Type u} {β : Type v} [DecidableEq α]
    (trie : Trie α β) : LookupEquiv trie trie := by
  intro keys
  rfl

/-- **Symmetry of trie lookup equivalence.** If a trie $T$ is lookup-equivalent to a trie $T'$,
then $T'$ is lookup-equivalent to $T$. -/
theorem LookupEquiv.symm {α : Type u} {β : Type v} [DecidableEq α]
    {left right : Trie α β} (h : LookupEquiv left right) : LookupEquiv right left := by
  intro keys
  exact (h keys).symm

/-- **Transitivity of trie lookup equivalence.** If a trie $T_1$ is lookup-equivalent to a trie
$T_2$ and $T_2$ is lookup-equivalent to a trie $T_3$, then $T_1$ is lookup-equivalent to $T_3$. -/
theorem LookupEquiv.trans {α : Type u} {β : Type v} [DecidableEq α]
    {first second third : Trie α β}
    (h₁ : LookupEquiv first second) (h₂ : LookupEquiv second third) :
    LookupEquiv first third := by
  intro keys
  exact (h₁ keys).trans (h₂ keys)

/-- **Lookup-equivalent valid tries have the same entries.** Let $T$ and $T'$ be valid tries
with keys that are lists over $\alpha$ and values in $\beta$, and suppose $T$ and $T'$ are
lookup-equivalent. Then for every key $k$ and every value $v \in \beta$, the pair $(k, v)$
occurs in the entry list of $T$ if and only if it occurs in the entry list of $T'$. -/
theorem LookupEquiv.mem_entries_iff {α : Type u} {β : Type v} [DecidableEq α]
    {left right : Trie α β} (h : LookupEquiv left right)
    (hleft : Valid left) (hright : Valid right) (keys : List α) (value : β) :
    (keys, value) ∈ left.entries ↔ (keys, value) ∈ right.entries := by
  rw [← lookup_eq_some_iff_mem_entries hleft keys value,
    ← lookup_eq_some_iff_mem_entries hright keys value, h keys]

/-- **Insertions at distinct keys commute in a trie.** For every trie $T$, all keys $k_1 \ne k_2$
and all values $v_1, v_2$, inserting $v_1$ at $k_1$ and then $v_2$ at $k_2$ gives a trie that is
lookup-equivalent to the one obtained by inserting $v_2$ at $k_2$ and then $v_1$ at $k_1$. -/
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
