/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Trie

/-!
# Trie deletion

Deletion for the finite tries of `CSLibExt.Algorithms.Lean.DataStructures.Trie`.
`delete` unmarks the terminal node of the deleted key and prunes childless
non-terminal nodes on the way back up: when the recursively updated child
carries no value and no children, its entry is dropped from the parent
altogether. The pruning step replaces the first entry at the updated key
in place and drops any later duplicates at that key, so the order of the
surviving entries (and hence of `entries`) is preserved and the lookup
specifications hold for arbitrary tries, with no `Valid` hypothesis;
`Valid.delete` separately records that deletion preserves the invariant.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

namespace Trie

/-- **Empty trie nodes.** The empty-node test is true on a trie node exactly when the node
carries no value and has no children; when deletion leaves a child in this state, the child is
removed from its parent. -/
def isEmptyNode {α : Type u} {β : Type v} : Trie α β → Bool
  | .node value children => value.isNone && children.isEmpty

/-- **Characterization of empty nodes.** The empty-node test is true on a trie $t$ exactly when
$t$ is the node with no value and no children, that is, the empty trie. -/
theorem isEmptyNode_eq_true_iff {α : Type u} {β : Type v}
    {t : Trie α β} : isEmptyNode t = true ↔ t = .node none [] := by
  cases t with
  | node value children =>
      cases value with
      | none =>
          cases children with
          | nil => simp [isEmptyNode]
          | cons head children => simp [isEmptyNode]
      | some result => simp [isEmptyNode]

private theorem lookup_eq_none_of_isEmptyNode {α : Type u} {β : Type v}
    [DecidableEq α] {t : Trie α β} (h : isEmptyNode t = true)
    (keys : List α) : t.lookup keys = none := by
  have ht : t = .node none [] := isEmptyNode_eq_true_iff.mp h
  subst ht
  exact lookup_empty keys

private theorem lookup_filter_key {α : Type u} {β : Type v}
    [DecidableEq α] {key : α} {children : List (α × Trie α β)} :
    (children.filter (fun entry => entry.1 != key)).lookup key = none := by
  induction children with
  | nil => rfl
  | cons head children ih =>
      rcases head with ⟨k', c'⟩
      by_cases h : k' = key
      · subst k'
        simp [List.filter, ih]
      · have hb : (k' != key) = true := by simp [h]
        have hb2 : (key == k') = false := by
          simp [show key ≠ k' from fun hh => h hh.symm]
        simp [List.filter, List.lookup, hb, hb2, ih]

private theorem lookup_filter_of_ne {α : Type u} {β : Type v}
    [DecidableEq α] {k key : α} (hk : k ≠ key)
    {children : List (α × Trie α β)} :
    (children.filter (fun entry => entry.1 != key)).lookup k =
      children.lookup k := by
  induction children with
  | nil => rfl
  | cons head children ih =>
      rcases head with ⟨k', c'⟩
      by_cases h : k' = key
      · subst k'
        have hb2 : (k == key) = false := by simp [hk]
        simp [List.filter, List.lookup, hb2, ih]
      · have hb : (k' != key) = true := by simp [h]
        by_cases hk' : k = k'
        · subst k'
          simp [List.filter, List.lookup, hb]
        · have hb2 : (k == k') = false := by simp [hk']
          simp [List.filter, List.lookup, hb, hb2, ih]

/--
**Setting a child in a trie's child list.** Let $L$ be a list of pairs $(k, c)$ of a key $k$
in $\alpha$ and a trie $c$ (the children of a trie node), let $a$ be a key and $t$ a trie, and
call $t$ empty when it carries no value and has no children. Setting the child at $a$ to $t$
in $L$ gives the following list. If no entry of $L$ has key $a$, the result is $L$ itself when
$t$ is empty, and $L$ with $(a, t)$ appended at the end otherwise. If some entry of $L$ has key
$a$, the entries before the first such entry are kept; that entry is replaced in place by
$(a, t)$, or removed when $t$ is empty; and every later entry with key $a$ is removed, while
later entries with other keys are kept in their order.

Thus the order of the surviving entries is preserved and at most one entry with key $a$
remains, even when $L$ has repeated keys. Deletion from a trie uses this operation to prune
empty nodes.
-/
def setChild {α : Type u} {β : Type v} [DecidableEq α] (key : α)
    (child : Trie α β) :
    List (α × Trie α β) → List (α × Trie α β)
  | [] => if isEmptyNode child then [] else [(key, child)]
  | (k, c) :: rest =>
      if k = key then
        if isEmptyNode child then rest.filter (fun entry => entry.1 != key)
        else (key, child) :: rest.filter (fun entry => entry.1 != key)
      else (k, c) :: setChild key child rest

/-- **Looking up a child just set.** Let $L$ be a list of letter–trie pairs, $a$ a letter and
$c$ a trie, and let $L'$ be obtained from $L$ by setting the child at $a$ to $c$ (removing the
entries at $a$ instead when $c$ has neither value nor children). Looking up $a$ in $L'$ finds
nothing when $c$ has neither value nor children, and finds $c$ otherwise. -/
theorem lookup_setChild_self {α : Type u} {β : Type v}
    [DecidableEq α] (key : α) (child : Trie α β)
    (children : List (α × Trie α β)) :
    (setChild key child children).lookup key =
      if isEmptyNode child then none else some child := by
  induction children with
  | nil =>
      by_cases he : isEmptyNode child = true <;> simp [setChild, he]
  | cons head children ih =>
      rcases head with ⟨k', c'⟩
      by_cases h : k' = key
      · subst k'
        by_cases he : isEmptyNode child = true
        · simp [setChild, he, lookup_filter_key]
        · simp [setChild, he]
      · have hb : (key == k') = false := by
          simp [show key ≠ k' from fun hh => h hh.symm]
        simp [setChild, h, List.lookup, hb, ih]

/-- **Setting a child leaves the other children unchanged.** Let $L$ be a list of letter–trie
pairs, $c$ a trie and $a \ne b$ letters, and let $L'$ be obtained from $L$ by setting the child
at $b$ to $c$ (removing the entries at $b$ instead when $c$ has neither value nor children).
Then looking up $a$ in $L'$ gives the same result as looking up $a$ in $L$. -/
theorem lookup_setChild_of_ne {α : Type u} {β : Type v}
    [DecidableEq α] {k key : α} (hk : k ≠ key) (child : Trie α β)
    (children : List (α × Trie α β)) :
    (setChild key child children).lookup k = children.lookup k := by
  induction children with
  | nil =>
      have hb : (k == key) = false := by simp [hk]
      by_cases he : isEmptyNode child = true <;>
        simp [setChild, he, List.lookup, hb]
  | cons head children ih =>
      rcases head with ⟨k', c'⟩
      by_cases h : k' = key
      · subst k'
        have hb : (k == key) = false := by simp [hk]
        by_cases he : isEmptyNode child = true
        · simp [setChild, he, List.lookup, hb, lookup_filter_of_ne hk]
        · simp [setChild, he, List.lookup, hb, lookup_filter_of_ne hk]
      · by_cases hk' : k = k'
        · subst k'
          simp [setChild, h, List.lookup]
        · have hb : (k == k') = false := by simp [hk']
          simp [setChild, h, List.lookup, hb, ih]

private theorem mem_of_lookup_eq_some {α : Type u} {β : Type v}
    [DecidableEq α] {key : α} {child : Trie α β}
    {children : List (α × Trie α β)}
    (h : children.lookup key = some child) : (key, child) ∈ children := by
  induction children with
  | nil => simp [List.lookup] at h
  | cons head children ih =>
      rcases head with ⟨k', c'⟩
      by_cases hk : key = k'
      · subst k'
        have hb : (key == key) = true := by simp
        simp [List.lookup, hb] at h
        cases h
        exact List.mem_cons_self
      · have hb : (key == k') = false := by simp [hk]
        simp [List.lookup, hb] at h
        exact List.mem_cons_of_mem _ (ih h)

private theorem mem_setChild {α : Type u} {β : Type v}
    [DecidableEq α] {key : α} {child : Trie α β}
    {children : List (α × Trie α β)} {entry : α × Trie α β}
    (he : entry ∈ setChild key child children) :
    entry = (key, child) ∨ entry ∈ children := by
  induction children with
  | nil =>
      by_cases hempty : isEmptyNode child = true
      · simp [setChild, hempty] at he
      · simp [setChild, hempty] at he
        exact Or.inl he
  | cons head children ih =>
      rcases head with ⟨k', c'⟩
      by_cases h : k' = key
      · subst k'
        by_cases hempty : isEmptyNode child = true
        · have hEq : setChild key child ((key, c') :: children) =
              children.filter (fun e => e.1 != key) := by
            simp [setChild, hempty]
          rw [hEq] at he
          exact Or.inr (List.mem_cons_of_mem _ (List.mem_filter.mp he).1)
        · have hEq : setChild key child ((key, c') :: children) =
              (key, child) :: children.filter (fun e => e.1 != key) := by
            simp [setChild, hempty]
          rw [hEq] at he
          rcases List.mem_cons.mp he with rfl | he
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ (List.mem_filter.mp he).1)
      · have hEq : setChild key child ((k', c') :: children) =
            (k', c') :: setChild key child children := by
          simp [setChild, h]
        rw [hEq] at he
        rcases List.mem_cons.mp he with rfl | he
        · exact Or.inr List.mem_cons_self
        · rcases ih he with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (List.mem_cons_of_mem _ h1)

private theorem mem_fst_setChild {α : Type u} {β : Type v}
    [DecidableEq α] {x key : α} {child : Trie α β}
    {children : List (α × Trie α β)}
    (hx : x ∈ (setChild key child children).map Prod.fst) :
    x = key ∨ x ∈ children.map Prod.fst := by
  obtain ⟨entry, he, hf⟩ := List.mem_map.mp hx
  rcases mem_setChild he with rfl | he
  · exact Or.inl hf.symm
  · exact Or.inr (List.mem_map.mpr ⟨entry, he, hf⟩)

private theorem nodup_fst_setChild {α : Type u} {β : Type v}
    [DecidableEq α] {key : α} {child : Trie α β}
    {children : List (α × Trie α β)}
    (hkeys : (children.map Prod.fst).Nodup) :
    ((setChild key child children).map Prod.fst).Nodup := by
  induction children with
  | nil =>
      by_cases hempty : isEmptyNode child = true <;> simp [setChild, hempty]
  | cons head children ih =>
      rcases head with ⟨k', c'⟩
      have hcons : (k' :: children.map Prod.fst).Nodup := hkeys
      have hnot : k' ∉ children.map Prod.fst := (List.nodup_cons.mp hcons).1
      have htail : (children.map Prod.fst).Nodup := (List.nodup_cons.mp hcons).2
      by_cases h : k' = key
      · subst k'
        have hFiltNodup :
            ((children.filter (fun e => e.1 != key)).map Prod.fst).Nodup :=
          (List.filter_sublist.map Prod.fst).nodup htail
        by_cases hempty : isEmptyNode child = true
        · have hEq : setChild key child ((key, c') :: children) =
              children.filter (fun e => e.1 != key) := by
            simp [setChild, hempty]
          rw [hEq]
          exact hFiltNodup
        · have hNotMem :
              key ∉ (children.filter (fun e => e.1 != key)).map Prod.fst := by
            intro hm
            obtain ⟨entry, he, hf⟩ := List.mem_map.mp hm
            have h2 := (List.mem_filter.mp he).2
            simp [hf] at h2
          have hEq : setChild key child ((key, c') :: children) =
              (key, child) :: children.filter (fun e => e.1 != key) := by
            simp [setChild, hempty]
          rw [hEq]
          simp only [List.map_cons, List.nodup_cons]
          exact ⟨hNotMem, hFiltNodup⟩
      · have hEq : setChild key child ((k', c') :: children) =
            (k', c') :: setChild key child children := by
          simp [setChild, h]
        rw [hEq]
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, ih htail⟩
        intro hm
        rcases mem_fst_setChild hm with h1 | h1
        · exact h h1
        · exact hnot h1

/-- **Setting a child preserves the child-list part of validity.** Let $L$ be a list of
letter–trie pairs whose letters are pairwise distinct and whose tries are all valid, let $c$
be a valid trie and $a$ a letter. Then the list obtained from $L$ by setting the child at $a$
to $c$ (removing the entries at $a$ instead when $c$ has neither value nor children) again has
pairwise distinct letters, and every trie in it is valid. -/
theorem setChild_valid {α : Type u} {β : Type v}
    [DecidableEq α] {key : α} {child : Trie α β}
    {children : List (α × Trie α β)}
    (hkeys : (children.map Prod.fst).Nodup)
    (hchildren : ∀ entry ∈ children, Valid entry.2)
    (hchild : Valid child) :
    ((setChild key child children).map Prod.fst).Nodup ∧
      ∀ entry ∈ setChild key child children, Valid entry.2 := by
  refine ⟨nodup_fst_setChild hkeys, ?_⟩
  intro entry he
  rcases mem_setChild he with rfl | he
  · exact hchild
  · exact hchildren entry he

/-- **Setting a child preserves validity.** Let a trie node with value $v$ and child list $L$ be
valid, let $c$ be a valid trie and $a$ a letter. Then the node with value $v$ whose child list
is obtained from $L$ by setting the child at $a$ to $c$ (removing the entries at $a$ instead
when $c$ has neither value nor children) is valid. -/
theorem Valid.setChild {α : Type u} {β : Type v}
    [DecidableEq α] {value : Option β} {children : List (α × Trie α β)}
    (h : Valid (.node value children)) {key : α} {child : Trie α β}
    (hchild : Valid child) :
    Valid (.node value (setChild key child children)) := by
  cases h with
  | node distinct childrenValid =>
      have hset := setChild_valid (key := key) distinct childrenValid hchild
      exact .node hset.1 hset.2

/--
**Deletion from a trie.** Deleting a key $k$ (a list of letters) from a trie $t$ works by
recursion on $k$. If $k$ is empty, the root of $t$ loses its value and keeps its children. If
$k$ consists of a first letter $a$ followed by a key $k'$ and the root of $t$ has no child at
$a$, then $t$ is unchanged. Otherwise $k'$ is deleted from the first child at $a$. If the
result has neither value nor children, every entry at $a$ is removed from the root's child
list; if not, the first entry at $a$ is replaced by the result and any later entries at $a$
are removed. The root's value and the other children, in their order, are kept.

Deleting an absent key leaves every lookup unchanged.
-/
def delete {α : Type u} {β : Type v} [DecidableEq α] (trie : Trie α β) :
    List α → Trie α β
  | [] =>
      match trie with
      | .node _ children => .node none children
  | key :: keys =>
      match trie with
      | .node current children =>
          match children.lookup key with
          | none => .node current children
          | some child =>
              .node current (setChild key (delete child keys) children)

/-- **A deleted key is absent.** For every trie $t$ and every key $k$, looking up $k$ in the
trie obtained from $t$ by deleting $k$ finds no value. -/
@[simp]
theorem lookup_delete_self {α : Type u} {β : Type v} [DecidableEq α]
    (trie : Trie α β) (keys : List α) :
    (trie.delete keys).lookup keys = none := by
  induction keys generalizing trie with
  | nil =>
      cases trie
      rfl
  | cons key keys ih =>
      cases trie with
      | node current children =>
          cases hlookup : children.lookup key with
          | none => simp [delete, lookup, hlookup]
          | some child =>
              simp only [delete, hlookup, lookup]
              rw [lookup_setChild_self]
              by_cases he : isEmptyNode (child.delete keys) = true
              · simp [he]
              · simp [he, ih child]

/-- **Deletion does not affect other keys.** For every trie $t$ and all keys $k \ne k'$, looking
up $k$ in the trie obtained from $t$ by deleting $k'$ gives the same result as looking up $k$
in $t$. -/
@[simp]
theorem lookup_delete_of_ne {α : Type u} {β : Type v} [DecidableEq α]
    (trie : Trie α β) {deletedKeys keys : List α}
    (h : keys ≠ deletedKeys) :
    (trie.delete deletedKeys).lookup keys = trie.lookup keys := by
  induction deletedKeys generalizing trie keys with
  | nil =>
      cases keys with
      | nil => exact (h rfl).elim
      | cons key keys =>
          cases trie
          rfl
  | cons deletedKey deletedKeys ih =>
      cases keys with
      | nil =>
          cases trie with
          | node current children =>
              cases hlookup : children.lookup deletedKey <;>
                simp [delete, lookup, hlookup]
      | cons key keys =>
          cases trie with
          | node current children =>
              by_cases hk : key = deletedKey
              · subst deletedKey
                have hne : keys ≠ deletedKeys := by
                  intro heq
                  apply h
                  rw [heq]
                cases hlookup : children.lookup key with
                | none => simp [delete, lookup, hlookup]
                | some child =>
                    simp only [delete, hlookup, lookup]
                    rw [lookup_setChild_self]
                    by_cases he : isEmptyNode (child.delete deletedKeys) =
                        true
                    · have hchild : child.lookup keys = none := by
                        rw [← ih child hne]
                        exact lookup_eq_none_of_isEmptyNode he keys
                      simp [he, hchild]
                    · simp [he, ih child hne]
              · cases hlookup : children.lookup deletedKey with
                | none => simp [delete, lookup, hlookup]
                | some child =>
                    simp only [delete, hlookup, lookup]
                    rw [lookup_setChild_of_ne hk]

/-- **Deletion preserves trie validity.** If a trie $t$ is valid, that is, every node has distinct
child keys and valid child tries, then for every key $k$ the trie obtained from $t$ by deleting
$k$ is valid. -/
theorem Valid.delete {α : Type u} {β : Type v} [DecidableEq α]
    {trie : Trie α β} (h : Valid trie) (keys : List α) :
    Valid (trie.delete keys) := by
  induction keys generalizing trie with
  | nil =>
      cases h with
      | node distinct childrenValid => exact .node distinct childrenValid
  | cons key keys ih =>
      cases h with
      | @node current children distinct childrenValid =>
          cases hlookup : children.lookup key with
          | none =>
              have hEq : (Trie.node current children).delete
                    (key :: keys) =
                  .node current children := by
                simp [Trie.delete, hlookup]
              rw [hEq]
              exact .node distinct childrenValid
          | some child =>
              have hmem : (key, child) ∈ children :=
                mem_of_lookup_eq_some hlookup
              have hnew : Valid (child.delete keys) :=
                ih (childrenValid (key, child) hmem)
              have hset := setChild_valid (key := key) distinct
                childrenValid hnew
              have hEq : (Trie.node current children).delete
                    (key :: keys) =
                  .node current
                    (Trie.setChild key (child.delete keys) children) := by
                simp [Trie.delete, hlookup]
              rw [hEq]
              exact .node hset.1 hset.2

end Trie

end Cslib.Algorithms.Lean
