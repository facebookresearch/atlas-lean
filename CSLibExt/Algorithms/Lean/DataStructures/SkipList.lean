/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Nodup
public import Mathlib.Order.Defs.LinearOrder

/-!
# Deterministic skip lists

This module models a finite skip list by a sorted bottom list whose nodes carry positive tower
heights. `level i` selects the nodes whose towers reach level `i`; consequently every upper level
is a subsequence of the level below it. Search descends from the greatest level while carrying the
suffix after the last visible predecessor, so every lower scan starts from the narrowed window.

Insertion takes an explicit height, separating deterministic correctness from any random promotion
policy. A zero requested height is normalized to one. Reinserting a key replaces its value while
preserving its old tower height. This list reference implementation takes `O(n * (H + 1))`
comparisons in the worst case for `n` nodes and maximum height `H`; upper-level progress can narrow
later scans, but no expected logarithmic bound is claimed.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

/-- **Skip-list node.** A skip-list node consists of a key, a value and a natural number, the
height of its tower. The node itself does not require the height to be positive; positivity is
part of the validity invariant of skip lists. -/
public structure SkipList.Entry (α : Type u) (β : Type v) where
  key : α
  value : β
  height : Nat
deriving DecidableEq, Repr

/-- **Skip list.** A deterministic skip list with keys in $\alpha$ and values in $\beta$ is
represented by the list of its bottom-level nodes, each node an entry carrying a key in $\alpha$,
a value in $\beta$ and a tower height, a natural number. No ordering or height condition is
imposed by this structure. -/
public structure SkipList (α : Type u) (β : Type v) where
  entries : List (SkipList.Entry α β)
deriving DecidableEq, Repr

namespace SkipList

/-- **Empty skip list.** The empty skip list is the skip list with no nodes. -/
public def empty {α : Type u} {β : Type v} : SkipList α β :=
  ⟨[]⟩

/-- **Valid skip list.** Let $\alpha$ be a linearly ordered type. A skip list with keys in
$\alpha$ and values in $\beta$ is valid when the keys of its bottom-level nodes are strictly
increasing along the list and every node has a tower of positive height. -/
public def Valid {α : Type u} {β : Type v} [LinearOrder α] (list : SkipList α β) : Prop :=
  list.entries.Pairwise (fun left right => left.key < right.key) ∧
    ∀ entry ∈ list.entries, 0 < entry.height

private def entriesAtLevel {α : Type u} {β : Type v} (index : Nat) :
    List (Entry α β) → List (Entry α β) :=
  List.filter fun entry => index < entry.height

/-- **Level of a skip list.** For a skip list and a level index $i$ (levels are numbered from $0$
at the bottom), level $i$ is the list of key-value pairs $(k, v)$ of the stored nodes whose tower
height $h$ satisfies $i < h$, in the order in which these nodes appear in the bottom-level list
of the skip list. -/
public def level {α : Type u} {β : Type v} (index : Nat) (list : SkipList α β) :
    List (α × β) :=
  (list.entries.filter fun entry => index < entry.height).map fun entry =>
    (entry.key, entry.value)

/-- **Bottom-level abstraction of a skip list.** The bottom-level abstraction of a skip list is
the association list obtained from its bottom-level nodes, in order, by keeping the key-value
pair $(k, v)$ of each node and forgetting its tower height. -/
public def abstraction {α : Type u} {β : Type v} (list : SkipList α β) :
    List (α × β) :=
  list.entries.map fun entry => (entry.key, entry.value)

/-- **Stored tower height of a key.** For a key $k$ and a skip list $S$, the stored tower height
of $k$ in $S$ is the tower height of the first bottom-level node of $S$ whose key equals $k$
under the given Boolean equality test on keys; it is undefined when no node has key $k$. -/
public def heightOf {α : Type u} {β : Type v} [BEq α]
    (key : α) (list : SkipList α β) : Option Nat :=
  (list.entries.map fun entry => (entry.key, entry.height)).lookup key

/-- **One level of skip-list search.** Let $k$ be a search key, $i$ a zero-based level and $L$
a list of skip-list nodes. Let $P$ be the longest prefix of $L$ whose nodes all have keys less
than $k$. If some node of $P$ has tower height greater than $i$ (so it is visible at level
$i$), advancing at level $i$ returns the part of $L$ after the last such node; otherwise it
returns $L$ unchanged.

The returned suffix is the window that every lower level continues to scan. -/
public def advanceAtLevel {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (index : Nat) (entries : List (Entry α β)) : List (Entry α β) :=
  (go entries).getD entries
where
  go : List (Entry α β) → Option (List (Entry α β))
    | [] => none
    | entry :: entries =>
        if entry.key < key then
          match go entries with
          | some suffix => some suffix
          | none => if index < entry.height then some entries else none
        else none

/-- **Skip-list search window.** Let $k$ be a key and let $H$ be the greatest tower height in a
skip list ($H = 0$ if the list is empty or every tower has height $0$). Start with the full list
of bottom-level nodes, and for each level $i$ from $H - 1$ down to $0$ in turn (no levels when
$H = 0$) replace the current list by the result of advancing at level $i$: within the longest
initial segment of the current list whose keys are all less than $k$, take the last node whose
tower height exceeds $i$ and keep only the nodes after it, leaving the list unchanged if there is
no such node. The search window for $k$ is the list that remains after these steps. -/
public def searchWindow {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (list : SkipList α β) : List (Entry α β) :=
  let maximumHeight :=
    list.entries.foldl (fun result entry => max result entry.height) 0
  go (List.range maximumHeight).reverse list.entries
where
  go : List Nat → List (Entry α β) → List (Entry α β)
    | [], entries => entries
    | index :: indices, entries =>
        go indices (advanceAtLevel key index entries)

/-- **Skip-list lookup.** The lookup of a key $k$ in a skip list computes the search window for
$k$, the suffix of the bottom-level nodes reached by descending from the highest level to level
$0$, and returns the value of the first node in the window whose key is $k$, or no value if the
window has no such node. -/
public def lookup {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (list : SkipList α β) : Option β :=
  ((searchWindow key list).map fun entry => (entry.key, entry.value)).lookup key

/-- **Skip-list insertion.** To insert key $k$ with value $v$ and requested height $h$ into a
skip list, scan its bottom-level nodes in order, keeping every node whose key is less than $k$.
At the first node whose key is not less than $k$: if its key equals $k$, its value is replaced
by $v$ and its tower height is kept; if its key is greater than $k$, a new node with key $k$,
value $v$ and tower height $\max(1, h)$ is placed before it. If every key is less than $k$, the
new node is appended at the end. -/
public def insert {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (value : β) (requestedHeight : Nat) (list : SkipList α β) : SkipList α β :=
  ⟨go list.entries⟩
where
  go : List (Entry α β) → List (Entry α β)
    | [] => [{ key, value, height := max 1 requestedHeight }]
    | entry :: entries =>
        if key < entry.key then
          { key, value, height := max 1 requestedHeight } :: entry :: entries
        else if entry.key < key then
          entry :: go entries
        else
          { entry with value := value } :: entries

/-- **The empty skip list is valid.** For every linearly ordered type $\alpha$ and every type
$\beta$, the empty skip list with keys in $\alpha$ and values in $\beta$ is valid. -/
public theorem valid_empty {α : Type u} {β : Type v} [LinearOrder α] :
    Valid (empty : SkipList α β) := by
  simp [Valid, empty]

/-- **Skip-list levels are sorted by key.** If a skip list is valid, then for every level index
$i$ (levels are numbered from $0$ at the bottom), the keys in the list of key-value pairs visible
at level $i$ are strictly increasing: every pair has a strictly smaller key than every pair after
it. -/
public theorem level_pairwise {α : Type u} {β : Type v} [LinearOrder α]
    {list : SkipList α β} (valid : Valid list) (index : Nat) :
    (level index list).Pairwise (fun left right => left.1 < right.1) := by
  rw [level, List.pairwise_map]
  exact valid.1.filter _

private theorem entriesAtLevel_succ_sublist {α : Type u} {β : Type v} (index : Nat)
    (entries : List (Entry α β)) :
    (entriesAtLevel (index + 1) entries).Sublist (entriesAtLevel index entries) := by
  induction entries with
  | nil => simp [entriesAtLevel]
  | cons entry entries ih =>
      by_cases high : index + 1 < entry.height
      · have low : index < entry.height := by omega
        simpa [entriesAtLevel, high, low] using ih.cons_cons entry
      · by_cases low : index < entry.height
        · simpa [entriesAtLevel, high, low] using ih.cons entry
        · simpa [entriesAtLevel, high, low] using ih

/-- **Each skip-list level is a subsequence of the level below.** For every skip list and every
level index $i$ (levels are numbered from $0$ at the bottom), the list of key-value pairs visible
at level $i + 1$ is a subsequence, not necessarily contiguous, of the list of key-value pairs
visible at level $i$. -/
public theorem level_succ_sublist_level {α : Type u} {β : Type v}
    (index : Nat) (list : SkipList α β) :
    (level (index + 1) list).Sublist (level index list) := by
  simpa [level, entriesAtLevel] using
    (entriesAtLevel_succ_sublist index list.entries).map
      (fun entry => (entry.key, entry.value))

/-- **Keys of a valid skip list are distinct.** If a skip list is valid, then the keys of the
pairs in its bottom-level abstraction, read in order, form a list without duplicates. -/
public theorem abstraction_keys_nodup {α : Type u} {β : Type v} [LinearOrder α]
    {list : SkipList α β} (valid : Valid list) :
    ((abstraction list).map Prod.fst).Nodup := by
  have ordered : list.entries.Pairwise (fun left right => left.key < right.key) := valid.1
  have keysOrdered : (list.entries.map Entry.key).Pairwise (· < ·) := by
    rwa [List.pairwise_map]
  rw [abstraction, List.map_map]
  have functionEquality :
      (Prod.fst ∘ fun entry : Entry α β => (entry.key, entry.value)) = Entry.key := by
    funext entry
    rfl
  rw [functionEquality]
  exact keysOrdered.nodup

/-- **Keys on each skip-list level are distinct.** If a skip list is valid, then for every level
index $i$ (levels are numbered from $0$ at the bottom), no key occurs twice in the list of
key-value pairs visible at level $i$. -/
public theorem level_keys_nodup {α : Type u} {β : Type v} [LinearOrder α]
    {list : SkipList α β} (valid : Valid list) (index : Nat) :
    ((level index list).map Prod.fst).Nodup := by
  have ordered := level_pairwise valid index
  have keysOrdered : ((level index list).map Prod.fst).Pairwise (· < ·) := by
    rwa [List.pairwise_map]
  exact keysOrdered.nodup

private theorem advanceAtLevel_go_some_suffix {α : Type u} {β : Type v}
    [LinearOrder α] (key : α) (index : Nat) {entries suffix : List (Entry α β)}
    (found : advanceAtLevel.go key index entries = some suffix) :
    suffix <:+ entries := by
  induction entries generalizing suffix with
  | nil => simp [advanceAtLevel.go] at found
  | cons entry entries ih =>
      rw [advanceAtLevel.go] at found
      by_cases before : entry.key < key
      · simp only [before, ite_true] at found
        cases scanned : advanceAtLevel.go key index entries with
        | none =>
            simp only [scanned] at found
            by_cases visible : index < entry.height
            · simp only [visible, ite_true] at found
              have suffix_eq : suffix = entries := (Option.some.inj found).symm
              rw [suffix_eq]
              simp
            · simp [visible] at found
        | some remaining =>
            simp only [scanned] at found
            have suffix_eq : suffix = remaining := (Option.some.inj found).symm
            rw [suffix_eq]
            exact (ih scanned).trans (by simp)
      · simp [before] at found

/-- **One search step returns a suffix.** For every search key, every level $i$ and every list
$L$ of skip-list nodes, advancing the search at level $i$ on $L$ returns a suffix of $L$. -/
public theorem advanceAtLevel_suffix {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (index : Nat) (entries : List (Entry α β)) :
    advanceAtLevel key index entries <:+ entries := by
  rw [advanceAtLevel]
  cases found : advanceAtLevel.go key index entries with
  | none => simp
  | some suffix =>
      simpa using advanceAtLevel_go_some_suffix key index found

private theorem searchWindow_go_suffix {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (indices : List Nat) (entries : List (Entry α β)) :
    searchWindow.go key indices entries <:+ entries := by
  induction indices generalizing entries with
  | nil => exact List.suffix_rfl
  | cons index indices ih =>
      exact (ih (advanceAtLevel key index entries)).trans
        (advanceAtLevel_suffix key index entries)

/-- **The search window is a suffix of the bottom level.** For every skip list and every key $k$,
the search window for $k$ is a suffix of the list of the skip list's bottom-level nodes. -/
public theorem searchWindow_suffix {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (list : SkipList α β) :
    searchWindow key list <:+ list.entries := by
  simpa [searchWindow] using
    searchWindow_go_suffix key
      (List.range (list.entries.foldl (fun result entry => max result entry.height) 0)).reverse
      list.entries

private theorem advanceAtLevel_go_some_lookup_eq {α : Type u} {β : Type v}
    [LinearOrder α] (key : α) (index : Nat) {entries suffix : List (Entry α β)}
    (found : advanceAtLevel.go key index entries = some suffix) :
    (suffix.map fun entry => (entry.key, entry.value)).lookup key =
      (entries.map fun entry => (entry.key, entry.value)).lookup key := by
  induction entries generalizing suffix with
  | nil => simp [advanceAtLevel.go] at found
  | cons entry entries ih =>
      rw [advanceAtLevel.go] at found
      by_cases before : entry.key < key
      · simp only [before, ite_true] at found
        have mismatch : (key == entry.key) = false := by simp [ne_of_gt before]
        rw [List.map_cons, List.lookup_cons]
        simp only [mismatch]
        cases scanned : advanceAtLevel.go key index entries with
        | none =>
            simp only [scanned] at found
            by_cases visible : index < entry.height
            · simp only [visible, ite_true] at found
              exact congrArg
                (fun remaining =>
                  (remaining.map fun entry => (entry.key, entry.value)).lookup key)
                (Option.some.inj found).symm
            · simp [visible] at found
        | some remaining =>
            simp only [scanned] at found
            have suffix_eq : suffix = remaining := (Option.some.inj found).symm
            rw [suffix_eq]
            exact ih scanned
      · simp [before] at found

private theorem advanceAtLevel_lookup_eq {α : Type u} {β : Type v}
    [LinearOrder α] (key : α) (index : Nat) (entries : List (Entry α β)) :
    ((advanceAtLevel key index entries).map fun entry => (entry.key, entry.value)).lookup key =
      (entries.map fun entry => (entry.key, entry.value)).lookup key := by
  rw [advanceAtLevel]
  cases found : advanceAtLevel.go key index entries with
  | none => simp
  | some suffix =>
      simpa using advanceAtLevel_go_some_lookup_eq key index found

private theorem searchWindow_go_lookup_eq {α : Type u} {β : Type v}
    [LinearOrder α] (key : α) (indices : List Nat) (entries : List (Entry α β)) :
    ((searchWindow.go key indices entries).map fun entry => (entry.key, entry.value)).lookup key =
      (entries.map fun entry => (entry.key, entry.value)).lookup key := by
  induction indices generalizing entries with
  | nil => rfl
  | cons index indices ih =>
      rw [searchWindow.go]
      exact (ih (advanceAtLevel key index entries)).trans
        (advanceAtLevel_lookup_eq key index entries)

/-- **Skip-list search agrees with bottom-level lookup.** For every skip list and every key $k$,
the top-down skip-list lookup of $k$ returns the same result as looking up $k$ in the
bottom-level abstraction, the list of key-value pairs of all stored nodes in order: the value of
the first pair with key $k$, or no value if there is none. -/
public theorem lookup_eq_abstraction {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (list : SkipList α β) :
    lookup key list = (abstraction list).lookup key := by
  simpa [lookup, searchWindow, abstraction] using
    searchWindow_go_lookup_eq key
      (List.range (list.entries.foldl (fun result entry => max result entry.height) 0)).reverse
      list.entries

private theorem all_lt_insert_go {α : Type u} {β : Type v} [LinearOrder α]
    {bound key : α} {value : β} {requestedHeight : Nat}
    {entries : List (Entry α β)} (bound_key : bound < key)
    (bound_entries : ∀ entry ∈ entries, bound < entry.key) :
    ∀ entry ∈ insert.go key value requestedHeight entries, bound < entry.key := by
  induction entries with
  | nil =>
      intro entry member
      simp only [insert.go, List.mem_singleton] at member
      subst entry
      exact bound_key
  | cons head entries ih =>
      have bound_head := bound_entries head (by simp)
      have bound_tail : ∀ entry ∈ entries, bound < entry.key := by
        intro entry member
        exact bound_entries entry (by simp [member])
      by_cases key_head : key < head.key
      · rw [insert.go]
        simp only [key_head, ite_true]
        intro entry member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | member
        · exact bound_key
        · exact bound_head
        · exact bound_tail entry member
      · by_cases head_key : head.key < key
        · rw [insert.go]
          simp only [key_head, ite_false, head_key, ite_true]
          intro entry member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact bound_head
          · exact ih bound_tail entry member
        · have key_eq : key = head.key :=
            le_antisymm (le_of_not_gt head_key) (le_of_not_gt key_head)
          rw [insert.go]
          simp only [key_head, ite_false, head_key, List.mem_cons]
          intro entry member
          rcases member with rfl | member
          · simpa [key_eq] using bound_entries head (by simp)
          · exact bound_entries entry (by simp [member])

private theorem pairwise_insert_go {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (value : β) (requestedHeight : Nat) (entries : List (Entry α β))
    (ordered : entries.Pairwise (fun left right => left.key < right.key)) :
    (insert.go key value requestedHeight entries).Pairwise
      (fun left right => left.key < right.key) := by
  induction entries with
  | nil => simp [insert.go]
  | cons head entries ih =>
      rw [List.pairwise_cons] at ordered
      by_cases key_head : key < head.key
      · rw [insert.go]
        simp only [key_head, ite_true, List.pairwise_cons]
        refine ⟨?_, ordered⟩
        intro entry member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact key_head
        · exact lt_trans key_head (ordered.1 entry member)
      · by_cases head_key : head.key < key
        · rw [insert.go]
          simp only [key_head, ite_false, head_key, ite_true, List.pairwise_cons]
          exact ⟨all_lt_insert_go head_key ordered.1, ih ordered.2⟩
        · have key_eq : key = head.key :=
            le_antisymm (le_of_not_gt head_key) (le_of_not_gt key_head)
          rw [insert.go]
          simp only [key_head, ite_false, head_key, List.pairwise_cons]
          simpa [key_eq] using ordered

private theorem heights_positive_insert_go {α : Type u} {β : Type v}
    [LinearOrder α] (key : α) (value : β) (requestedHeight : Nat)
    (entries : List (Entry α β))
    (positive : ∀ entry ∈ entries, 0 < entry.height) :
    ∀ entry ∈ insert.go key value requestedHeight entries, 0 < entry.height := by
  induction entries with
  | nil =>
      intro entry member
      simp only [insert.go, List.mem_singleton] at member
      subst entry
      exact Nat.zero_lt_of_ne_zero (by simp)
  | cons head entries ih =>
      have headPositive := positive head (by simp)
      have tailPositive : ∀ entry ∈ entries, 0 < entry.height := by
        intro entry member
        exact positive entry (by simp [member])
      by_cases key_head : key < head.key
      · rw [insert.go]
        simp only [key_head, ite_true]
        intro entry member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | member
        · exact Nat.zero_lt_of_ne_zero (by simp)
        · exact headPositive
        · exact tailPositive entry member
      · by_cases head_key : head.key < key
        · rw [insert.go]
          simp only [key_head, ite_false, head_key, ite_true]
          intro entry member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact headPositive
          · exact ih tailPositive entry member
        · rw [insert.go]
          simp only [key_head, ite_false, head_key, List.mem_cons]
          intro entry member
          rcases member with rfl | member
          · exact headPositive
          · exact tailPositive entry member

/-- **Insertion preserves skip-list validity.** Let $\alpha$ be a linearly ordered type and
$\beta$ a type. If a skip list with keys in $\alpha$ and values in $\beta$ is valid, then for every
key $k \in \alpha$, value $v \in \beta$ and requested height $h \in \mathbb{N}$ (including
$h = 0$), inserting $k$ with value $v$ and requested height $h$ yields a valid skip list. This
covers both a new key and a key already present, whose value is replaced. -/
public theorem valid_insert {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {value : β} {requestedHeight : Nat} {list : SkipList α β}
    (valid : Valid list) : Valid (insert key value requestedHeight list) := by
  exact ⟨pairwise_insert_go key value requestedHeight list.entries valid.1,
    heights_positive_insert_go key value requestedHeight list.entries valid.2⟩

private theorem abstraction_lookup_insert {α : Type u} {β : Type v}
    [LinearOrder α] (key : α) (value : β) (requestedHeight : Nat)
    (entries : List (Entry α β)) :
    ((insert.go key value requestedHeight entries).map
      (fun entry => (entry.key, entry.value))).lookup key = some value := by
  induction entries with
  | nil => simp [insert.go]
  | cons head entries ih =>
      by_cases key_head : key < head.key
      · rw [insert.go]
        simp only [key_head, ite_true, List.map_cons, List.lookup_cons]
        simp
      · by_cases head_key : head.key < key
        · have different : key ≠ head.key := ne_of_gt head_key
          rw [insert.go]
          simp only [key_head, ite_false, head_key, ite_true, List.map_cons,
            List.lookup_cons]
          have mismatch : (key == head.key) = false := by simp [different]
          simp only [mismatch]
          exact ih
        · have key_eq : key = head.key :=
            le_antisymm (le_of_not_gt head_key) (le_of_not_gt key_head)
          rw [insert.go]
          simp only [key_head, ite_false, head_key, List.map_cons, List.lookup_cons]
          simp [key_eq]

private theorem abstraction_lookup_insert_of_ne {α : Type u} {β : Type v}
    [LinearOrder α] (key other : α) (value : β) (requestedHeight : Nat)
    (entries : List (Entry α β)) (different : other ≠ key) :
    ((insert.go key value requestedHeight entries).map
      (fun entry => (entry.key, entry.value))).lookup other =
        (entries.map fun entry => (entry.key, entry.value)).lookup other := by
  induction entries with
  | nil => simp [insert.go, different]
  | cons head entries ih =>
      by_cases key_head : key < head.key
      · rw [insert.go]
        simp only [key_head, ite_true, List.map_cons, List.lookup_cons]
        have mismatch : (other == key) = false := by simp [different]
        simp only [mismatch]
      · by_cases head_key : head.key < key
        · rw [insert.go]
          simp only [key_head, ite_false, head_key, ite_true, List.map_cons,
            List.lookup_cons]
          rw [ih]
        · have key_eq : key = head.key :=
            le_antisymm (le_of_not_gt head_key) (le_of_not_gt key_head)
          rw [insert.go]
          simp only [key_head, ite_false, head_key, List.map_cons, List.lookup_cons]
          have other_ne_head : other ≠ head.key := by
            intro equal
            exact different (equal.trans key_eq.symm)
          have mismatch : (other == head.key) = false := by simp [other_ne_head]
          simp only [mismatch]

private theorem lookup_some_mem {α : Type u} {β : Type v}
    [BEq α] [LawfulBEq α] {key : α} {value : β} {entries : List (α × β)}
    (found : entries.lookup key = some value) : (key, value) ∈ entries := by
  rcases List.lookup_eq_some_iff.mp found with ⟨before, after, equation, _⟩
  rw [equation]
  simp

private theorem height_lookup_insert_go_of_present {α : Type u} {β : Type v}
    [LinearOrder α] (key : α) (value : β) (requestedHeight existingHeight : Nat)
    (entries : List (Entry α β))
    (ordered : entries.Pairwise (fun left right => left.key < right.key))
    (found : (entries.map fun entry => (entry.key, entry.height)).lookup key =
      some existingHeight) :
    ((insert.go key value requestedHeight entries).map
      (fun entry => (entry.key, entry.height))).lookup key = some existingHeight := by
  induction entries with
  | nil => simp at found
  | cons head entries ih =>
      rw [List.pairwise_cons] at ordered
      by_cases key_head : key < head.key
      · have mappedMember := lookup_some_mem found
        rcases List.mem_map.mp mappedMember with ⟨entry, entryMember, pairEquality⟩
        have entryKey : entry.key = key := congrArg Prod.fst pairEquality
        simp only [List.mem_cons] at entryMember
        rcases entryMember with rfl | entryMember
        · exact False.elim ((lt_irrefl key) (by simpa [entryKey] using key_head))
        · have head_entry : head.key < entry.key := ordered.1 entry entryMember
          exact False.elim (lt_asymm key_head (by simpa [entryKey] using head_entry))
      · by_cases head_key : head.key < key
        · have mismatch : (key == head.key) = false := by simp [ne_of_gt head_key]
          simp only [List.map_cons] at found
          rw [List.lookup_cons] at found
          simp only [mismatch] at found
          rw [insert.go]
          simp only [key_head, ite_false, head_key, ite_true, List.map_cons,
            List.lookup_cons, mismatch]
          exact ih ordered.2 found
        · have key_eq : key = head.key :=
            le_antisymm (le_of_not_gt head_key) (le_of_not_gt key_head)
          have keys_match : (key == head.key) = true := by simp [key_eq]
          simp only [List.map_cons] at found
          rw [List.lookup_cons] at found
          simp only [keys_match] at found
          have height_eq : head.height = existingHeight := Option.some.inj found
          rw [insert.go]
          simp only [key_head, ite_false, head_key, List.map_cons, List.lookup_cons, keys_match]
          exact congrArg some height_eq

/-- **Lookup after insertion returns the inserted value.** For every skip list, key $k$, value
$v$ and requested height $h$, looking up $k$ after inserting $k$ with value $v$ and requested
height $h$ returns $v$. -/
public theorem lookup_insert {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (value : β) (requestedHeight : Nat) (list : SkipList α β) :
    lookup key (insert key value requestedHeight list) = some value := by
  rw [lookup_eq_abstraction]
  exact abstraction_lookup_insert key value requestedHeight list.entries

/-- **Skip-list insertion does not change lookup of other keys.** Let $\alpha$ be a linearly
ordered type. For every skip list $S$ with keys in $\alpha$ and values in $\beta$, all keys $k$
and $k'$ in $\alpha$ with $k' \ne k$, every value $v \in \beta$ and every requested height
$h \in \mathbb{N}$, looking up $k'$ in the skip list obtained by inserting $k$ with value $v$ and
requested height $h$ into $S$ gives the same result as looking up $k'$ in $S$. -/
public theorem lookup_insert_of_ne {α : Type u} {β : Type v} [LinearOrder α]
    (key other : α) (value : β) (requestedHeight : Nat) (list : SkipList α β)
    (different : other ≠ key) :
    lookup other (insert key value requestedHeight list) = lookup other list := by
  rw [lookup_eq_abstraction, lookup_eq_abstraction]
  exact abstraction_lookup_insert_of_ne key other value requestedHeight list.entries different

private theorem height_lookup_insert_go_of_absent {α : Type u} {β : Type v}
    [LinearOrder α] (key : α) (value : β) (requestedHeight : Nat)
    (entries : List (Entry α β))
    (absent : (entries.map fun entry => (entry.key, entry.height)).lookup key =
      none) :
    ((insert.go key value requestedHeight entries).map
      (fun entry => (entry.key, entry.height))).lookup key =
        some (max 1 requestedHeight) := by
  induction entries with
  | nil => simp [insert.go]
  | cons head entries ih =>
      by_cases key_head : key < head.key
      · rw [insert.go]
        simp only [key_head, ite_true, List.map_cons, List.lookup_cons]
        simp
      · by_cases head_key : head.key < key
        · have mismatch : (key == head.key) = false := by simp [ne_of_gt head_key]
          simp only [List.map_cons] at absent
          rw [List.lookup_cons] at absent
          simp only [mismatch] at absent
          rw [insert.go]
          simp only [key_head, ite_false, head_key, ite_true, List.map_cons,
            List.lookup_cons, mismatch]
          exact ih absent
        · have key_eq : key = head.key :=
            le_antisymm (le_of_not_gt head_key) (le_of_not_gt key_head)
          have keys_match : (key == head.key) = true := by simp [key_eq]
          simp only [List.map_cons] at absent
          rw [List.lookup_cons] at absent
          simp only [keys_match] at absent
          simp at absent

/-- **Reinsertion preserves tower height.** Let $S$ be a valid skip list in which the key $k$
has stored tower height $h_0$. Then after inserting $k$ into $S$ with any value and any
requested height, the stored tower height of $k$ is still $h_0$. -/
public theorem heightOf_insert_of_present {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (value : β) (requestedHeight existingHeight : Nat)
    (list : SkipList α β) (valid : Valid list)
    (present : heightOf key list = some existingHeight) :
    heightOf key (insert key value requestedHeight list) = some existingHeight := by
  exact height_lookup_insert_go_of_present key value requestedHeight existingHeight
    list.entries valid.1 present
/-- **Height of a newly inserted key.** If a key $k$ does not occur in a skip list $S$, then
after inserting $k$ into $S$ with any value and requested height $h$, the stored tower height
of $k$ is $\max(1, h)$. -/
public theorem heightOf_insert_of_absent {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (value : β) (requestedHeight : Nat)
    (list : SkipList α β)
    (absent : heightOf key list = none) :
    heightOf key (insert key value requestedHeight list) =
      some (max 1 requestedHeight) := by
  exact height_lookup_insert_go_of_absent key value requestedHeight
    list.entries absent


end SkipList

end Cslib.Algorithms.Lean
