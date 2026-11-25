/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SkipList

/-!
# Skip-list erasure

Erasure traverses the ordered bottom-level entries and removes the matching stored tower.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

namespace SkipList

/-- **Skip-list erasure.** Given a key $k$ from a linearly ordered type and a skip list $S$, the
erasure of $k$ from $S$ is the skip list obtained by scanning the entries of $S$ in order: an
entry whose key is less than $k$ is kept and the scan continues; at the first entry whose key is
greater than $k$ the scan stops, and that entry and all later ones are kept; at the first entry
whose key equals $k$ that entry is removed, the scan stops, and all later entries are kept. Every
kept entry keeps its key, value and tower height. -/
public def erase {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (list : SkipList α β) : SkipList α β :=
  ⟨go list.entries⟩
where
  go : List (Entry α β) → List (Entry α β)
    | [] => []
    | entry :: entries =>
        if key < entry.key then
          entry :: entries
        else if entry.key < key then
          entry :: go entries
        else
          entries

/-- **Erasing from the empty skip list.** For every key $k$, erasing $k$ from the empty skip list
gives the empty skip list. -/
@[simp] public theorem erase_empty {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) : erase key (empty : SkipList α β) = empty := by
  rfl

/-- **Erasing a key below the first entry.** Let $e$ be a skip-list entry and $L$ a list of
entries. If a key $k$ is less than the key of $e$, then erasing $k$ from the skip list with entry
list $e$ followed by $L$ leaves the entry list $e$ followed by $L$ unchanged. -/
public theorem erase_cons_of_lt {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {entry : Entry α β} {entries : List (Entry α β)}
    (before : key < entry.key) :
    (erase key ⟨entry :: entries⟩).entries = entry :: entries := by
  simp [erase, erase.go, before]

/-- **Erasing past a smaller first entry.** Let $e$ be a skip-list entry and $L$ a list of
entries. If the key of $e$ is less than a key $k$, then erasing $k$ from the skip list with entry
list $e$ followed by $L$ gives the entry list consisting of $e$ followed by the entry list obtained
by erasing $k$ from the skip list with entry list $L$. -/
public theorem erase_cons_of_gt {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {entry : Entry α β} {entries : List (Entry α β)}
    (after : entry.key < key) :
    (erase key ⟨entry :: entries⟩).entries =
      entry :: (erase key ⟨entries⟩).entries := by
  simp [erase, erase.go, after, not_lt_of_ge (le_of_lt after)]

/-- **Erasing the key of the first entry.** Let $e$ be a skip-list entry and $L$ a list of
entries, and consider the skip list whose entry list is $e$ followed by $L$. If a key $k$ equals
the key of $e$, then erasing $k$ from this skip list leaves the entry list $L$. -/
public theorem erase_cons_of_eq {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {entry : Entry α β} {entries : List (Entry α β)}
    (matching : key = entry.key) :
    (erase key ⟨entry :: entries⟩).entries = entries := by
  subst key
  have neither : ¬entry.key < entry.key := lt_irrefl _
  simp [erase, erase.go, neither]

private theorem eraseEntries_eq_filter {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (entries : List (Entry α β))
    (ordered : entries.Pairwise (fun left right => left.key < right.key)) :
    erase.go key entries =
      entries.filter (fun entry => decide (entry.key ≠ key)) := by
  induction entries with
  | nil => simp [erase.go]
  | cons entry entries ih =>
      rw [List.pairwise_cons] at ordered
      by_cases before : key < entry.key
      · have allDifferent : ∀ candidate ∈ entry :: entries, candidate.key ≠ key := by
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact ne_of_gt before
          · exact ne_of_gt (lt_trans before (ordered.1 candidate member))
        have filtered :
            (entry :: entries).filter (fun candidate => decide (candidate.key ≠ key)) =
              entry :: entries := by
          apply List.filter_eq_self.mpr
          intro candidate member
          simp [allDifferent candidate member]
        rw [erase.go]
        simp only [before, ite_true]
        exact filtered.symm
      · by_cases after : entry.key < key
        · have different : entry.key ≠ key := ne_of_lt after
          rw [erase.go, List.filter_cons]
          have keep : decide (entry.key ≠ key) = true := by simp [different]
          simp only [before, ite_false, after, ite_true, keep]
          exact congrArg (List.cons entry) (ih ordered.2)
        · have matching : key = entry.key :=
            le_antisymm (le_of_not_gt after) (le_of_not_gt before)
          have allDifferent : ∀ candidate ∈ entries, candidate.key ≠ key := by
            intro candidate member
            have greater : key < candidate.key := by
              simpa [matching] using ordered.1 candidate member
            exact ne_of_gt greater
          have filtered :
              entries.filter (fun candidate => decide (candidate.key ≠ key)) = entries := by
            apply List.filter_eq_self.mpr
            intro candidate member
            simp [allDifferent candidate member]
          rw [erase.go, List.filter_cons]
          have drop : decide (entry.key ≠ key) = false := by simp [matching]
          simp only [before, ite_false, after, drop]
          exact filtered.symm

/-- **Erasure on a valid skip list filters out the key.** If $S$ is a valid skip list and $k$ is
a key, then the entry list of the skip list obtained by erasing $k$ from $S$ is the entry list of
$S$ with every entry whose key equals $k$ removed, the remaining entries kept in their order. -/
public theorem erase_entries_filter {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {list : SkipList α β} (valid : Valid list) :
    (erase key list).entries =
      list.entries.filter (fun entry => decide (entry.key ≠ key)) := by
  change erase.go key list.entries = _
  exact eraseEntries_eq_filter key list.entries valid.1

/-- **Erasure preserves skip-list validity.** Let $L$ be a valid skip list, that is, its keys are
strictly increasing and every stored tower has positive height. For every key $k$, the skip list
obtained from $L$ by erasing $k$ is again valid. -/
public theorem valid_erase {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {list : SkipList α β} (valid : Valid list) :
    Valid (erase key list) := by
  rw [Valid]
  constructor
  · rw [erase_entries_filter valid]
    exact valid.1.filter _
  · intro entry member
    rw [erase_entries_filter valid] at member
    exact valid.2 entry (List.mem_of_mem_filter member)

private theorem lookup_map_filter_eq_none {α : Type u} {β : Type v} {γ : Type*}
    [LinearOrder α] (key : α) (project : Entry α β → γ)
    (entries : List (Entry α β)) :
    ((entries.filter (fun entry => decide (entry.key ≠ key))).map
      (fun entry => (entry.key, project entry))).lookup key = none := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      by_cases matching : entry.key = key
      · rw [List.filter_cons]
        have drop : decide (entry.key ≠ key) = false := by simp [matching]
        simp only [drop]
        exact ih
      · rw [List.filter_cons]
        have keep : decide (entry.key ≠ key) = true := by simp [matching]
        have reverse : key ≠ entry.key := fun equal => matching equal.symm
        have mismatch : (key == entry.key) = false := by simp [reverse]
        simp only [keep, ite_true, List.map_cons, List.lookup_cons, mismatch]
        exact ih

private theorem lookup_map_filter_of_ne {α : Type u} {β : Type v} {γ : Type*}
    [LinearOrder α] (key other : α) (project : Entry α β → γ)
    (entries : List (Entry α β)) (different : other ≠ key) :
    ((entries.filter (fun entry => decide (entry.key ≠ key))).map
      (fun entry => (entry.key, project entry))).lookup other =
        (entries.map fun entry => (entry.key, project entry)).lookup other := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      by_cases matching : entry.key = key
      · rw [List.filter_cons]
        have drop : decide (entry.key ≠ key) = false := by simp [matching]
        have mismatch : (other == entry.key) = false := by simp [matching, different]
        simp only [drop, List.map_cons, List.lookup_cons, mismatch]
        exact ih
      · rw [List.filter_cons]
        have keep : decide (entry.key ≠ key) = true := by simp [matching]
        simp only [keep, ite_true, List.map_cons]
        by_cases found : other = entry.key
        · have keysMatch : (other == entry.key) = true := by simp [found]
          simp only [List.lookup_cons, keysMatch]
        · have keysDiffer : (other == entry.key) = false := by simp [found]
          simp only [List.lookup_cons, keysDiffer]
          exact ih

/-- **Erased keys are absent from a skip list.** Let $L$ be a valid skip list, that is, its keys
are strictly increasing and every stored tower has positive height. For every key $k$, looking
up $k$ in the skip list obtained from $L$ by erasing $k$ returns no value. -/
public theorem lookup_erase {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {list : SkipList α β} (valid : Valid list) :
    lookup key (erase key list) = none := by
  rw [lookup_eq_abstraction, abstraction, erase_entries_filter valid]
  exact lookup_map_filter_eq_none key (fun entry => entry.value) list.entries

/-- **Erasure preserves lookups of other keys.** If $S$ is a valid skip list and $k$, $k'$ are
keys with $k' \ne k$, then looking up $k'$ in the skip list obtained by erasing $k$ from $S$ gives
the same result as looking up $k'$ in $S$: the same value, or no value in both. -/
public theorem lookup_erase_of_ne {α : Type u} {β : Type v} [LinearOrder α]
    {key other : α} {list : SkipList α β} (valid : Valid list)
    (different : other ≠ key) :
    lookup other (erase key list) = lookup other list := by
  rw [lookup_eq_abstraction, lookup_eq_abstraction, abstraction, abstraction,
    erase_entries_filter valid]
  exact lookup_map_filter_of_ne key other (fun entry => entry.value) list.entries different

/-- **The erased key has no stored height.** If $S$ is a valid skip list and $k$ is a key, then
after erasing $k$ from $S$ the key $k$ has no stored tower height. -/
public theorem heightOf_erase {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {list : SkipList α β} (valid : Valid list) :
    heightOf key (erase key list) = none := by
  rw [heightOf, erase_entries_filter valid]
  exact lookup_map_filter_eq_none key (fun entry => entry.height) list.entries

/-- **Erasure preserves the heights of other keys.** If $S$ is a valid skip list and $k$, $k'$
are keys with $k' \ne k$, then the stored tower height of $k'$ in the skip list obtained by
erasing $k$ from $S$ is the same as in $S$; in particular $k'$ has no stored height in one exactly
when it has none in the other. -/
public theorem heightOf_erase_of_ne {α : Type u} {β : Type v} [LinearOrder α]
    {key other : α} {list : SkipList α β} (valid : Valid list)
    (different : other ≠ key) :
    heightOf other (erase key list) = heightOf other list := by
  rw [heightOf, heightOf, erase_entries_filter valid]
  exact lookup_map_filter_of_ne key other (fun entry => entry.height) list.entries different

private theorem level_filter_ne {α : Type u} {β : Type v} [DecidableEq α]
    (key : α) (index : Nat) (entries : List (Entry α β)) :
    (((entries.filter (fun entry => decide (entry.key ≠ key))).filter
      (fun entry => index < entry.height)).map fun entry => (entry.key, entry.value)) =
      ((entries.filter (fun entry => index < entry.height)).map
        fun entry => (entry.key, entry.value)).filter
          (fun pair => decide (pair.1 ≠ key)) := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      by_cases matching : entry.key = key
      · have drop : decide (entry.key ≠ key) = false := by simp [matching]
        by_cases visible : index < entry.height
        · have visibleTrue : decide (index < entry.height) = true := by simp [visible]
          have pairDrop : decide ((entry.key, entry.value).1 ≠ key) = false := by
            simp [matching]
          simpa only [List.filter_cons, drop, visibleTrue, pairDrop,
            Bool.false_eq_true, ite_false, ite_true, List.map_cons] using ih
        · have visibleFalse : decide (index < entry.height) = false := by simp [visible]
          simpa only [List.filter_cons, drop, visibleFalse, Bool.false_eq_true,
            ite_false, List.map_cons] using ih
      · by_cases visible : index < entry.height
        · have keep : decide (entry.key ≠ key) = true := by simp [matching]
          have visibleTrue : decide (index < entry.height) = true := by simp [visible]
          have pairKeep : decide ((entry.key, entry.value).1 ≠ key) = true := by
            simp [matching]
          simpa only [List.filter_cons, keep, visibleTrue, pairKeep,
            ite_true, List.map_cons] using
              congrArg (List.cons (entry.key, entry.value)) ih
        · have keep : decide (entry.key ≠ key) = true := by simp [matching]
          have visibleFalse : decide (index < entry.height) = false := by simp [visible]
          simpa only [List.filter_cons, keep, visibleFalse, Bool.false_eq_true,
            ite_false, ite_true, List.map_cons] using ih

/-- **Erasure removes the key from every level.** If $S$ is a valid skip list, $k$ is a key and
$i$ is a natural number, then the level-$i$ list of key-value pairs (levels numbered from $0$) of
the skip list obtained by erasing $k$ from $S$ is the level-$i$ list of $S$ with every pair whose
key equals $k$ removed, the remaining pairs kept in their order. -/
public theorem level_erase {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {list : SkipList α β} (valid : Valid list) (index : Nat) :
    level index (erase key list) =
      (level index list).filter (fun pair => decide (pair.1 ≠ key)) := by
  simpa [level, erase_entries_filter valid] using level_filter_ne key index list.entries

end SkipList

end Cslib.Algorithms.Lean
