/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Radix tries (Patricia tries)

A radix trie compresses a trie by labelling edges with nonempty lists instead of single
symbols (La Rocca, *Advanced Algorithms and Data Structures*, ch. 6). A node stores an
optional value, so a key may end at an internal node, together with a list of
`(label, subtree)` children. In a valid trie every label is nonempty, first symbols of
sibling labels are distinct, every subtree is valid, and every non-root node is
path-compressed: a node storing no value has at least two children, so no unary
value-free node could be merged into its parent edge. Lookup follows the child whose
label starts with the next key symbol and requires the whole label to be a prefix of the
remaining key. Insertion walks to the edge sharing the key's first symbol and splits that
edge at the longest common prefix of key and label: if both continue past the common
prefix, a new internal node with no value branches to the old subtree and a new leaf.
Children use a raw association list because Lean cannot nest recursively valued tries in
`AList`; `Valid` records the invariant. The abstraction is `entries`, the flattened
key-value list in stored sibling order, and lookup is characterized against it for valid
tries. No complexity bounds are proved.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

/-- A radix trie from list keys over `α` to values in `β`, with list-labelled edges. -/
inductive RadixTrie (α : Type u) (β : Type v) where
  | node : Option β → List (List α × RadixTrie α β) → RadixTrie α β

namespace RadixTrie

/-- The trie containing no key-value entries. -/
def empty {α : Type u} {β : Type v} : RadixTrie α β :=
  .node none []

/-- The longest common prefix of two lists. -/
def commonPrefix {α : Type u} [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: xs, b :: ys => if a = b then a :: commonPrefix xs ys else []

theorem commonPrefix_nil_left {α : Type u} [DecidableEq α] (ys : List α) :
    commonPrefix [] ys = [] :=
  rfl

theorem commonPrefix_nil_right {α : Type u} [DecidableEq α] (xs : List α) :
    commonPrefix xs [] = [] := by
  cases xs <;> rfl

theorem commonPrefix_cons_cons {α : Type u} [DecidableEq α] (a : α) (xs : List α)
    (b : α) (ys : List α) :
    commonPrefix (a :: xs) (b :: ys) =
      if a = b then a :: commonPrefix xs ys else [] :=
  rfl

/-- The longest common prefix of a list with itself is the list. -/
theorem commonPrefix_self {α : Type u} [DecidableEq α] (xs : List α) :
    commonPrefix xs xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [commonPrefix, ih]

/-- A shared prefix factors out of the longest common prefix. -/
theorem commonPrefix_append_append {α : Type u} [DecidableEq α]
    (P xs ys : List α) :
    commonPrefix (P ++ xs) (P ++ ys) = P ++ commonPrefix xs ys := by
  induction P with
  | nil => rfl
  | cons p P ih =>
      show commonPrefix (p :: (P ++ xs)) (p :: (P ++ ys)) =
        p :: (P ++ commonPrefix xs ys)
      rw [commonPrefix_cons_cons, ite_eq_left rfl, ih]

/--
Both lists extend their longest common prefix, and the remainders are the reason the
prefix is longest: one is empty, or their heads differ.
-/
theorem commonPrefix_spec {α : Type u} [DecidableEq α] (xs ys : List α) :
    ∃ xs' ys', xs = commonPrefix xs ys ++ xs' ∧ ys = commonPrefix xs ys ++ ys' ∧
      (xs' = [] ∨ ys' = [] ∨
        ∃ x xs'' y ys'', xs' = x :: xs'' ∧ ys' = y :: ys'' ∧ x ≠ y) := by
  induction xs generalizing ys with
  | nil => exact ⟨[], ys, rfl, rfl, Or.inl rfl⟩
  | cons x xs ih =>
      cases ys with
      | nil => exact ⟨x :: xs, [], rfl, rfl, Or.inr (Or.inl rfl)⟩
      | cons y ys =>
          by_cases h : x = y
          · subst y
            obtain ⟨xs', ys', hxs, hys, hdiv⟩ := ih ys
            exact ⟨xs', ys',
              by rw [commonPrefix_cons_cons, ite_eq_left rfl, List.cons_append,
                ← hxs],
              by rw [commonPrefix_cons_cons, ite_eq_left rfl, List.cons_append,
                ← hys], hdiv⟩
          · exact ⟨x :: xs, y :: ys,
              by rw [commonPrefix_cons_cons, ite_eq_right h, List.nil_append],
              by rw [commonPrefix_cons_cons, ite_eq_right h, List.nil_append],
              Or.inr (Or.inr ⟨x, xs, y, ys, rfl, rfl, h⟩)⟩

/-- A list is its longest common prefix with another list, followed by the drop remainder. -/
theorem append_drop_commonPrefix_left {α : Type u} [DecidableEq α]
    (xs ys : List α) :
    xs = commonPrefix xs ys ++ xs.drop (commonPrefix xs ys).length := by
  obtain ⟨xs', -, hxs, -, -⟩ := commonPrefix_spec xs ys
  generalize hP : commonPrefix xs ys = P
  rw [hP] at hxs
  rw [hxs, List.drop_append_length]

/-- The longest-common-prefix decomposition, stated with the drop remainders. -/
theorem commonPrefix_drop_spec {α : Type u} [DecidableEq α] (xs ys : List α) :
    xs = commonPrefix xs ys ++ xs.drop (commonPrefix xs ys).length ∧
      ys = commonPrefix xs ys ++ ys.drop (commonPrefix xs ys).length ∧
      (xs.drop (commonPrefix xs ys).length = [] ∨
        ys.drop (commonPrefix xs ys).length = [] ∨
        ∃ x xs'' y ys'', xs.drop (commonPrefix xs ys).length = x :: xs'' ∧
          ys.drop (commonPrefix xs ys).length = y :: ys'' ∧ x ≠ y) := by
  obtain ⟨xs', ys', hxs, hys, hdiv⟩ := commonPrefix_spec xs ys
  generalize hP : commonPrefix xs ys = P
  rw [hP] at hxs hys
  have hdx : xs.drop P.length = xs' := by
    rw [hxs, List.drop_append_length]
  have hdy : ys.drop P.length = ys' := by
    rw [hys, List.drop_append_length]
  rw [hdx, hdy]
  exact ⟨hxs, hys, hdiv⟩

/-- If the longest common prefix is the whole second list, the first extends it. -/
theorem append_of_commonPrefix_eq {α : Type u} [DecidableEq α] {xs ys : List α}
    (h : commonPrefix xs ys = ys) : xs = ys ++ xs.drop ys.length := by
  have h1 := append_drop_commonPrefix_left xs ys
  rw [h] at h1
  exact h1

/-- If the first list extends the second, the longest common prefix is the second. -/
theorem commonPrefix_eq_of_append {α : Type u} [DecidableEq α] {xs ys t : List α}
    (h : xs = ys ++ t) : commonPrefix xs ys = ys := by
  have h2 := commonPrefix_append_append ys t ([] : List α)
  simp only [commonPrefix_nil_right, List.append_nil] at h2
  rw [h]
  exact h2

/-- Returns the first child edge whose label starts with `c`, if any. -/
def findEdge {α : Type u} {β : Type v} [DecidableEq α] (c : α) :
    List (List α × RadixTrie α β) → Option (List α × RadixTrie α β)
  | [] => none
  | (label, child) :: rest =>
      if label.head? = some c then some (label, child) else findEdge c rest

theorem findEdge_nil {α : Type u} {β : Type v} [DecidableEq α] (c : α) :
    findEdge c ([] : List (List α × RadixTrie α β)) = none :=
  rfl

theorem findEdge_cons {α : Type u} {β : Type v} [DecidableEq α] (c : α)
    (label : List α) (child : RadixTrie α β)
    (rest : List (List α × RadixTrie α β)) :
    findEdge c ((label, child) :: rest) =
      if label.head? = some c then some (label, child) else findEdge c rest :=
  rfl

theorem findEdge_some_head {α : Type u} {β : Type v} [DecidableEq α] {c : α}
    {children : List (List α × RadixTrie α β)} {label : List α}
    {child : RadixTrie α β}
    (h : findEdge c children = some (label, child)) : label.head? = some c := by
  induction children with
  | nil => simp [findEdge] at h
  | cons head rest ih =>
      rcases head with ⟨label', child'⟩
      by_cases hh : label'.head? = some c
      · simp [findEdge, hh] at h
        obtain ⟨h1, -⟩ := h
        rw [← h1]
        exact hh
      · simp [findEdge, hh] at h
        exact ih h

theorem findEdge_some_mem {α : Type u} {β : Type v} [DecidableEq α] {c : α}
    {children : List (List α × RadixTrie α β)} {label : List α}
    {child : RadixTrie α β}
    (h : findEdge c children = some (label, child)) :
    (label, child) ∈ children := by
  induction children with
  | nil => simp [findEdge] at h
  | cons head rest ih =>
      rcases head with ⟨label', child'⟩
      by_cases hh : label'.head? = some c
      · simp [findEdge, hh] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
      · simp [findEdge, hh] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem findEdge_eq_none_imp {α : Type u} {β : Type v} [DecidableEq α] {c : α}
    {children : List (List α × RadixTrie α β)}
    (h : findEdge c children = none) :
    ∀ e ∈ children, e.1.head? ≠ some c := by
  induction children with
  | nil =>
      intro e he
      simp at he
  | cons head rest ih =>
      rcases head with ⟨label', child'⟩
      by_cases hh : label'.head? = some c
      · simp [findEdge, hh] at h
      · simp [findEdge, hh] at h
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hh
        · exact ih h e he

/--
Replaces the first child edge whose label starts with `c` by `newEdge`, appending
`newEdge` at the end when there is no such edge.
-/
def replaceEdge {α : Type u} {β : Type v} [DecidableEq α] (c : α)
    (newEdge : List α × RadixTrie α β) :
    List (List α × RadixTrie α β) → List (List α × RadixTrie α β)
  | [] => [newEdge]
  | (label, child) :: rest =>
      if label.head? = some c then newEdge :: rest
      else (label, child) :: replaceEdge c newEdge rest

theorem replaceEdge_nil {α : Type u} {β : Type v} [DecidableEq α] (c : α)
    (newEdge : List α × RadixTrie α β) :
    replaceEdge c newEdge ([] : List (List α × RadixTrie α β)) = [newEdge] :=
  rfl

theorem replaceEdge_cons {α : Type u} {β : Type v} [DecidableEq α] (c : α)
    (newEdge : List α × RadixTrie α β) (label : List α) (child : RadixTrie α β)
    (rest : List (List α × RadixTrie α β)) :
    replaceEdge c newEdge ((label, child) :: rest) =
      if label.head? = some c then newEdge :: rest
      else (label, child) :: replaceEdge c newEdge rest :=
  rfl

theorem findEdge_replaceEdge_same {α : Type u} {β : Type v} [DecidableEq α]
    {c : α} {newEdge : List α × RadixTrie α β}
    (hhead : newEdge.1.head? = some c)
    (children : List (List α × RadixTrie α β)) :
    findEdge c (replaceEdge c newEdge children) = some newEdge := by
  rcases newEdge with ⟨nlabel, nchild⟩
  have hhead' : nlabel.head? = some c := hhead
  induction children with
  | nil => rw [replaceEdge_nil, findEdge_cons, ite_eq_left hhead']
  | cons head rest ih =>
      rcases head with ⟨label, child⟩
      by_cases hh : label.head? = some c
      · rw [replaceEdge_cons, ite_eq_left hh, findEdge_cons, ite_eq_left hhead']
      · rw [replaceEdge_cons, ite_eq_right hh, findEdge_cons, ite_eq_right hh, ih]

theorem findEdge_replaceEdge_ne {α : Type u} {β : Type v} [DecidableEq α]
    {c c' : α} (h : c' ≠ c) {newEdge : List α × RadixTrie α β}
    (hhead : newEdge.1.head? = some c)
    (children : List (List α × RadixTrie α β)) :
    findEdge c' (replaceEdge c newEdge children) = findEdge c' children := by
  rcases newEdge with ⟨nlabel, nchild⟩
  have hhead' : nlabel.head? = some c := hhead
  have hne : nlabel.head? ≠ some c' := by
    rw [hhead']
    exact fun hEq => h (Option.some.inj hEq).symm
  induction children with
  | nil => rw [replaceEdge_nil, findEdge_cons, ite_eq_right hne]
  | cons head rest ih =>
      rcases head with ⟨label, child⟩
      by_cases hh : label.head? = some c
      · have hh' : label.head? ≠ some c' := by
          rw [hh]
          exact fun hEq => h (Option.some.inj hEq).symm
        rw [replaceEdge_cons, ite_eq_left hh, findEdge_cons, ite_eq_right hne,
          findEdge_cons, ite_eq_right hh']
      · by_cases hh' : label.head? = some c'
        · rw [replaceEdge_cons, ite_eq_right hh, findEdge_cons, ite_eq_left hh',
            findEdge_cons, ite_eq_left hh']
        · rw [replaceEdge_cons, ite_eq_right hh, findEdge_cons, ite_eq_right hh',
            findEdge_cons, ite_eq_right hh', ih]

private theorem exists_cons_of_head?_eq_some {α : Type u} {label : List α} {c : α}
    (h : label.head? = some c) : ∃ ls, label = c :: ls := by
  cases label with
  | nil => simp at h
  | cons x xs =>
      have hx : x = c := by
        have h2 := h
        simp only [List.head?_cons, Option.some.injEq] at h2
        exact h2
      exact ⟨xs, by rw [hx]⟩

/-- Looks up a list key in a radix trie. -/
def lookup {α : Type u} {β : Type v} [DecidableEq α] :
    RadixTrie α β → List α → Option β
  | .node value _, [] => value
  | .node _ children, key@(_ :: _) => lookupChildren children key
where
  lookupChildren : List (List α × RadixTrie α β) → List α → Option β
    | [], _ => none
    | (label, child) :: rest, key@(c :: _) =>
        if label.head? = some c then
          if commonPrefix key label = label then
            lookup child (key.drop label.length)
          else none
        else lookupChildren rest key
    | _ :: _, [] => none

@[simp]
theorem lookup_nil {α : Type u} {β : Type v} [DecidableEq α] (value : Option β)
    (children : List (List α × RadixTrie α β)) :
    lookup (.node value children) ([] : List α) = value :=
  rfl

private theorem lookupChildren_eq_findEdge {α : Type u} {β : Type v}
    [DecidableEq α] (children : List (List α × RadixTrie α β)) (c : α)
    (ks : List α) :
    lookup.lookupChildren children (c :: ks) =
      match findEdge c children with
      | none => none
      | some (label, child) =>
          if commonPrefix (c :: ks) label = label then
            lookup child ((c :: ks).drop label.length)
          else none := by
  induction children with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨label, child⟩
      by_cases hh : label.head? = some c
      · simp [lookup.lookupChildren, findEdge, hh]
      · simp [lookup.lookupChildren, findEdge, hh, ih]

/--
Lookup of a nonempty key follows the first edge whose label starts with the key's
head, and continues below it only when the whole label prefixes the key.
-/
theorem lookup_node_cons {α : Type u} {β : Type v} [DecidableEq α]
    (value : Option β) (children : List (List α × RadixTrie α β)) (c : α)
    (ks : List α) :
    lookup (.node value children) (c :: ks) =
      match findEdge c children with
      | none => none
      | some (label, child) =>
          if commonPrefix (c :: ks) label = label then
            lookup child ((c :: ks).drop label.length)
          else none :=
  lookupChildren_eq_findEdge children c ks

/-- Every lookup in the empty trie fails. -/
@[simp]
theorem lookup_empty {α : Type u} {β : Type v} [DecidableEq α]
    (keys : List α) : (empty : RadixTrie α β).lookup keys = none := by
  cases keys <;> simp [empty, lookup_node_cons, findEdge]

private theorem lookup_leaf {α : Type u} {β : Type v} [DecidableEq α] (v : β)
    (keys : List α) :
    lookup (.node (some v) [] : RadixTrie α β) keys =
      if keys = [] then some v else none := by
  cases keys <;> simp [lookup_node_cons, findEdge]

/--
Inserts or replaces the value at a list key. At a node, insertion finds the child edge
whose label shares the key's first symbol and splits it at the longest common prefix of
key and label: an exhausted key ends at a new internal node above the old subtree, an
exhausted label continues into the subtree, and two nonempty remainders branch at a new
internal node with no value.
-/
def insert {α : Type u} {β : Type v} [DecidableEq α]
    (trie : RadixTrie α β) (key : List α) (value : β) : RadixTrie α β :=
  match trie, key with
  | .node _ children, [] => .node (some value) children
  | .node current children, (c :: ks) =>
      match _hfind : findEdge c children with
      | none => .node current (replaceEdge c ((c :: ks), .node (some value) []) children)
      | some (label, child) =>
          if (c :: ks).drop (commonPrefix (c :: ks) label).length = [] then
            if label.drop (commonPrefix (c :: ks) label).length = [] then
              .node current (replaceEdge c (label, child.insert [] value) children)
            else
              .node current (replaceEdge c
                (commonPrefix (c :: ks) label,
                  .node (some value)
                    [(label.drop (commonPrefix (c :: ks) label).length, child)])
                children)
          else if label.drop (commonPrefix (c :: ks) label).length = [] then
            .node current (replaceEdge c
              (label, child.insert
                ((c :: ks).drop (commonPrefix (c :: ks) label).length) value)
              children)
          else
            .node current (replaceEdge c
              (commonPrefix (c :: ks) label,
                .node none
                  [(label.drop (commonPrefix (c :: ks) label).length, child),
                    ((c :: ks).drop (commonPrefix (c :: ks) label).length,
                      .node (some value) [])])
              children)
termination_by key.length
decreasing_by
  all_goals
    have hhead := findEdge_some_head _hfind
    obtain ⟨ls, rfl⟩ := exists_cons_of_head?_eq_some hhead
    have hcp : commonPrefix (c :: ks) (c :: ls) = c :: commonPrefix ks ls := by
      rw [commonPrefix_cons_cons, ite_eq_left rfl]
    simp only [List.length_drop, hcp, List.length_cons, List.length_nil]
    omega

theorem insert_nil {α : Type u} {β : Type v} [DecidableEq α] (current : Option β)
    (children : List (List α × RadixTrie α β)) (value : β) :
    insert (.node current children) [] value = .node (some value) children := by
  unfold insert
  rfl

theorem insert_cons_none {α : Type u} {β : Type v} [DecidableEq α]
    (current : Option β) (children : List (List α × RadixTrie α β)) (c : α)
    (ks : List α) (value : β) (hfind : findEdge c children = none) :
    insert (.node current children) (c :: ks) value =
      .node current (replaceEdge c ((c :: ks), .node (some value) []) children) := by
  simp only [insert]
  rw [hfind]

theorem insert_cons_some_nil_nil {α : Type u} {β : Type v} [DecidableEq α]
    (current : Option β) (children : List (List α × RadixTrie α β)) (c : α)
    (ks : List α) (value : β) (label : List α) (child : RadixTrie α β)
    (hfind : findEdge c children = some (label, child))
    (hk : (c :: ks).drop (commonPrefix (c :: ks) label).length = [])
    (hl : label.drop (commonPrefix (c :: ks) label).length = []) :
    insert (.node current children) (c :: ks) value =
      .node current (replaceEdge c (label, child.insert [] value) children) := by
  simp only [insert]
  rw [hfind]
  dsimp only
  rw [ite_eq_left hk, ite_eq_left hl]

theorem insert_cons_some_nil_cons {α : Type u} {β : Type v} [DecidableEq α]
    (current : Option β) (children : List (List α × RadixTrie α β)) (c : α)
    (ks : List α) (value : β) (label : List α) (child : RadixTrie α β)
    (hfind : findEdge c children = some (label, child))
    (hk : (c :: ks).drop (commonPrefix (c :: ks) label).length = [])
    (hl : label.drop (commonPrefix (c :: ks) label).length ≠ []) :
    insert (.node current children) (c :: ks) value =
      .node current (replaceEdge c
        (commonPrefix (c :: ks) label,
          .node (some value)
            [(label.drop (commonPrefix (c :: ks) label).length, child)])
        children) := by
  simp only [insert]
  rw [hfind]
  dsimp only
  rw [ite_eq_left hk, ite_eq_right hl]

theorem insert_cons_some_cons_nil {α : Type u} {β : Type v} [DecidableEq α]
    (current : Option β) (children : List (List α × RadixTrie α β)) (c : α)
    (ks : List α) (value : β) (label : List α) (child : RadixTrie α β)
    (hfind : findEdge c children = some (label, child))
    (hk : (c :: ks).drop (commonPrefix (c :: ks) label).length ≠ [])
    (hl : label.drop (commonPrefix (c :: ks) label).length = []) :
    insert (.node current children) (c :: ks) value =
      .node current (replaceEdge c
        (label, child.insert ((c :: ks).drop (commonPrefix (c :: ks) label).length)
          value)
        children) := by
  simp only [insert]
  rw [hfind]
  dsimp only
  rw [ite_eq_right hk, ite_eq_left hl]

theorem insert_cons_some_cons_cons {α : Type u} {β : Type v} [DecidableEq α]
    (current : Option β) (children : List (List α × RadixTrie α β)) (c : α)
    (ks : List α) (value : β) (label : List α) (child : RadixTrie α β)
    (hfind : findEdge c children = some (label, child))
    (hk : (c :: ks).drop (commonPrefix (c :: ks) label).length ≠ [])
    (hl : label.drop (commonPrefix (c :: ks) label).length ≠ []) :
    insert (.node current children) (c :: ks) value =
      .node current (replaceEdge c
        (commonPrefix (c :: ks) label,
          .node none
            [(label.drop (commonPrefix (c :: ks) label).length, child),
              ((c :: ks).drop (commonPrefix (c :: ks) label).length,
                .node (some value) [])])
        children) := by
  simp only [insert]
  rw [hfind]
  dsimp only
  rw [ite_eq_right hk, ite_eq_right hl]

/-- Looking up an inserted key returns its new value. -/
@[simp]
theorem lookup_insert_same {α : Type u} {β : Type v} [DecidableEq α]
    (trie : RadixTrie α β) (keys : List α) (value : β) :
    (trie.insert keys value).lookup keys = some value := by
  induction hlen : keys.length using Nat.strongRecOn generalizing trie keys with
  | _ n ih =>
      cases keys with
      | nil =>
          cases trie with
          | node current children => simp [insert_nil]
      | cons c ks =>
          cases trie with
          | node current children =>
              cases hfind : findEdge c children with
              | none =>
                  rw [insert_cons_none current children c ks value hfind,
                    lookup_node_cons,
                    findEdge_replaceEdge_same
                      (newEdge := ((c :: ks), .node (some value) [])) (by rfl)
                      children]
                  show (if commonPrefix (c :: ks) (c :: ks) = (c :: ks) then
                      lookup (.node (some value) []) ((c :: ks).drop (c :: ks).length)
                    else none) = some value
                  rw [commonPrefix_self, ite_eq_left rfl,
                    List.drop_of_length_le (Nat.le_refl _), lookup_nil]
              | some edge =>
                  rcases edge with ⟨label, child⟩
                  have hhead := findEdge_some_head hfind
                  obtain ⟨ls, rfl⟩ := exists_cons_of_head?_eq_some hhead
                  have hcp : commonPrefix (c :: ks) (c :: ls) =
                      c :: commonPrefix ks ls := by
                    rw [commonPrefix_cons_cons, ite_eq_left rfl]
                  have hPhead : (commonPrefix (c :: ks) (c :: ls)).head? =
                      some c := by
                    simp only [hcp, List.head?_cons]
                  obtain ⟨hkey, hlabel, hdiv⟩ :=
                    commonPrefix_drop_spec (c :: ks) (c :: ls)
                  cases hK : (c :: ks).drop
                      (commonPrefix (c :: ks) (c :: ls)).length with
                  | nil =>
                      cases hL : (c :: ls).drop
                          (commonPrefix (c :: ks) (c :: ls)).length with
                      | nil =>
                          have e1 : (c :: ks) =
                              commonPrefix (c :: ks) (c :: ls) := by
                            have h2 := hkey
                            rw [hK, List.append_nil] at h2
                            exact h2
                          have e2 : (c :: ls) =
                              commonPrefix (c :: ks) (c :: ls) := by
                            have h2 := hlabel
                            rw [hL, List.append_nil] at h2
                            exact h2
                          rw [insert_cons_some_nil_nil current children c ks
                              value (c :: ls) child hfind hK hL,
                            lookup_node_cons,
                            findEdge_replaceEdge_same
                              (newEdge := ((c :: ls), child.insert [] value))
                              (findEdge_some_head hfind) children]
                          show (if commonPrefix (c :: ks) (c :: ls) = (c :: ls)
                              then lookup (child.insert [] value)
                                ((c :: ks).drop (c :: ls).length)
                            else none) = some value
                          rw [ite_eq_left e2.symm,
                            show (c :: ks) = (c :: ls) from e1.trans e2.symm,
                            List.drop_of_length_le (Nat.le_refl _)]
                          cases child with
                          | node cv cch => rw [insert_nil, lookup_nil]
                      | cons l ls' =>
                          have hLne : (c :: ls).drop
                              (commonPrefix (c :: ks) (c :: ls)).length ≠ [] := by
                            simp [hL]
                          rw [insert_cons_some_nil_cons current children c ks
                              value (c :: ls) child hfind hK hLne, hL,
                            lookup_node_cons,
                            findEdge_replaceEdge_same
                              (newEdge := (commonPrefix (c :: ks) (c :: ls),
                                .node (some value) [(l :: ls', child)]))
                              hPhead children]
                          show (if commonPrefix (c :: ks)
                                (commonPrefix (c :: ks) (c :: ls)) =
                                commonPrefix (c :: ks) (c :: ls)
                              then lookup (.node (some value) [(l :: ls', child)])
                                ((c :: ks).drop
                                  (commonPrefix (c :: ks) (c :: ls)).length)
                            else none) = some value
                          rw [ite_eq_left (commonPrefix_eq_of_append hkey), hK,
                            lookup_nil]
                  | cons k' ks' =>
                      cases hL : (c :: ls).drop
                          (commonPrefix (c :: ks) (c :: ls)).length with
                      | nil =>
                          have hKne : (c :: ks).drop
                              (commonPrefix (c :: ks) (c :: ls)).length ≠ [] := by
                            simp [hK]
                          have e2 : (c :: ls) =
                              commonPrefix (c :: ks) (c :: ls) := by
                            have h2 := hlabel
                            rw [hL, List.append_nil] at h2
                            exact h2
                          have hlt : ((c :: ks).drop (c :: ls).length).length <
                              n := by
                            have h3 : (c :: ls).length =
                                (commonPrefix ks ls).length + 1 := by
                              have h4 := congrArg List.length e2
                              rw [hcp] at h4
                              simp only [List.length_cons] at h4 ⊢
                              omega
                            have h5 : 0 < (c :: ks).length := by
                              rw [List.length_cons]
                              omega
                            rw [← hlen, List.length_drop]
                            omega
                          rw [insert_cons_some_cons_nil current children c ks
                              value (c :: ls) child hfind hKne hL,
                            lookup_node_cons,
                            findEdge_replaceEdge_same
                              (newEdge := ((c :: ls), child.insert
                                ((c :: ks).drop
                                  (commonPrefix (c :: ks) (c :: ls)).length)
                                value))
                              (findEdge_some_head hfind) children]
                          show (if commonPrefix (c :: ks) (c :: ls) = (c :: ls)
                              then lookup (child.insert
                                  ((c :: ks).drop
                                    (commonPrefix (c :: ks) (c :: ls)).length)
                                  value)
                                ((c :: ks).drop (c :: ls).length)
                            else none) = some value
                          rw [ite_eq_left e2.symm, ← e2]
                          exact ih _ hlt child _ rfl
                      | cons l ls' =>
                          have hKne : (c :: ks).drop
                              (commonPrefix (c :: ks) (c :: ls)).length ≠ [] := by
                            simp [hK]
                          have hLne : (c :: ls).drop
                              (commonPrefix (c :: ks) (c :: ls)).length ≠ [] := by
                            simp [hL]
                          have hne : k' ≠ l := by
                            rcases hdiv with h1 | h2 |
                              ⟨x, xs'', y, ys'', hx, hy, hxy⟩
                            · rw [hK] at h1
                              simp at h1
                            · rw [hL] at h2
                              simp at h2
                            · rw [hK] at hx
                              rw [hL] at hy
                              obtain ⟨rfl, -⟩ := List.cons.inj hx
                              obtain ⟨rfl, -⟩ := List.cons.inj hy
                              exact hxy
                          rw [insert_cons_some_cons_cons current children c ks
                              value (c :: ls) child hfind hKne hLne, hK, hL,
                            lookup_node_cons,
                            findEdge_replaceEdge_same
                              (newEdge := (commonPrefix (c :: ks) (c :: ls),
                                .node none [(l :: ls', child),
                                  ((k' :: ks'), .node (some value) [])]))
                              hPhead children]
                          show (if commonPrefix (c :: ks)
                                (commonPrefix (c :: ks) (c :: ls)) =
                                commonPrefix (c :: ks) (c :: ls)
                              then lookup
                                (.node none [(l :: ls', child),
                                  ((k' :: ks'), .node (some value) [])])
                                ((c :: ks).drop
                                  (commonPrefix (c :: ks) (c :: ls)).length)
                            else none) = some value
                          rw [ite_eq_left (commonPrefix_eq_of_append hkey), hK,
                            lookup_node_cons]
                          have hlk : (l :: ls').head? ≠ some k' := by
                            rw [List.head?_cons]
                            exact fun hEq => Ne.symm hne (Option.some.inj hEq)
                          rw [findEdge_cons, ite_eq_right hlk, findEdge_cons,
                            ite_eq_left (show (k' :: ks').head? = some k' from
                              rfl)]
                          show (if commonPrefix (k' :: ks') (k' :: ks') =
                                (k' :: ks')
                              then lookup (.node (some value) [])
                                ((k' :: ks').drop (k' :: ks').length)
                            else none) = some value
                          rw [commonPrefix_self, ite_eq_left rfl,
                            List.drop_of_length_le (Nat.le_refl _), lookup_nil]

private theorem commonPrefix_append_eq_iff {α : Type u} [DecidableEq α]
    (P ρ L' : List α) :
    (commonPrefix (P ++ ρ) (P ++ L') = (P ++ L')) ↔ commonPrefix ρ L' = L' := by
  rw [commonPrefix_append_append]
  constructor
  · intro hEq
    have h2 := congrArg (List.drop P.length) hEq
    rwa [List.drop_append_length, List.drop_append_length] at h2
  · intro hEq
    rw [hEq]

private theorem drop_append_length_add {α : Type u} (P ρ L' : List α) :
    (P ++ ρ).drop (P ++ L').length = ρ.drop L'.length := by
  rw [List.length_append, ← List.drop_drop, List.drop_append_length]

private theorem lookup_nil_insert_cons {α : Type u} {β : Type v}
    [DecidableEq α] (current : Option β)
    (children : List (List α × RadixTrie α β)) (c : α) (ks : List α) (value : β) :
    lookup (insert (.node current children) (c :: ks) value) [] = current := by
  cases hfind : findEdge c children with
  | none => rw [insert_cons_none _ _ _ _ _ hfind, lookup_nil]
  | some edge =>
      rcases edge with ⟨label, child⟩
      by_cases hk : (c :: ks).drop (commonPrefix (c :: ks) label).length = []
      · by_cases hl : label.drop (commonPrefix (c :: ks) label).length = []
        · rw [insert_cons_some_nil_nil _ _ _ _ _ _ _ hfind hk hl, lookup_nil]
        · rw [insert_cons_some_nil_cons _ _ _ _ _ _ _ hfind hk hl, lookup_nil]
      · by_cases hl : label.drop (commonPrefix (c :: ks) label).length = []
        · rw [insert_cons_some_cons_nil _ _ _ _ _ _ _ hfind hk hl, lookup_nil]
        · rw [insert_cons_some_cons_cons _ _ _ _ _ _ _ hfind hk hl, lookup_nil]

/-- Inserting one key does not change the lookup result for a distinct key. -/
@[simp]
theorem lookup_insert_of_ne {α : Type u} {β : Type v} [DecidableEq α]
    (trie : RadixTrie α β) {insertedKeys keys : List α} (value : β)
    (h : keys ≠ insertedKeys) :
    (trie.insert insertedKeys value).lookup keys = trie.lookup keys := by
  suffices hsuff : ∀ (trie : RadixTrie α β) (insertedKeys keys : List α),
      keys ≠ insertedKeys →
      (trie.insert insertedKeys value).lookup keys = trie.lookup keys from
    hsuff trie insertedKeys keys h
  intro trie insertedKeys
  induction hlen : insertedKeys.length using Nat.strongRecOn
      generalizing trie insertedKeys with
  | _ n ih =>
      intro keys h
      cases insertedKeys with
      | nil =>
          cases keys with
          | nil => exact (h rfl).elim
          | cons c' ks' =>
              cases trie with
              | node current children =>
                  rw [insert_nil, lookup_node_cons, lookup_node_cons]
      | cons c ks =>
          cases keys with
          | nil =>
              cases trie with
              | node current children =>
                  rw [lookup_nil_insert_cons, lookup_nil]
          | cons c' ks' =>
              cases trie with
              | node current children =>
                  by_cases hcc : c' = c
                  · obtain rfl : c = c' := hcc.symm
                    cases hfind : findEdge c children with
                    | none =>
                        rw [insert_cons_none current children c ks value hfind,
                          lookup_node_cons, lookup_node_cons, hfind,
                          findEdge_replaceEdge_same
                            (newEdge := ((c :: ks), .node (some value) []))
                            (by rfl) children]
                        show (if commonPrefix (c :: ks') (c :: ks) = (c :: ks)
                            then lookup (.node (some value) [])
                              ((c :: ks').drop (c :: ks).length)
                          else none) = none
                        by_cases hcpK :
                            commonPrefix (c :: ks') (c :: ks) = (c :: ks)
                        · rw [ite_eq_left hcpK, lookup_leaf]
                          by_cases hd :
                              (c :: ks').drop (c :: ks).length = []
                          · have hcontra : (c :: ks') = (c :: ks) := by
                              have h2 := append_of_commonPrefix_eq hcpK
                              rw [hd, List.append_nil] at h2
                              exact h2
                            exact (h hcontra).elim
                          · rw [ite_eq_right hd]
                        · rw [ite_eq_right hcpK]
                    | some edge =>
                        rcases edge with ⟨label, child⟩
                        have hhead := findEdge_some_head hfind
                        obtain ⟨ls, rfl⟩ := exists_cons_of_head?_eq_some hhead
                        have hcp : commonPrefix (c :: ks) (c :: ls) =
                            c :: commonPrefix ks ls := by
                          rw [commonPrefix_cons_cons, ite_eq_left rfl]
                        have hPhead :
                            (commonPrefix (c :: ks) (c :: ls)).head? =
                              some c := by
                          simp only [hcp, List.head?_cons]
                        obtain ⟨hkey, hlabel, hdiv⟩ :=
                          commonPrefix_drop_spec (c :: ks) (c :: ls)
                        cases hK : (c :: ks).drop
                            (commonPrefix (c :: ks) (c :: ls)).length with
                        | nil =>
                            cases hL : (c :: ls).drop
                                (commonPrefix (c :: ks) (c :: ls)).length with
                            | nil =>
                                have e1 : (c :: ks) =
                                    commonPrefix (c :: ks) (c :: ls) := by
                                  have h2 := hkey
                                  rw [hK, List.append_nil] at h2
                                  exact h2
                                have e2 : (c :: ls) =
                                    commonPrefix (c :: ks) (c :: ls) := by
                                  have h2 := hlabel
                                  rw [hL, List.append_nil] at h2
                                  exact h2
                                rw [insert_cons_some_nil_nil current children c
                                    ks value (c :: ls) child hfind hK hL,
                                  lookup_node_cons, lookup_node_cons, hfind,
                                  findEdge_replaceEdge_same
                                    (newEdge := ((c :: ls),
                                      child.insert [] value))
                                    (findEdge_some_head hfind) children]
                                show (if commonPrefix (c :: ks') (c :: ls) =
                                      (c :: ls)
                                    then lookup (child.insert [] value)
                                      ((c :: ks').drop (c :: ls).length)
                                  else none) =
                                    (if commonPrefix (c :: ks') (c :: ls) =
                                      (c :: ls)
                                    then lookup child
                                      ((c :: ks').drop (c :: ls).length)
                                  else none)
                                by_cases hcond :
                                    commonPrefix (c :: ks') (c :: ls) =
                                      (c :: ls)
                                · rw [ite_eq_left hcond, ite_eq_left hcond]
                                  have hρ : (c :: ks').drop (c :: ls).length ≠
                                      [] := by
                                    intro hd
                                    have h2 := append_of_commonPrefix_eq hcond
                                    rw [hd, List.append_nil] at h2
                                    exact h (h2.trans (e1.trans e2.symm).symm)
                                  have hlt0 : ([] : List α).length < n := by
                                    rw [List.length_nil, ← hlen,
                                      List.length_cons]
                                    omega
                                  exact ih _ hlt0 child [] rfl _ hρ
                                · rw [ite_eq_right hcond, ite_eq_right hcond]
                            | cons l ls' =>
                                have hLne : (c :: ls).drop
                                    (commonPrefix (c :: ks) (c :: ls)).length ≠
                                      [] := by
                                  simp [hL]
                                have e1 : (c :: ks) =
                                    commonPrefix (c :: ks) (c :: ls) := by
                                  have h2 := hkey
                                  rw [hK, List.append_nil] at h2
                                  exact h2
                                have hlab : (c :: ls) =
                                    commonPrefix (c :: ks) (c :: ls) ++
                                      (l :: ls') := by
                                  have h2 := hlabel
                                  rwa [hL] at h2
                                rw [insert_cons_some_nil_cons current children c
                                    ks value (c :: ls) child hfind hK hLne, hL,
                                  lookup_node_cons, lookup_node_cons, hfind,
                                  findEdge_replaceEdge_same
                                    (newEdge := (commonPrefix (c :: ks)
                                      (c :: ls),
                                      .node (some value) [(l :: ls', child)]))
                                    hPhead children]
                                show (if commonPrefix (c :: ks')
                                      (commonPrefix (c :: ks) (c :: ls)) =
                                      commonPrefix (c :: ks) (c :: ls)
                                    then lookup
                                      (.node (some value) [(l :: ls', child)])
                                      ((c :: ks').drop
                                        (commonPrefix (c :: ks)
                                          (c :: ls)).length)
                                  else none) =
                                    (if commonPrefix (c :: ks') (c :: ls) =
                                      (c :: ls)
                                    then lookup child
                                      ((c :: ks').drop (c :: ls).length)
                                  else none)
                                by_cases hP : commonPrefix (c :: ks')
                                    (commonPrefix (c :: ks) (c :: ls)) =
                                    commonPrefix (c :: ks) (c :: ls)
                                · rw [ite_eq_left hP]
                                  set P := commonPrefix (c :: ks) (c :: ls)
                                    with hPgen
                                  cases hρ : (c :: ks').drop P.length with
                                  | nil =>
                                      have hcontra : (c :: ks') = (c :: ks) := by
                                        have h2 := append_of_commonPrefix_eq hP
                                        rw [hρ, List.append_nil] at h2
                                        exact h2.trans e1.symm
                                      exact (h hcontra).elim
                                  | cons d ρs =>
                                      have hκ : (c :: ks') =
                                          P ++ (d :: ρs) := by
                                        have h2 := append_of_commonPrefix_eq hP
                                        rwa [hρ] at h2
                                      have hcond : (commonPrefix (c :: ks')
                                            (c :: ls) = (c :: ls)) ↔
                                          commonPrefix (d :: ρs) (l :: ls') =
                                            (l :: ls') := by
                                        rw [hκ, hlab]
                                        exact commonPrefix_append_eq_iff _ _ _
                                      have hdrop : (c :: ks').drop
                                            (c :: ls).length =
                                          (d :: ρs).drop (l :: ls').length := by
                                        rw [hκ, hlab]
                                        exact drop_append_length_add _ _ _
                                      rw [lookup_node_cons]
                                      by_cases hd : d = l
                                      · obtain rfl : l = d := hd.symm
                                        rw [findEdge_cons,
                                          ite_eq_left
                                            (show (l :: ls').head? = some l from
                                              rfl)]
                                        show (if commonPrefix (l :: ρs)
                                              (l :: ls') = (l :: ls')
                                            then lookup child
                                              ((l :: ρs).drop (l :: ls').length)
                                          else none) =
                                            (if commonPrefix (c :: ks')
                                              (c :: ls) = (c :: ls)
                                            then lookup child
                                              ((c :: ks').drop (c :: ls).length)
                                          else none)
                                        by_cases hc2 : commonPrefix (l :: ρs)
                                            (l :: ls') = (l :: ls')
                                        · rw [ite_eq_left hc2,
                                            ite_eq_left (hcond.mpr hc2), hdrop]
                                        · rw [ite_eq_right hc2,
                                            ite_eq_right
                                              (fun hcc => hc2 (hcond.mp hcc))]
                                      · have hlk : (l :: ls').head? ≠
                                            some d := by
                                          rw [List.head?_cons]
                                          exact fun hEq =>
                                            hd (Option.some.inj hEq).symm
                                        rw [findEdge_cons, ite_eq_right hlk,
                                          findEdge_nil]
                                        show none =
                                          (if commonPrefix (c :: ks')
                                              (c :: ls) = (c :: ls)
                                          then lookup child
                                            ((c :: ks').drop (c :: ls).length)
                                          else none)
                                        have hcR : ¬ commonPrefix (c :: ks')
                                            (c :: ls) = (c :: ls) := by
                                          intro hcc
                                          have h2 := hcond.mp hcc
                                          rw [commonPrefix_cons_cons,
                                            ite_eq_right hd] at h2
                                          cases h2
                                        rw [ite_eq_right hcR]
                                · rw [ite_eq_right hP]
                                  have hcR : ¬ commonPrefix (c :: ks')
                                      (c :: ls) = (c :: ls) := by
                                    intro hcc
                                    apply hP
                                    have h2 := append_of_commonPrefix_eq hcc
                                    rw [hlab, List.append_assoc] at h2
                                    exact commonPrefix_eq_of_append h2
                                  rw [ite_eq_right hcR]
                        | cons k' kd =>
                            cases hL : (c :: ls).drop
                                (commonPrefix (c :: ks) (c :: ls)).length with
                            | nil =>
                                have hKne : (c :: ks).drop
                                    (commonPrefix (c :: ks) (c :: ls)).length ≠
                                      [] := by
                                  simp [hK]
                                have e2 : (c :: ls) =
                                    commonPrefix (c :: ks) (c :: ls) := by
                                  have h2 := hlabel
                                  rw [hL, List.append_nil] at h2
                                  exact h2
                                have hlt : ((c :: ks).drop
                                      (c :: ls).length).length < n := by
                                  have h3 : (c :: ls).length =
                                      (commonPrefix ks ls).length + 1 := by
                                    have h4 := congrArg List.length e2
                                    rw [hcp] at h4
                                    simp only [List.length_cons] at h4 ⊢
                                    omega
                                  have h5 : 0 < (c :: ks).length := by
                                    rw [List.length_cons]
                                    omega
                                  rw [← hlen, List.length_drop]
                                  omega
                                rw [insert_cons_some_cons_nil current children c
                                    ks value (c :: ls) child hfind hKne hL,
                                  lookup_node_cons, lookup_node_cons, hfind,
                                  findEdge_replaceEdge_same
                                    (newEdge := ((c :: ls), child.insert
                                      ((c :: ks).drop
                                        (commonPrefix (c :: ks)
                                          (c :: ls)).length) value))
                                    (findEdge_some_head hfind) children]
                                show (if commonPrefix (c :: ks') (c :: ls) =
                                      (c :: ls)
                                    then lookup (child.insert
                                        ((c :: ks).drop
                                          (commonPrefix (c :: ks)
                                            (c :: ls)).length) value)
                                      ((c :: ks').drop (c :: ls).length)
                                  else none) =
                                    (if commonPrefix (c :: ks') (c :: ls) =
                                      (c :: ls)
                                    then lookup child
                                      ((c :: ks').drop (c :: ls).length)
                                  else none)
                                by_cases hcond :
                                    commonPrefix (c :: ks') (c :: ls) =
                                      (c :: ls)
                                · rw [ite_eq_left hcond, ite_eq_left hcond,
                                    ← e2]
                                  have hρ : (c :: ks').drop (c :: ls).length ≠
                                      (c :: ks).drop (c :: ls).length := by
                                    intro hd
                                    have h2 := append_of_commonPrefix_eq hcond
                                    have h3 := hkey
                                    rw [← e2] at h3
                                    rw [hd] at h2
                                    exact h (h2.trans h3.symm)
                                  exact ih _ hlt child _ rfl _ hρ
                                · rw [ite_eq_right hcond, ite_eq_right hcond]
                            | cons l ls' =>
                                have hKne : (c :: ks).drop
                                    (commonPrefix (c :: ks) (c :: ls)).length ≠
                                      [] := by
                                  simp [hK]
                                have hLne : (c :: ls).drop
                                    (commonPrefix (c :: ks) (c :: ls)).length ≠
                                      [] := by
                                  simp [hL]
                                have hne : k' ≠ l := by
                                  rcases hdiv with h1 | h2 |
                                    ⟨x, xs'', y, ys'', hx, hy, hxy⟩
                                  · rw [hK] at h1
                                    simp at h1
                                  · rw [hL] at h2
                                    simp at h2
                                  · rw [hK] at hx
                                    rw [hL] at hy
                                    obtain ⟨rfl, -⟩ := List.cons.inj hx
                                    obtain ⟨rfl, -⟩ := List.cons.inj hy
                                    exact hxy
                                have hlab : (c :: ls) =
                                    commonPrefix (c :: ks) (c :: ls) ++
                                      (l :: ls') := by
                                  have h2 := hlabel
                                  rwa [hL] at h2
                                rw [insert_cons_some_cons_cons current children
                                    c ks value (c :: ls) child hfind hKne
                                    hLne, hK, hL,
                                  lookup_node_cons, lookup_node_cons, hfind,
                                  findEdge_replaceEdge_same
                                    (newEdge := (commonPrefix (c :: ks)
                                      (c :: ls),
                                      .node none [(l :: ls', child),
                                        ((k' :: kd),
                                          .node (some value) [])]))
                                    hPhead children]
                                show (if commonPrefix (c :: ks')
                                      (commonPrefix (c :: ks) (c :: ls)) =
                                      commonPrefix (c :: ks) (c :: ls)
                                    then lookup
                                      (.node none [(l :: ls', child),
                                        ((k' :: kd),
                                          .node (some value) [])])
                                      ((c :: ks').drop
                                        (commonPrefix (c :: ks)
                                          (c :: ls)).length)
                                  else none) =
                                    (if commonPrefix (c :: ks') (c :: ls) =
                                      (c :: ls)
                                    then lookup child
                                      ((c :: ks').drop (c :: ls).length)
                                  else none)
                                by_cases hP : commonPrefix (c :: ks')
                                    (commonPrefix (c :: ks) (c :: ls)) =
                                    commonPrefix (c :: ks) (c :: ls)
                                · rw [ite_eq_left hP]
                                  set P := commonPrefix (c :: ks) (c :: ls)
                                    with hPgen
                                  cases hρ : (c :: ks').drop P.length with
                                  | nil =>
                                      rw [lookup_nil]
                                      have hcR : ¬ commonPrefix (c :: ks')
                                          (c :: ls) = (c :: ls) := by
                                        intro hcc
                                        have hκ : (c :: ks') =
                                            P ++ [] := by
                                          have h2 :=
                                            append_of_commonPrefix_eq hP
                                          rwa [hρ] at h2
                                        have hcond : (commonPrefix (c :: ks')
                                              (c :: ls) = (c :: ls)) ↔
                                            commonPrefix ([] : List α)
                                              (l :: ls') = (l :: ls') := by
                                          rw [hκ, hlab]
                                          exact
                                            commonPrefix_append_eq_iff _ _ _
                                        have h2 := hcond.mp hcc
                                        rw [commonPrefix_nil_left] at h2
                                        cases h2
                                      rw [ite_eq_right hcR]
                                  | cons d ρs =>
                                      have hκ : (c :: ks') =
                                          P ++ (d :: ρs) := by
                                        have h2 := append_of_commonPrefix_eq hP
                                        rwa [hρ] at h2
                                      have hcond : (commonPrefix (c :: ks')
                                            (c :: ls) = (c :: ls)) ↔
                                          commonPrefix (d :: ρs) (l :: ls') =
                                            (l :: ls') := by
                                        rw [hκ, hlab]
                                        exact commonPrefix_append_eq_iff _ _ _
                                      have hdrop : (c :: ks').drop
                                            (c :: ls).length =
                                          (d :: ρs).drop (l :: ls').length := by
                                        rw [hκ, hlab]
                                        exact drop_append_length_add _ _ _
                                      rw [lookup_node_cons]
                                      by_cases hd : d = l
                                      · obtain rfl : l = d := hd.symm
                                        rw [findEdge_cons,
                                          ite_eq_left
                                            (show (l :: ls').head? = some l from
                                              rfl)]
                                        show (if commonPrefix (l :: ρs)
                                              (l :: ls') = (l :: ls')
                                            then lookup child
                                              ((l :: ρs).drop (l :: ls').length)
                                          else none) =
                                            (if commonPrefix (c :: ks')
                                              (c :: ls) = (c :: ls)
                                            then lookup child
                                              ((c :: ks').drop (c :: ls).length)
                                          else none)
                                        by_cases hc2 : commonPrefix (l :: ρs)
                                            (l :: ls') = (l :: ls')
                                        · rw [ite_eq_left hc2,
                                            ite_eq_left (hcond.mpr hc2), hdrop]
                                        · rw [ite_eq_right hc2,
                                            ite_eq_right
                                              (fun hcc => hc2 (hcond.mp hcc))]
                                      · have hlk : (l :: ls').head? ≠
                                            some d := by
                                          rw [List.head?_cons]
                                          exact fun hEq =>
                                            hd (Option.some.inj hEq).symm
                                        have hcR : ¬ commonPrefix (c :: ks')
                                            (c :: ls) = (c :: ls) := by
                                          intro hcc
                                          have h2 := hcond.mp hcc
                                          rw [commonPrefix_cons_cons,
                                            ite_eq_right hd] at h2
                                          cases h2
                                        by_cases hd2 : d = k'
                                        · subst hd2
                                          rw [findEdge_cons, ite_eq_right hlk,
                                            findEdge_cons,
                                            ite_eq_left
                                              (show (d :: kd).head? = some d
                                                from rfl)]
                                          show (if commonPrefix (d :: ρs)
                                                (d :: kd) = (d :: kd)
                                              then lookup (.node (some value)
                                                  [])
                                                ((d :: ρs).drop
                                                  (d :: kd).length)
                                            else none) =
                                              (if commonPrefix (c :: ks')
                                                (c :: ls) = (c :: ls)
                                              then lookup child
                                                ((c :: ks').drop
                                                  (c :: ls).length)
                                            else none)
                                          rw [ite_eq_right hcR]
                                          by_cases hcpρ :
                                              commonPrefix (d :: ρs) (d :: kd) =
                                                (d :: kd)
                                          · rw [ite_eq_left hcpρ, lookup_leaf]
                                            by_cases hd3 : (d :: ρs).drop
                                                (d :: kd).length = []
                                            · have hκ2 : (d :: ρs) =
                                                  (d :: kd) := by
                                                have h2 :=
                                                  append_of_commonPrefix_eq hcpρ
                                                rwa [hd3, List.append_nil] at h2
                                              have hins : (c :: ks) =
                                                  commonPrefix (c :: ks)
                                                    (c :: ls) ++ (d :: kd) := by
                                                have h2 := hkey
                                                rwa [hK] at h2
                                              have hκ3 : (c :: ks') =
                                                  commonPrefix (c :: ks)
                                                    (c :: ls) ++ (d :: kd) := by
                                                rwa [hκ2] at hκ
                                              exact (h (hκ3.trans
                                                hins.symm)).elim
                                            · rw [ite_eq_right hd3]
                                          · rw [ite_eq_right hcpρ]
                                        · have hkk : (k' :: kd).head? ≠
                                              some d := by
                                            rw [List.head?_cons]
                                            exact fun hEq =>
                                              hd2 (Option.some.inj hEq).symm
                                          rw [findEdge_cons, ite_eq_right hlk,
                                            findEdge_cons, ite_eq_right hkk,
                                            findEdge_nil]
                                          show none =
                                            (if commonPrefix (c :: ks')
                                                (c :: ls) = (c :: ls)
                                            then lookup child
                                              ((c :: ks').drop (c :: ls).length)
                                            else none)
                                          rw [ite_eq_right hcR]
                                · rw [ite_eq_right hP]
                                  have hcR : ¬ commonPrefix (c :: ks')
                                      (c :: ls) = (c :: ls) := by
                                    intro hcc
                                    apply hP
                                    have h2 := append_of_commonPrefix_eq hcc
                                    rw [hlab, List.append_assoc] at h2
                                    exact commonPrefix_eq_of_append h2
                                  rw [ite_eq_right hcR]
                  · cases hfind : findEdge c children with
                    | none =>
                        rw [insert_cons_none current children c ks value hfind,
                          lookup_node_cons, lookup_node_cons,
                          findEdge_replaceEdge_ne hcc
                            (newEdge := ((c :: ks), .node (some value) []))
                            (by rfl) children]
                    | some edge =>
                        rcases edge with ⟨label, child⟩
                        by_cases hk : (c :: ks).drop
                            (commonPrefix (c :: ks) label).length = []
                        · by_cases hl : label.drop
                              (commonPrefix (c :: ks) label).length = []
                          · rw [insert_cons_some_nil_nil current children c ks
                                value label child hfind hk hl,
                              lookup_node_cons, lookup_node_cons,
                              findEdge_replaceEdge_ne hcc
                                (newEdge := (label, child.insert [] value))
                                (findEdge_some_head hfind) children]
                          · obtain ⟨ls, rfl⟩ :=
                              exists_cons_of_head?_eq_some
                                (findEdge_some_head hfind)
                            have hcp : commonPrefix (c :: ks) (c :: ls) =
                                c :: commonPrefix ks ls := by
                              rw [commonPrefix_cons_cons, ite_eq_left rfl]
                            have hPhead :
                                (commonPrefix (c :: ks) (c :: ls)).head? =
                                  some c := by
                              simp only [hcp, List.head?_cons]
                            rw [insert_cons_some_nil_cons current children c
                                ks value (c :: ls) child hfind hk hl,
                              lookup_node_cons, lookup_node_cons,
                              findEdge_replaceEdge_ne hcc
                                (newEdge := (commonPrefix (c :: ks) (c :: ls),
                                  .node (some value)
                                    [((c :: ls).drop
                                      (commonPrefix (c :: ks)
                                        (c :: ls)).length, child)]))
                                hPhead children]
                        · by_cases hl : label.drop
                              (commonPrefix (c :: ks) label).length = []
                          · rw [insert_cons_some_cons_nil current children c
                                ks value label child hfind hk hl,
                              lookup_node_cons, lookup_node_cons,
                              findEdge_replaceEdge_ne hcc
                                (newEdge := (label, child.insert
                                  ((c :: ks).drop
                                    (commonPrefix (c :: ks) label).length)
                                  value))
                                (findEdge_some_head hfind) children]
                          · obtain ⟨ls, rfl⟩ :=
                              exists_cons_of_head?_eq_some
                                (findEdge_some_head hfind)
                            have hcp : commonPrefix (c :: ks) (c :: ls) =
                                c :: commonPrefix ks ls := by
                              rw [commonPrefix_cons_cons, ite_eq_left rfl]
                            have hPhead :
                                (commonPrefix (c :: ks) (c :: ls)).head? =
                                  some c := by
                              simp only [hcp, List.head?_cons]
                            rw [insert_cons_some_cons_cons current children c
                                ks value (c :: ls) child hfind hk hl,
                              lookup_node_cons, lookup_node_cons,
                              findEdge_replaceEdge_ne hcc
                                (newEdge := (commonPrefix (c :: ks) (c :: ls),
                                  .node none
                                    [((c :: ls).drop
                                      (commonPrefix (c :: ks)
                                        (c :: ls)).length, child),
                                      ((c :: ks).drop
                                        (commonPrefix (c :: ks)
                                          (c :: ls)).length,
                                        .node (some value) [])]))
                                hPhead children]

private theorem length_le_replaceEdge {α : Type u} {β : Type v} [DecidableEq α]
    (c : α) (newEdge : List α × RadixTrie α β)
    (children : List (List α × RadixTrie α β)) :
    children.length ≤ (replaceEdge c newEdge children).length := by
  induction children with
  | nil =>
      rw [replaceEdge_nil]
      simp
  | cons head rest ih =>
      rcases head with ⟨label, child⟩
      rw [replaceEdge_cons]
      by_cases hh : label.head? = some c
      · rw [ite_eq_left hh]
        simp
      · rw [ite_eq_right hh]
        simp only [List.length_cons]
        omega

/--
Path compression at a single node: a node reached by an edge either ends a key (it
stores a value) or genuinely branches (it has at least two children). A value-free node
with at most one child could be merged into its parent edge, which is exactly what a
radix trie rules out. The root is exempt, since it has no incoming edge.
-/
def RootCompact {α : Type u} {β : Type v} : RadixTrie α β → Prop
  | .node cv cc => cv ≠ none ∨ 2 ≤ cc.length

theorem rootCompact_some {α : Type u} {β : Type v} (v : β)
    (cc : List (List α × RadixTrie α β)) :
    RootCompact (.node (some v) cc : RadixTrie α β) :=
  Or.inl (by simp)

theorem rootCompact_insert_nil {α : Type u} {β : Type v} [DecidableEq α]
    (trie : RadixTrie α β) (value : β) :
    RootCompact (trie.insert [] value) := by
  cases trie with
  | node current children =>
      rw [insert_nil]
      exact rootCompact_some value children

theorem rootCompact_insert_cons {α : Type u} {β : Type v} [DecidableEq α]
    {cv : Option β} {cc : List (List α × RadixTrie α β)}
    (h : cv ≠ none ∨ 2 ≤ cc.length) (c : α) (ks : List α) (value : β) :
    RootCompact (insert (.node cv cc) (c :: ks) value) := by
  obtain ⟨cc', heq, hlen⟩ : ∃ cc',
      insert (.node cv cc) (c :: ks) value = .node cv cc' ∧ cc.length ≤ cc'.length := by
    cases hfind : findEdge c cc with
    | none =>
        exact ⟨_, insert_cons_none cv cc c ks value hfind,
          length_le_replaceEdge c _ cc⟩
    | some edge =>
        rcases edge with ⟨label, child⟩
        by_cases hk : (c :: ks).drop (commonPrefix (c :: ks) label).length = []
        · by_cases hl : label.drop (commonPrefix (c :: ks) label).length = []
          · exact ⟨_, insert_cons_some_nil_nil cv cc c ks value label child hfind hk hl,
              length_le_replaceEdge c _ cc⟩
          · exact ⟨_, insert_cons_some_nil_cons cv cc c ks value label child hfind hk hl,
              length_le_replaceEdge c _ cc⟩
        · by_cases hl : label.drop (commonPrefix (c :: ks) label).length = []
          · exact ⟨_, insert_cons_some_cons_nil cv cc c ks value label child hfind hk hl,
              length_le_replaceEdge c _ cc⟩
          · exact ⟨_, insert_cons_some_cons_cons cv cc c ks value label child hfind hk hl,
              length_le_replaceEdge c _ cc⟩
  rw [heq]
  show cv ≠ none ∨ 2 ≤ cc'.length
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/--
The radix-trie invariant: at every node, edge labels are nonempty, their first symbols
are distinct, every subtree is valid, and every subtree is path-compressed at its root
(`RootCompact`): a value-free non-root node has at least two children, so no unary
value-free node remains to be merged into its parent edge.
-/
inductive Valid {α : Type u} {β : Type v} : RadixTrie α β → Prop where
  | node {value : Option β} {children : List (List α × RadixTrie α β)}
      (nonempty : ∀ e ∈ children, e.1 ≠ [])
      (distinct : (children.map (fun e => e.1.head?)).Nodup)
      (childrenValid : ∀ e ∈ children, Valid e.2)
      (compact : ∀ e ∈ children, RootCompact e.2) :
      Valid (.node value children)

/-- The empty trie is valid. -/
theorem Valid.empty {α : Type u} {β : Type v} : Valid (empty : RadixTrie α β) :=
  .node (by simp) (by simp) (by simp) (by simp)

/-- A valid node has no duplicate edge first symbols. -/
theorem Valid.nodup_child_heads {α : Type u} {β : Type v} {value : Option β}
    {children : List (List α × RadixTrie α β)}
    (h : Valid (.node value children)) :
    (children.map (fun e => e.1.head?)).Nodup := by
  cases h with
  | node _ distinct _ _ => exact distinct

/-- Every child subtree of a valid node is path-compressed at its root. -/
theorem Valid.rootCompact_child {α : Type u} {β : Type v} {value : Option β}
    {children : List (List α × RadixTrie α β)}
    (h : Valid (.node value children)) {e : List α × RadixTrie α β}
    (he : e ∈ children) :
    RootCompact e.2 := by
  cases h with
  | node _ _ _ compact => exact compact e he

private theorem mem_map_head?_replaceEdge_imp {α : Type u} {β : Type v}
    [DecidableEq α] {c : α} {newEdge : List α × RadixTrie α β}
    {children : List (List α × RadixTrie α β)} {x : Option α}
    (h : x ∈ (replaceEdge c newEdge children).map (fun e => e.1.head?)) :
    x ∈ children.map (fun e => e.1.head?) ∨ x = newEdge.1.head? := by
  induction children with
  | nil =>
      rw [replaceEdge_nil] at h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      exact Or.inr h
  | cons head rest ih =>
      rcases head with ⟨label, child⟩
      simp only [List.map_cons, List.mem_cons]
      by_cases hh : label.head? = some c
      · rw [replaceEdge_cons, ite_eq_left hh] at h
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
      · rw [replaceEdge_cons, ite_eq_right hh] at h
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact Or.inl (Or.inl h)
        · rcases ih h with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h

private theorem replaceEdge_valid_children {α : Type u} {β : Type v}
    [DecidableEq α] {c : α} {newEdge : List α × RadixTrie α β}
    {children : List (List α × RadixTrie α β)}
    (hkeys : (children.map (fun e => e.1.head?)).Nodup)
    (hchildren : ∀ e ∈ children, e.1 ≠ [] ∧ Valid e.2 ∧ RootCompact e.2)
    (hnew : newEdge.1 ≠ [] ∧ Valid newEdge.2 ∧ RootCompact newEdge.2)
    (hhead : newEdge.1.head? = some c) :
    ((replaceEdge c newEdge children).map (fun e => e.1.head?)).Nodup ∧
      ∀ e ∈ replaceEdge c newEdge children, e.1 ≠ [] ∧ Valid e.2 ∧ RootCompact e.2 := by
  rcases newEdge with ⟨nlabel, nchild⟩
  obtain ⟨hn1, hn2, hn3⟩ := hnew
  have hhead' : nlabel.head? = some c := hhead
  induction children with
  | nil =>
      rw [replaceEdge_nil]
      constructor
      · simp
      · intro e he
        rw [List.mem_singleton] at he
        cases he
        exact ⟨hn1, hn2, hn3⟩
  | cons head rest ih =>
      rcases head with ⟨label, child⟩
      have hhead_old := hchildren (label, child) (by simp)
      have htail : ∀ e ∈ rest, e.1 ≠ [] ∧ Valid e.2 ∧ RootCompact e.2 :=
        fun e he => hchildren e (List.mem_cons_of_mem _ he)
      simp only [List.map_cons] at hkeys
      have htailKeys : (rest.map (fun e => e.1.head?)).Nodup :=
        (List.nodup_cons.mp hkeys).2
      by_cases hh : label.head? = some c
      · rw [replaceEdge_cons, ite_eq_left hh]
        constructor
        · simp only [List.map_cons]
          rw [hhead', ← hh]
          exact hkeys
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact ⟨hn1, hn2, hn3⟩
          · exact htail e he
      · rw [replaceEdge_cons, ite_eq_right hh]
        have hi := ih htailKeys htail
        constructor
        · simp only [List.map_cons, List.nodup_cons]
          constructor
          · intro hmem
            have hnot : label.head? ∉ rest.map (fun e => e.1.head?) :=
              (List.nodup_cons.mp hkeys).1
            rcases mem_map_head?_replaceEdge_imp hmem with h | h
            · exact hnot h
            · exact hh (h.trans hhead')
          · exact hi.1
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact hhead_old
          · exact hi.2 e he

/-- Insertion preserves the radix-trie invariant. -/
theorem Valid.insert {α : Type u} {β : Type v} [DecidableEq α]
    {trie : RadixTrie α β} (h : Valid trie) (keys : List α) (value : β) :
    Valid (trie.insert keys value) := by
  suffices hsuff : ∀ (trie : RadixTrie α β) (keys : List α), Valid trie →
      Valid (trie.insert keys value) from hsuff trie keys h
  intro trie keys
  induction hlen : keys.length using Nat.strongRecOn
      generalizing trie keys with
  | _ n ih =>
      intro h
      cases keys with
      | nil =>
          cases h with
          | @node current children hne hdist hval hcomp =>
              rw [insert_nil]
              exact .node hne hdist hval hcomp
      | cons c ks =>
          cases h with
          | @node current children hne hdist hval hcomp =>
              have hbundle : ∀ e ∈ children, e.1 ≠ [] ∧ Valid e.2 ∧ RootCompact e.2 :=
                fun e he => ⟨hne e he, hval e he, hcomp e he⟩
              have hleaf : Valid (.node (some value) [] : RadixTrie α β) :=
                .node (by simp) (by simp) (by simp) (by simp)
              cases hfind : findEdge c children with
              | none =>
                  rw [insert_cons_none current children c ks value hfind]
                  have hr := replaceEdge_valid_children hdist hbundle
                    (newEdge := ((c :: ks), .node (some value) []))
                    ⟨by simp, hleaf, rootCompact_some value []⟩ (by rfl)
                  exact .node (fun e he => (hr.2 e he).1) hr.1
                    (fun e he => (hr.2 e he).2.1) (fun e he => (hr.2 e he).2.2)
              | some edge =>
                  rcases edge with ⟨label, child⟩
                  have hmem : (label, child) ∈ children :=
                    findEdge_some_mem hfind
                  have hchildValid : Valid child := hval (label, child) hmem
                  have hhead : label.head? = some c := findEdge_some_head hfind
                  obtain ⟨ls, rfl⟩ := exists_cons_of_head?_eq_some hhead
                  have hcp : commonPrefix (c :: ks) (c :: ls) =
                      c :: commonPrefix ks ls := by
                    rw [commonPrefix_cons_cons, ite_eq_left rfl]
                  have hPhead : (commonPrefix (c :: ks) (c :: ls)).head? =
                      some c := by
                    simp only [hcp, List.head?_cons]
                  have hPne : commonPrefix (c :: ks) (c :: ls) ≠ [] := by
                    rw [hcp]
                    exact List.cons_ne_nil _ _
                  by_cases hk : (c :: ks).drop
                      (commonPrefix (c :: ks) (c :: ls)).length = []
                  · by_cases hl : (c :: ls).drop
                        (commonPrefix (c :: ks) (c :: ls)).length = []
                    · rw [insert_cons_some_nil_nil current children c ks value
                        (c :: ls) child hfind hk hl]
                      have hlt0 : ([] : List α).length < n := by
                        rw [List.length_nil, ← hlen, List.length_cons]
                        omega
                      have hnewChild : Valid (child.insert [] value) :=
                        ih _ hlt0 child [] rfl hchildValid
                      have hr := replaceEdge_valid_children hdist hbundle
                        (newEdge := ((c :: ls), child.insert [] value))
                        ⟨List.cons_ne_nil _ _, hnewChild,
                          rootCompact_insert_nil child value⟩ hhead
                      exact .node (fun e he => (hr.2 e he).1) hr.1
                        (fun e he => (hr.2 e he).2.1) (fun e he => (hr.2 e he).2.2)
                    · have hsub : Valid (.node (some value)
                          [((c :: ls).drop
                            (commonPrefix (c :: ks) (c :: ls)).length, child)] :
                          RadixTrie α β) := by
                        apply Valid.node
                        · intro e he
                          simp only [List.mem_cons, List.not_mem_nil,
                            or_false] at he
                          cases he
                          exact hl
                        · simp
                        · intro e he
                          simp only [List.mem_cons, List.not_mem_nil,
                            or_false] at he
                          cases he
                          exact hchildValid
                        · intro e he
                          simp only [List.mem_cons, List.not_mem_nil,
                            or_false] at he
                          cases he
                          exact hcomp (c :: ls, child) hmem
                      rw [insert_cons_some_nil_cons current children c ks
                        value (c :: ls) child hfind hk hl]
                      have hr := replaceEdge_valid_children hdist hbundle
                        (newEdge := (commonPrefix (c :: ks) (c :: ls),
                          .node (some value)
                            [((c :: ls).drop
                              (commonPrefix (c :: ks) (c :: ls)).length,
                              child)]))
                        ⟨hPne, hsub, rootCompact_some value _⟩ hPhead
                      exact .node (fun e he => (hr.2 e he).1) hr.1
                        (fun e he => (hr.2 e he).2.1) (fun e he => (hr.2 e he).2.2)
                  · by_cases hl : (c :: ls).drop
                        (commonPrefix (c :: ks) (c :: ls)).length = []
                    · have hlt : ((c :: ks).drop
                            (commonPrefix (c :: ks) (c :: ls)).length).length <
                          n := by
                        rw [← hlen, List.length_drop, hcp]
                        simp only [List.length_cons]
                        omega
                      have hnewChild : Valid (child.insert
                          ((c :: ks).drop
                            (commonPrefix (c :: ks) (c :: ls)).length)
                          value) :=
                        ih _ hlt child _ rfl hchildValid
                      have hrcNew : RootCompact (child.insert
                          ((c :: ks).drop
                            (commonPrefix (c :: ks) (c :: ls)).length)
                          value) := by
                        have hrcChild : RootCompact child := hcomp _ hmem
                        cases child with
                        | node cv cc =>
                            cases hdrop : (c :: ks).drop
                                (commonPrefix (c :: ks) (c :: ls)).length with
                            | nil => exact absurd hdrop hk
                            | cons d ds =>
                                exact rootCompact_insert_cons hrcChild d ds value
                      rw [insert_cons_some_cons_nil current children c ks
                        value (c :: ls) child hfind hk hl]
                      have hr := replaceEdge_valid_children hdist hbundle
                        (newEdge := ((c :: ls), child.insert
                          ((c :: ks).drop
                            (commonPrefix (c :: ks) (c :: ls)).length) value))
                        ⟨List.cons_ne_nil _ _, hnewChild, hrcNew⟩ hhead
                      exact .node (fun e he => (hr.2 e he).1) hr.1
                        (fun e he => (hr.2 e he).2.1) (fun e he => (hr.2 e he).2.2)
                    · have hdiv3 : ∃ x xs'' y ys'',
                          (c :: ks).drop
                              (commonPrefix (c :: ks) (c :: ls)).length =
                            x :: xs'' ∧
                          (c :: ls).drop
                              (commonPrefix (c :: ks) (c :: ls)).length =
                            y :: ys'' ∧ x ≠ y := by
                        rcases (commonPrefix_drop_spec (c :: ks)
                          (c :: ls)).2.2 with h1 | h2 | h3
                        · exact (hk h1).elim
                        · exact (hl h2).elim
                        · exact h3
                      obtain ⟨x, xs'', y, ys'', hx, hy, hxy⟩ := hdiv3
                      have hheads : ((c :: ls).drop
                            (commonPrefix (c :: ks) (c :: ls)).length).head? ≠
                          ((c :: ks).drop
                            (commonPrefix (c :: ks) (c :: ls)).length).head? := by
                        rw [hy, hx, List.head?_cons, List.head?_cons]
                        exact fun hEq => hxy (Option.some.inj hEq).symm
                      have hsub : Valid (.node none
                          [((c :: ls).drop
                              (commonPrefix (c :: ks) (c :: ls)).length,
                            child),
                            ((c :: ks).drop
                              (commonPrefix (c :: ks) (c :: ls)).length,
                            .node (some value) [])] : RadixTrie α β) := by
                        apply Valid.node
                        · intro e he
                          simp only [List.mem_cons] at he
                          rcases he with rfl | he
                          · exact hl
                          · rcases he with rfl | he
                            · exact hk
                            · exact (List.not_mem_nil he).elim
                        · simp only [List.map_cons, List.map_nil,
                            List.nodup_cons, List.mem_singleton]
                          exact ⟨hheads, by simp⟩
                        · intro e he
                          simp only [List.mem_cons] at he
                          rcases he with rfl | he
                          · exact hchildValid
                          · rcases he with rfl | he
                            · exact hleaf
                            · exact (List.not_mem_nil he).elim
                        · intro e he
                          simp only [List.mem_cons] at he
                          rcases he with rfl | he
                          · exact hcomp (c :: ls, child) hmem
                          · rcases he with rfl | he
                            · exact rootCompact_some value []
                            · exact (List.not_mem_nil he).elim
                      rw [insert_cons_some_cons_cons current children c ks
                        value (c :: ls) child hfind hk hl]
                      have hr := replaceEdge_valid_children hdist hbundle
                        (newEdge := (commonPrefix (c :: ks) (c :: ls),
                          .node none
                            [((c :: ls).drop
                                (commonPrefix (c :: ks) (c :: ls)).length,
                              child),
                              ((c :: ks).drop
                                (commonPrefix (c :: ks) (c :: ls)).length,
                              .node (some value) [])]))
                        ⟨hPne, hsub, Or.inr (by simp)⟩ hPhead
                      exact .node (fun e he => (hr.2 e he).1) hr.1
                        (fun e he => (hr.2 e he).2.1) (fun e he => (hr.2 e he).2.2)

/-- Enumerates the key-value entries of a radix trie in stored sibling order. -/
def entries {α : Type u} {β : Type v} : RadixTrie α β → List (List α × β)
  | .node value children =>
      (match value with
       | none => []
       | some result => [([], result)]) ++ childEntries children
where
  childEntries : List (List α × RadixTrie α β) → List (List α × β)
    | [] => []
    | (label, child) :: children =>
        child.entries.map (fun (keys, result) => (label ++ keys, result)) ++
          childEntries children

/-- The stored keys of a radix trie, in stored sibling order. -/
def keys {α : Type u} {β : Type v} (trie : RadixTrie α β) : List (List α) :=
  trie.entries.map Prod.fst

private theorem findEdge_eq_some_iff {α : Type u} {β : Type v}
    [DecidableEq α] {c : α} {children : List (List α × RadixTrie α β)}
    (hkeys : (children.map (fun e => e.1.head?)).Nodup)
    {label : List α} {child : RadixTrie α β} :
    findEdge c children = some (label, child) ↔
      (label, child) ∈ children ∧ label.head? = some c := by
  induction children with
  | nil => simp [findEdge]
  | cons head rest ih =>
      rcases head with ⟨label', child'⟩
      simp only [List.map_cons] at hkeys
      have htail := (List.nodup_cons.mp hkeys).2
      have hnot : label'.head? ∉ rest.map (fun e => e.1.head?) :=
        (List.nodup_cons.mp hkeys).1
      by_cases hh : label'.head? = some c
      · rw [findEdge_cons, ite_eq_left hh]
        constructor
        · intro hEq
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hEq)
          exact ⟨by simp, hh⟩
        · rintro ⟨hmem, hhead⟩
          rcases List.mem_cons.mp hmem with hEq | hmem
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
            rfl
          · exfalso
            exact hnot (List.mem_map.mpr
              ⟨(label, child), hmem, hhead.trans hh.symm⟩)
      · rw [findEdge_cons, ite_eq_right hh, ih htail]
        constructor
        · rintro ⟨hmem, hhead⟩
          exact ⟨List.mem_cons_of_mem _ hmem, hhead⟩
        · rintro ⟨hmem, hhead⟩
          rcases List.mem_cons.mp hmem with hEq | hmem
          · exfalso
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
            exact hh hhead
          · exact ⟨hmem, hhead⟩

private theorem mem_childEntries_iff_exists {α : Type u} {β : Type v}
    {path : List α} {value : β} {children : List (List α × RadixTrie α β)} :
    (path, value) ∈ entries.childEntries children ↔
      ∃ label child keys, (label, child) ∈ children ∧
        (keys, value) ∈ child.entries ∧ path = label ++ keys := by
  induction children with
  | nil => simp [entries.childEntries]
  | cons head children ih =>
      rcases head with ⟨label', child'⟩
      rw [entries.childEntries, List.mem_append]
      constructor
      · intro hor
        rcases hor with hhead | htail
        · obtain ⟨entry, hentry, hEq⟩ := List.mem_map.mp hhead
          rcases entry with ⟨keys, result⟩
          have hparts := Prod.mk.inj hEq
          cases hparts.2
          exact ⟨label', child', keys, by simp, hentry, hparts.1.symm⟩
        · obtain ⟨label, child, keys, hmem, hentry, hpath⟩ := ih.mp htail
          exact ⟨label, child, keys, by simp [hmem], hentry, hpath⟩
      · rintro ⟨label, child, keys, hmem, hentry, hpath⟩
        rcases List.mem_cons.mp hmem with hEq | hmem
        · have hparts := Prod.mk.inj hEq
          cases hparts.1
          cases hparts.2
          apply Or.inl
          exact List.mem_map.mpr ⟨(keys, value), hentry, by
            simp only
            exact congrArg (fun p => (p, value)) hpath.symm⟩
        · exact Or.inr (ih.mpr ⟨label, child, keys, hmem, hentry, hpath⟩)

private theorem head?_eq_of_append {α : Type u} {c : α} {ks label keys : List α}
    (hne : label ≠ []) (hpath : (c :: ks) = label ++ keys) :
    label.head? = some c := by
  cases label with
  | nil => exact (hne rfl).elim
  | cons x xs =>
      have h2 : (c :: ks) = x :: (xs ++ keys) := hpath
      have hx : c = x := (List.cons.inj h2).1
      rw [List.head?_cons, hx]

/-- Lookup succeeds exactly when the pair occurs in `entries`, for valid tries. -/
theorem lookup_eq_some_iff_mem_entries {α : Type u} {β : Type v}
    [DecidableEq α] {trie : RadixTrie α β} (h : Valid trie) (keys : List α)
    (value : β) :
    trie.lookup keys = some value ↔ (keys, value) ∈ trie.entries := by
  induction hlen : keys.length using Nat.strongRecOn
      generalizing trie keys with
  | _ n ih =>
      cases keys with
      | nil =>
          cases trie with
          | node current children =>
              cases h with
              | @node _ _ hne hdist hval _ =>
                  have hnex : ¬ ∃ label child keys,
                      (label, child) ∈ children ∧
                      (keys, value) ∈ child.entries ∧ [] = label ++ keys := by
                    rintro ⟨label, child, keys, hmem, -, hnil⟩
                    have hlabel : label = [] :=
                      (List.append_eq_nil_iff.mp hnil.symm).1
                    exact hne (label, child) hmem hlabel
                  have hfalse : (∃ label child keys,
                      (label, child) ∈ children ∧
                      (keys, value) ∈ child.entries ∧
                      ([] : List α) = label ++ keys) = False :=
                    propext ⟨hnex, False.elim⟩
                  simp only [lookup_nil, entries, List.mem_append]
                  rw [mem_childEntries_iff_exists, hfalse]
                  cases current <;> simp [eq_comm]
      | cons c ks =>
          cases trie with
          | node current children =>
              cases h with
              | @node _ _ hne hdist hval _ =>
                  have hroot : (c :: ks, value) ∉
                      (match current with
                       | none => []
                       | some result => [([], result)]) := by
                    cases current <;> simp
                  simp only [entries, List.mem_append, hroot, false_or]
                  rw [lookup_node_cons, mem_childEntries_iff_exists]
                  cases hfind : findEdge c children with
                  | none =>
                      constructor
                      · intro hcontra
                        cases hcontra
                      · rintro ⟨label, child, keys, hmem, -, hpath⟩
                        have hhead : label.head? = some c :=
                          head?_eq_of_append (hne (label, child) hmem) hpath
                        have hfe := (findEdge_eq_some_iff hdist).mpr
                          ⟨hmem, hhead⟩
                        rw [hfind] at hfe
                        cases hfe
                  | some edge =>
                      rcases edge with ⟨label, child⟩
                      have hmem : (label, child) ∈ children :=
                        findEdge_some_mem hfind
                      have hchildValid : Valid child :=
                        hval (label, child) hmem
                      have hhead : label.head? = some c :=
                        findEdge_some_head hfind
                      obtain ⟨ls, rfl⟩ := exists_cons_of_head?_eq_some hhead
                      show (if commonPrefix (c :: ks) (c :: ls) = (c :: ls)
                          then lookup child ((c :: ks).drop (c :: ls).length)
                        else none) = some value ↔ _
                      by_cases hcond :
                          commonPrefix (c :: ks) (c :: ls) = (c :: ls)
                      · rw [ite_eq_left hcond]
                        have happend : (c :: ks) =
                            (c :: ls) ++ (c :: ks).drop (c :: ls).length :=
                          append_of_commonPrefix_eq hcond
                        have hlt : ((c :: ks).drop (c :: ls).length).length <
                            n := by
                          have h1 : 0 < (c :: ls).length := by
                            rw [List.length_cons]
                            omega
                          have h2 : 0 < (c :: ks).length := by
                            rw [List.length_cons]
                            omega
                          rw [← hlen, List.length_drop]
                          omega
                        rw [ih _ hlt hchildValid _ rfl]
                        constructor
                        · intro hentry
                          exact ⟨(c :: ls), child,
                            (c :: ks).drop (c :: ls).length, hmem, hentry,
                            happend⟩
                        · rintro ⟨label', child', keys', hmem', hentry',
                            hpath⟩
                          have hhead' : label'.head? = some c :=
                            head?_eq_of_append (hne (label', child') hmem')
                              hpath
                          have hfe := (findEdge_eq_some_iff hdist).mpr
                            ⟨hmem', hhead'⟩
                          rw [hfind] at hfe
                          obtain ⟨rfl, rfl⟩ :=
                            Prod.mk.inj (Option.some.inj hfe)
                          have hkeys' : keys' =
                              (c :: ks).drop (c :: ls).length := by
                            rw [hpath, List.drop_append_length]
                          rw [← hkeys']
                          exact hentry'
                      · rw [ite_eq_right hcond]
                        constructor
                        · intro hcontra
                          cases hcontra
                        · rintro ⟨label', child', keys', hmem', -, hpath⟩
                          have hhead' : label'.head? = some c :=
                            head?_eq_of_append (hne (label', child') hmem')
                              hpath
                          have hfe := (findEdge_eq_some_iff hdist).mpr
                            ⟨hmem', hhead'⟩
                          rw [hfind] at hfe
                          obtain ⟨rfl, rfl⟩ :=
                            Prod.mk.inj (Option.some.inj hfe)
                          exact (hcond
                            (commonPrefix_eq_of_append hpath)).elim

/-- A key is stored exactly when its lookup succeeds, for valid tries. -/
theorem mem_keys_iff {α : Type u} {β : Type v} [DecidableEq α]
    {trie : RadixTrie α β} (h : Valid trie) (key : List α) :
    key ∈ trie.keys ↔ ∃ value, trie.lookup key = some value := by
  rw [keys, List.mem_map]
  constructor
  · rintro ⟨⟨k, v⟩, hmem, hk⟩
    obtain rfl : key = k := hk.symm
    exact ⟨v, (lookup_eq_some_iff_mem_entries h key v).mpr hmem⟩
  · rintro ⟨v, hv⟩
    exact ⟨(key, v), (lookup_eq_some_iff_mem_entries h key v).mp hv, rfl⟩

/-! ## Prefix search, bulk construction, and key uniqueness

Generic `RadixTrie` API (moved here from the suffix-tree module, which is a
client of it): prefix search (`hasPrefix`) and its correctness against
`keys`, building a trie from a list of pairs (`buildFrom`) with lookup and
key characterizations, and duplicate-freeness of stored keys
(`Valid.keys_nodup`). -/

private theorem commonPrefix_comm {γ : Type u} [DecidableEq γ] (xs ys : List γ) :
    commonPrefix xs ys = commonPrefix ys xs := by
  induction xs generalizing ys with
  | nil => rw [commonPrefix_nil_left, commonPrefix_nil_right]
  | cons a xs ih =>
      cases ys with
      | nil => rfl
      | cons b ys =>
          by_cases h : a = b
          · subst h
            rw [commonPrefix_cons_cons, commonPrefix_cons_cons, ite_eq_left rfl, ite_eq_left rfl, ih]
          · rw [commonPrefix_cons_cons, commonPrefix_cons_cons, ite_eq_right h,
              ite_eq_right (Ne.symm h)]

/-- A list prefixes another exactly when it is their longest common prefix. -/
private theorem isPrefix_iff_commonPrefix_eq {γ : Type u} [DecidableEq γ]
    {p l : List γ} : p <+: l ↔ commonPrefix p l = p := by
  constructor
  · rintro ⟨t, ht⟩
    rw [commonPrefix_comm p l]
    exact commonPrefix_eq_of_append ht.symm
  · intro h
    have h1 := append_drop_commonPrefix_left l p
    rw [commonPrefix_comm l p, h] at h1
    exact ⟨l.drop p.length, h1.symm⟩

/--
If `p` prefixes `l ++ k`, the longest common prefix of `p` and `l` is one of the two:
`p` and `l` cannot diverge.
-/
private theorem commonPrefix_eq_or_of_isPrefix_append {γ : Type u} [DecidableEq γ]
    {p l k : List γ} (h : p <+: l ++ k) :
    commonPrefix p l = p ∨ commonPrefix p l = l := by
  obtain ⟨p', l', hp, hl, hdiv⟩ := commonPrefix_spec p l
  rcases hdiv with rfl | rfl | ⟨x, xs, y, ys, rfl, rfl, hxy⟩
  · exact Or.inl (by simpa using hp.symm)
  · exact Or.inr (by simpa using hl.symm)
  · exfalso
    obtain ⟨t, ht⟩ := h
    have ht2 : (commonPrefix p l ++ (x :: xs)) ++ t =
        (commonPrefix p l ++ (y :: ys)) ++ k := by
      rw [← hp, ← hl]
      exact ht
    simp only [List.append_assoc, List.cons_append] at ht2
    exact hxy (List.cons.inj (List.append_cancel_left ht2)).1

private theorem head?_append_of_ne_nil {γ : Type u} {label : List γ} (h : label ≠ [])
    (k : List γ) : (label ++ k).head? = label.head? := by
  cases label with
  | nil => simp at h
  | cons a as => rfl

private theorem head?_eq_some_of_isPrefix_append {γ : Type u} {label k : List γ}
    (hne : label ≠ []) {c : γ} {cs : List γ} (h : c :: cs <+: label ++ k) :
    label.head? = some c := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨a, as, rfl⟩ : ∃ a as, label = a :: as := by
    cases label with
    | nil => simp at hne
    | cons a as => exact ⟨a, as, rfl⟩
  simp only [List.cons_append] at ht
  rw [List.head?_cons, ← (List.cons.inj ht).1]

private theorem not_isPrefix_cons_nil {γ : Type u} {c : γ} {cs : List γ} :
    ¬ ((c :: cs) <+: ([] : List γ)) := by
  rintro ⟨t, ht⟩
  simp at ht

/--
In a node whose edge heads are distinct, `findEdge` finds a stored edge whose label
starts with `c`.
-/
private theorem findEdge_eq_some_of_mem {γ : Type u} {β : Type v} [DecidableEq γ]
    {children : List (List γ × RadixTrie γ β)}
    (hdist : (children.map (fun e => e.1.head?)).Nodup)
    {label : List γ} {child : RadixTrie γ β} (hmem : (label, child) ∈ children)
    {c : γ} (hhead : label.head? = some c) :
    findEdge c children = some (label, child) := by
  induction children with
  | nil => simp at hmem
  | cons head rest ih =>
      rcases head with ⟨label₀, child₀⟩
      have hnot : label₀.head? ∉ rest.map (fun e => e.1.head?) :=
        (List.nodup_cons.mp hdist).1
      have hdist_rest : (rest.map (fun e => e.1.head?)).Nodup :=
        (List.nodup_cons.mp hdist).2
      by_cases hh : label₀.head? = some c
      · rw [findEdge_cons, ite_eq_left hh]
        rcases List.mem_cons.mp hmem with hEq | hmem
        · rw [hEq]
        · exfalso
          apply hnot
          have hEq : label₀.head? = label.head? := by rw [hh, hhead]
          rw [hEq]
          exact List.mem_map.mpr ⟨(label, child), hmem, rfl⟩
      · rw [findEdge_cons, ite_eq_right hh]
        rcases List.mem_cons.mp hmem with hEq | hmem
        · obtain ⟨rfl, -⟩ := Prod.mk.inj hEq
          exact absurd hhead hh
        · exact ih hdist_rest hmem

private theorem mem_childEntries_iff {γ : Type u} {β : Type v}
    {children : List (List γ × RadixTrie γ β)} {path : List γ} {val : β} :
    (path, val) ∈ entries.childEntries children ↔
      ∃ label child ks, (label, child) ∈ children ∧ (ks, val) ∈ child.entries ∧
        path = label ++ ks := by
  induction children with
  | nil => simp [entries.childEntries]
  | cons head rest ih =>
      rcases head with ⟨label, child⟩
      rw [entries.childEntries, List.mem_append, ih]
      constructor
      · rintro (h | ⟨label', child', ks, hmem, hks, rfl⟩)
        · rw [List.mem_map] at h
          obtain ⟨⟨ks, v'⟩, hks, hEq⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
          exact ⟨label, child, ks, by simp, hks, rfl⟩
        · exact ⟨label', child', ks, List.mem_cons_of_mem _ hmem, hks, rfl⟩
      · rintro ⟨label', child', ks, hmem, hks, rfl⟩
        rcases List.mem_cons.mp hmem with hEq | hmem
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
          exact Or.inl (List.mem_map.mpr ⟨(ks, val), hks, rfl⟩)
        · exact Or.inr ⟨label', child', ks, hmem, hks, rfl⟩

private theorem mem_entries_node_iff {γ : Type u} {β : Type v} {value : Option β}
    {children : List (List γ × RadixTrie γ β)} {path : List γ} {val : β} :
    (path, val) ∈ (RadixTrie.node value children).entries ↔
      (path = [] ∧ value = some val) ∨
        ∃ label child ks, (label, child) ∈ children ∧ (ks, val) ∈ child.entries ∧
          path = label ++ ks := by
  simp only [entries, List.mem_append]
  rw [mem_childEntries_iff]
  cases value with
  | none => simp
  | some v₀ =>
      simp only [List.mem_singleton, Prod.mk.injEq, Option.some.injEq]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · exact Or.inl ⟨h1, h2.symm⟩
        · exact Or.inr h
      · rintro (⟨h1, h2⟩ | h)
        · exact Or.inl ⟨h1, h2.symm⟩
        · exact Or.inr h

private theorem mem_keys_node_iff {γ : Type u} {β : Type v} {value : Option β}
    {children : List (List γ × RadixTrie γ β)} {path : List γ} :
    path ∈ (RadixTrie.node value children).keys ↔
      (path = [] ∧ ∃ v, value = some v) ∨
        ∃ label child ks, (label, child) ∈ children ∧ ks ∈ child.keys ∧
          path = label ++ ks := by
  rw [keys, List.mem_map]
  constructor
  · rintro ⟨⟨p, val⟩, hmem, rfl⟩
    rw [mem_entries_node_iff] at hmem
    rcases hmem with ⟨rfl, hv⟩ | ⟨label, child, ks, hmemc, hmemk, rfl⟩
    · exact Or.inl ⟨rfl, val, hv⟩
    · exact Or.inr ⟨label, child, ks, hmemc,
        by rw [keys, List.mem_map]; exact ⟨(ks, val), hmemk, rfl⟩, rfl⟩
  · rintro (⟨rfl, val, hv⟩ | ⟨label, child, ks, hmemc, hk, rfl⟩)
    · exact ⟨([], val), mem_entries_node_iff.mpr (Or.inl ⟨rfl, hv⟩), rfl⟩
    · rw [keys, List.mem_map] at hk
      obtain ⟨⟨p, val⟩, hmemk, hp⟩ := hk
      obtain rfl : ks = p := hp.symm
      exact ⟨(label ++ ks, val),
        mem_entries_node_iff.mpr (Or.inr ⟨label, child, ks, hmemc, hmemk, rfl⟩), rfl⟩

private theorem nodup_childKeys {γ : Type u} {β : Type v}
    {children : List (List γ × RadixTrie γ β)}
    (hne : ∀ e ∈ children, e.1 ≠ [])
    (hdist : (children.map (fun e => e.1.head?)).Nodup)
    (hchild : ∀ e ∈ children, e.2.keys.Nodup) :
    ((entries.childEntries children).map Prod.fst).Nodup := by
  induction children with
  | nil => simp [entries.childEntries]
  | cons head rest ih =>
      rcases head with ⟨label, child⟩
      have hne_head : label ≠ [] := hne (label, child) (by simp)
      have hne_rest : ∀ e ∈ rest, e.1 ≠ [] :=
        fun e he => hne e (List.mem_cons_of_mem _ he)
      have hchild_head : child.keys.Nodup := hchild (label, child) (by simp)
      have hchild_rest : ∀ e ∈ rest, e.2.keys.Nodup :=
        fun e he => hchild e (List.mem_cons_of_mem _ he)
      have hnot : label.head? ∉ rest.map (fun e => e.1.head?) :=
        (List.nodup_cons.mp hdist).1
      have hdist_rest : (rest.map (fun e => e.1.head?)).Nodup :=
        (List.nodup_cons.mp hdist).2
      have ihr := ih hne_rest hdist_rest hchild_rest
      rw [entries.childEntries, List.map_append]
      have hmap : (child.entries.map (fun (ks, r) => (label ++ ks, r))).map Prod.fst =
          child.keys.map (fun ks => label ++ ks) := by
        rw [keys, List.map_map, List.map_map]
        apply List.map_congr_left
        rintro ⟨ks, r⟩ -
        rfl
      rw [hmap, List.nodup_append]
      refine ⟨List.Pairwise.map (f := fun ks => label ++ ks) (fun a b hab => by simpa using hab) hchild_head, ihr, ?_⟩
      intro x hx y hxrest hxy
      subst hxy
      obtain ⟨ks, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨⟨p, val⟩, hp, hpEq⟩ := List.mem_map.mp hxrest
      have hpeq : p = label ++ ks := hpEq
      obtain ⟨label', child', ks', hmem', -, hp'⟩ := mem_childEntries_iff.mp hp
      have h1 : (label ++ ks).head? = label.head? := head?_append_of_ne_nil hne_head ks
      have h2 : (label ++ ks).head? = label'.head? := by
        rw [← hpeq, hp']
        exact head?_append_of_ne_nil (hne_rest _ hmem') ks'
      exact hnot (by
        rw [← h1, h2]
        exact List.mem_map.mpr ⟨(label', child'), hmem', rfl⟩)

/-- The stored keys of a valid radix trie are duplicate-free. -/
theorem Valid.keys_nodup {γ : Type u} {β : Type v} {t : RadixTrie γ β} (h : Valid t) :
    t.keys.Nodup := by
  induction h with
  | node hne hdist hvalid hcompact ih =>
      rename_i value children
      have hchild := nodup_childKeys hne hdist ih
      rw [keys]
      simp only [entries, List.map_append]
      cases value with
      | none => simpa using hchild
      | some v =>
          have hnotmem : ([] : List γ) ∉ (entries.childEntries children).map Prod.fst := by
            intro hmem
            obtain ⟨⟨p, w⟩, hp, hpEq⟩ := List.mem_map.mp hmem
            have hpeq : p = [] := hpEq
            obtain ⟨label, child, ks, hmemc, -, hp'⟩ := mem_childEntries_iff.mp hp
            rw [hpeq] at hp'
            exact hne _ hmemc (List.append_eq_nil_iff.mp hp'.symm).1
          show (([] : List γ) :: (entries.childEntries children).map Prod.fst).Nodup
          exact List.nodup_cons.mpr ⟨hnotmem, hchild⟩

/--
Whether some key stored in the trie extends `p`. The walk follows the edge whose label
starts with the pattern's head symbol; it succeeds when the pattern ends inside that
edge (with a stored key below) or at a node reached by consuming whole edges.
-/
def hasPrefix {γ : Type u} {β : Type v} [DecidableEq γ] (t : RadixTrie γ β)
    (p : List γ) : Bool :=
  match t, p with
  | t, [] => !t.keys.isEmpty
  | .node _ children, (c :: cs) =>
      match _hfind : findEdge c children with
      | none => false
      | some (label, child) =>
          if commonPrefix (c :: cs) label = (c :: cs) then !child.keys.isEmpty
          else if commonPrefix (c :: cs) label = label then
            hasPrefix child ((c :: cs).drop label.length)
          else false
termination_by p.length
decreasing_by
  have hhead := findEdge_some_head _hfind
  obtain ⟨ls, rfl⟩ := exists_cons_of_head?_eq_some hhead
  simp only [List.length_drop, List.length_cons]
  omega

theorem hasPrefix_nil {γ : Type u} {β : Type v} [DecidableEq γ] (t : RadixTrie γ β) :
    t.hasPrefix [] = !t.keys.isEmpty := by
  simp only [hasPrefix]

theorem hasPrefix_cons_none {γ : Type u} {β : Type v} [DecidableEq γ]
    (value : Option β) (children : List (List γ × RadixTrie γ β)) (c : γ) (cs : List γ)
    (hfind : findEdge c children = none) :
    (RadixTrie.node value children).hasPrefix (c :: cs) = false := by
  simp only [hasPrefix]
  rw [hfind]

theorem hasPrefix_cons_some {γ : Type u} {β : Type v} [DecidableEq γ]
    (value : Option β) (children : List (List γ × RadixTrie γ β)) (c : γ) (cs : List γ)
    (label : List γ) (child : RadixTrie γ β)
    (hfind : findEdge c children = some (label, child)) :
    (RadixTrie.node value children).hasPrefix (c :: cs) =
      if commonPrefix (c :: cs) label = (c :: cs) then !child.keys.isEmpty
      else if commonPrefix (c :: cs) label = label then
        child.hasPrefix ((c :: cs).drop label.length)
      else false := by
  simp only [hasPrefix]
  rw [hfind]

private theorem exists_mem_of_keys_nonempty {γ : Type u} {β : Type v}
    {t : RadixTrie γ β} (h : (!t.keys.isEmpty) = true) : ∃ k, k ∈ t.keys := by
  cases hk : t.keys with
  | nil => simp [hk] at h
  | cons a as => exact ⟨a, by simp⟩

private theorem keys_nonempty_of_mem {γ : Type u} {β : Type v} {t : RadixTrie γ β}
    {k : List γ} (h : k ∈ t.keys) : (!t.keys.isEmpty) = true := by
  cases hk : t.keys with
  | nil => simp [hk] at h
  | cons a as => rfl

/-- Prefix search succeeds exactly when some stored key extends the pattern. -/
theorem hasPrefix_eq_true_iff {γ : Type u} {β : Type v} [DecidableEq γ]
    {t : RadixTrie γ β} (h : Valid t) (p : List γ) :
    t.hasPrefix p = true ↔ ∃ k ∈ t.keys, p <+: k := by
  induction hlen : p.length using Nat.strongRecOn generalizing t p with
  | _ n ih =>
      cases t with
      | node value children =>
          cases h with
          | node hne hdist hvalid =>
              cases p with
              | nil =>
                  rw [hasPrefix_nil]
                  constructor
                  · intro hnonempty
                    obtain ⟨k, hk⟩ := exists_mem_of_keys_nonempty hnonempty
                    exact ⟨k, hk, ⟨k, rfl⟩⟩
                  · rintro ⟨k, hk, -⟩
                    exact keys_nonempty_of_mem hk
              | cons c cs =>
                  cases hfind : findEdge c children with
                  | none =>
                      rw [hasPrefix_cons_none value children c cs hfind]
                      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
                      intro k hk hpre
                      rw [mem_keys_node_iff] at hk
                      rcases hk with ⟨rfl, -⟩ | ⟨label, child, ks, hmem, -, rfl⟩
                      · exact not_isPrefix_cons_nil hpre
                      · have hhead : label.head? = some c :=
                          head?_eq_some_of_isPrefix_append (hne _ hmem) hpre
                        exact findEdge_eq_none_imp hfind _ hmem hhead
                  | some lc =>
                      rcases lc with ⟨label, child⟩
                      rw [hasPrefix_cons_some value children c cs label child hfind]
                      have hmem : (label, child) ∈ children := findEdge_some_mem hfind
                      have hne_label : label ≠ [] := hne _ hmem
                      have hchild : Valid child := hvalid _ hmem
                      have key_decomp : ∀ k ∈ (RadixTrie.node value children).keys,
                          (c :: cs) <+: k → ∃ k' ∈ child.keys, k = label ++ k' := by
                        intro k hk hpre
                        rw [mem_keys_node_iff] at hk
                        rcases hk with ⟨rfl, -⟩ |
                          ⟨label', child', k', hmem', hk', rfl⟩
                        · exact absurd hpre not_isPrefix_cons_nil
                        · have hhead' : label'.head? = some c :=
                            head?_eq_some_of_isPrefix_append (hne _ hmem') hpre
                          have hfind' := findEdge_eq_some_of_mem hdist hmem' hhead'
                          rw [hfind] at hfind'
                          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hfind')
                          exact ⟨k', hk', rfl⟩
                      by_cases hcp1 : commonPrefix (c :: cs) label = (c :: cs)
                      · rw [ite_eq_left hcp1]
                        constructor
                        · intro hnonempty
                          obtain ⟨k', hk'⟩ := exists_mem_of_keys_nonempty hnonempty
                          refine ⟨label ++ k', ?_, ?_⟩
                          · rw [mem_keys_node_iff]
                            exact Or.inr ⟨label, child, k', hmem, hk', rfl⟩
                          · have h1 : (c :: cs) <+: label :=
                              isPrefix_iff_commonPrefix_eq.mpr hcp1
                            exact h1.trans ⟨k', rfl⟩
                        · rintro ⟨k, hk, hpre⟩
                          obtain ⟨k', hk', -⟩ := key_decomp k hk hpre
                          exact keys_nonempty_of_mem hk'
                      · rw [ite_eq_right hcp1]
                        by_cases hcp2 : commonPrefix (c :: cs) label = label
                        · rw [ite_eq_left hcp2]
                          have hlabelpre : label <+: (c :: cs) := by
                            rw [isPrefix_iff_commonPrefix_eq, commonPrefix_comm]
                            exact hcp2
                          obtain ⟨t₀, ht₀⟩ := hlabelpre
                          have hdrop : (c :: cs).drop label.length = t₀ := by
                            rw [← ht₀, List.drop_append_length]
                          have hlabelpos : 0 < label.length :=
                            Nat.pos_of_ne_zero (fun h0 =>
                              hne_label (List.length_eq_zero_iff.mp h0))
                          have hlen' : ((c :: cs).drop label.length).length < n := by
                            rw [← hlen, List.length_drop, List.length_cons]
                            omega
                          rw [ih _ hlen' hchild _ rfl]
                          constructor
                          · rintro ⟨k', hk', hpre'⟩
                            rw [hdrop] at hpre'
                            obtain ⟨t₁, ht₁⟩ := hpre'
                            refine ⟨label ++ k', ?_, ?_⟩
                            · rw [mem_keys_node_iff]
                              exact Or.inr ⟨label, child, k', hmem, hk', rfl⟩
                            · rw [← ht₀]
                              exact ⟨t₁, by rw [List.append_assoc, ht₁]⟩
                          · rintro ⟨k, hk, hpre⟩
                            obtain ⟨k', hk', rfl⟩ := key_decomp k hk hpre
                            refine ⟨k', hk', ?_⟩
                            rw [← ht₀] at hpre
                            obtain ⟨t₁, ht₁⟩ := hpre
                            rw [List.append_assoc] at ht₁
                            rw [hdrop]
                            exact ⟨t₁, List.append_cancel_left ht₁⟩
                        · rw [ite_eq_right hcp2]
                          simp only [Bool.false_eq_true, false_iff, not_exists,
                            not_and]
                          intro k hk hpre
                          obtain ⟨k', -, hkEq⟩ := key_decomp k hk hpre
                          rw [hkEq] at hpre
                          rcases commonPrefix_eq_or_of_isPrefix_append hpre with
                            hcp | hcp
                          · exact hcp1 hcp
                          · exact hcp2 hcp

/--
The trie built from a list of key-value pairs by inserting the head pair last. Later
pairs in the list are inserted first, so on duplicate keys the head-most value wins.
-/
def buildFrom {γ : Type u} {β : Type v} [DecidableEq γ] :
    List (List γ × β) → RadixTrie γ β
  | [] => empty
  | (k, v) :: L => (buildFrom L).insert k v

theorem Valid.buildFrom {γ : Type u} {β : Type v} [DecidableEq γ]
    (L : List (List γ × β)) : Valid (buildFrom L) := by
  induction L with
  | nil => exact Valid.empty
  | cons kv L ih =>
      rcases kv with ⟨k, v⟩
      exact ih.insert k v

/-- Every listed key is found by lookup in the built trie, under some value. -/
theorem lookup_buildFrom_exists_of_mem {γ : Type u} {β : Type v} [DecidableEq γ]
    {L : List (List γ × β)} {k : List γ} {v : β} (h : (k, v) ∈ L) :
    ∃ v', (buildFrom L).lookup k = some v' := by
  induction L with
  | nil => simp at h
  | cons kv L ih =>
      rcases kv with ⟨k₀, v₀⟩
      show ∃ v', ((buildFrom L).insert k₀ v₀).lookup k = some v'
      rcases List.mem_cons.mp h with hEq | hmem
      · obtain ⟨rfl, -⟩ := Prod.mk.inj hEq
        exact ⟨v₀, lookup_insert_same _ _ _⟩
      · by_cases hk : k = k₀
        · subst hk
          exact ⟨v₀, lookup_insert_same _ _ _⟩
        · obtain ⟨v', hv'⟩ := ih hmem
          exact ⟨v', by rw [lookup_insert_of_ne _ _ hk]; exact hv'⟩

/-- Every key found by lookup in the built trie comes from the list, with its value. -/
theorem mem_of_lookup_buildFrom {γ : Type u} {β : Type v} [DecidableEq γ]
    {L : List (List γ × β)} {k : List γ} {v : β}
    (h : (buildFrom L).lookup k = some v) : (k, v) ∈ L := by
  induction L with
  | nil => simp [buildFrom] at h
  | cons kv L ih =>
      rcases kv with ⟨k₀, v₀⟩
      change ((buildFrom L).insert k₀ v₀).lookup k = some v at h
      by_cases hk : k = k₀
      · subst hk
        have hsame := lookup_insert_same (buildFrom L) k v₀
        rw [hsame] at h
        obtain rfl : v₀ = v := Option.some.inj h
        simp
      · rw [lookup_insert_of_ne _ _ hk] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- The stored keys of the built trie are exactly the listed keys. -/
theorem mem_keys_buildFrom {γ : Type u} {β : Type v} [DecidableEq γ]
    {L : List (List γ × β)} {k : List γ} :
    k ∈ (buildFrom L).keys ↔ ∃ v, (k, v) ∈ L := by
  rw [mem_keys_iff (Valid.buildFrom L)]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, mem_of_lookup_buildFrom hv⟩
  · rintro ⟨v, hv⟩
    exact lookup_buildFrom_exists_of_mem hv

/-- With duplicate-free keys, lookup in the built trie returns the listed value. -/
theorem lookup_buildFrom_of_mem {γ : Type u} {β : Type v} [DecidableEq γ]
    {L : List (List γ × β)} (hnd : (L.map Prod.fst).Nodup) {k : List γ} {v : β}
    (h : (k, v) ∈ L) : (buildFrom L).lookup k = some v := by
  induction L with
  | nil => simp at h
  | cons kv L ih =>
      rcases kv with ⟨k₀, v₀⟩
      have hnot : k₀ ∉ L.map Prod.fst := (List.nodup_cons.mp hnd).1
      have hnd' : (L.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      show ((buildFrom L).insert k₀ v₀).lookup k = some v
      rcases List.mem_cons.mp h with hEq | hmem
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
        exact lookup_insert_same _ _ _
      · have hk : k ≠ k₀ := fun hkk =>
          hnot (hkk ▸ List.mem_map.mpr ⟨(k, v), hmem, rfl⟩)
        rw [lookup_insert_of_ne _ _ hk]
        exact ih hnd' hmem

end RadixTrie

end Cslib.Algorithms.Lean
