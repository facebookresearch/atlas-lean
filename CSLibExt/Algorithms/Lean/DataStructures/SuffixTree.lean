/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.RadixTrie
public import CSLibExt.Algorithms.Lean.DataStructures.SuffixArray
public import Mathlib.Data.List.Basic

/-!
# Suffix trees

The suffix tree of a list `s` is the radix (Patricia) trie of all suffixes of the
terminated string `s.map some ++ [none]`, over the alphabet `Option α` with `none` as a
fresh terminator (each terminated suffix contains `none` only at its end, so as strings
no terminated suffix is a prefix of another). Each suffix is stored with its starting
index as the value, so the stored keys are exactly the `s.length + 1` suffixes of the
terminated string, and exact lookup of a suffix returns its starting index. The API
is stated about stored keys; identifying them with the structural leaves of the trie
(the value-bearing nodes with no children) is not formalized here.

Pattern search is prefix lookup: `RadixTrie.hasPrefix` walks the trie following the edge
sharing the pattern's first symbol, succeeding when the pattern ends inside an edge or
at a node above stored keys. The main theorems state that `(suffixTree s).hasPrefix
(p.map some)` holds exactly when `p` is a prefix of some suffix of `s`, and equivalently
when `p <:+: s`.

The generic `RadixTrie` facts the construction needs — prefix search and its
correctness against `keys`, building a trie from a list of pairs (`buildFrom`)
with lookup and key characterizations, and duplicate-freeness of stored keys —
live in `RadixTrie.lean` with the rest of the radix-trie API, so radix-trie
clients do not import suffix-tree or suffix-array code.

Construction is naive insertion of all suffixes, taking quadratic total input length in
`s.length`. Out of scope: the linear-time Ukkonen construction, suffix links, a
structural characterization of trie leaves (and their coincidence with the stored
keys), and any in-order correspondence with the suffix array. The construction here
is the suffix-tree representation; it reuses `RadixTrie` directly, and no separate
compact-trie node type is exported.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

namespace SuffixTree

variable {α : Type u} [DecidableEq α]

/-- **Terminated string.** For a list $s = (s_0, \dots, s_{n-1})$ over $\alpha$, the terminated
string of $s$ is the list $(\mathrm{some}\,s_0, \dots, \mathrm{some}\,s_{n-1}, \mathrm{none})$
over $\mathrm{Option}\,\alpha$: every symbol of $s$ tagged $\mathrm{some}$, followed by the
terminator $\mathrm{none}$. -/
def terminated (s : List α) : List (Option α) :=
  s.map some ++ [none]

omit [DecidableEq α] in
@[simp] theorem terminated_length (s : List α) :
    (terminated s).length = s.length + 1 := by
  simp [terminated]

omit [DecidableEq α] in
theorem terminated_drop (s : List α) {i : Nat} (hi : i ≤ s.length) :
    (terminated s).drop i = (s.drop i).map some ++ [none] := by
  have hlen : i ≤ (s.map some).length := by rwa [List.length_map]
  rw [terminated, List.drop_append_of_le_length hlen, ← List.map_drop]

omit [DecidableEq α] in
/-- **Suffixes of the terminated string.** For a list $s$ over $\alpha$ and a natural number
$i \le |s|$, removing the first $i$ entries of the terminated string of $s$ gives the suffix
of $s$ starting at index $i$ with every symbol tagged $\mathrm{some}$, followed by
$\mathrm{none}$. -/
theorem terminated_drop_eq_suffix_map (s : List α) {i : Nat} (hi : i ≤ s.length) :
    (terminated s).drop i = (SuffixArray.suffix s i).map some ++ [none] :=
  terminated_drop s hi

/-- **Suffix entries of a string.** For a list $s = (s_0, \dots, s_{n-1})$ over $\alpha$, let
$\hat s = (\mathrm{some}\,s_0, \dots, \mathrm{some}\,s_{n-1}, \mathrm{none})$ be its
terminated string. The suffix entries of $s$ are the list of pairs $(\hat s_{\ge i}, i)$ for
$i = 0, 1, \dots, n$ in increasing order, where $\hat s_{\ge i}$ is $\hat s$ with its first
$i$ entries removed: each nonempty suffix of $\hat s$ paired with its starting index. -/
def suffixEntries (s : List α) : List (List (Option α) × Nat) :=
  (List.range (s.length + 1)).map (fun i => ((terminated s).drop i, i))

omit [DecidableEq α] in
theorem mem_suffixEntries {s : List α} {k : List (Option α)} {i : Nat} :
    (k, i) ∈ suffixEntries s ↔ i ≤ s.length ∧ k = (terminated s).drop i := by
  rw [suffixEntries, List.mem_map]
  constructor
  · rintro ⟨j, hj, hEq⟩
    obtain ⟨hk, rfl⟩ := Prod.mk.inj hEq
    exact ⟨Nat.le_of_lt_succ (List.mem_range.mp hj), hk.symm⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩

omit [DecidableEq α] in
theorem suffixEntries_map_fst (s : List α) :
    (suffixEntries s).map Prod.fst =
      (List.range (s.length + 1)).map (fun i => (terminated s).drop i) := by
  rw [suffixEntries, List.map_map]
  apply List.map_congr_left
  intro i _hi
  rfl

omit [DecidableEq α] in
/-- **Terminated suffixes are distinct.** Let $s$ be a list over $\alpha$. The lists obtained from
the terminated string of $s$ by removing its first $i$ symbols, for $i$ ranging over
$0, 1, \ldots, |s|$, are pairwise distinct.

They are distinct because their lengths differ. -/
theorem nodup_terminated_drops (s : List α) :
    ((List.range (s.length + 1)).map (fun i => (terminated s).drop i)).Nodup := by
  refine List.nodup_range.map_on ?_
  intro i hi j hj h
  rw [List.mem_range] at hi hj
  have hlen : (terminated s).length - i = (terminated s).length - j := by
    have h2 := congrArg List.length h
    rwa [List.length_drop, List.length_drop] at h2
  rw [terminated_length] at hlen
  omega

omit [DecidableEq α] in
theorem suffixEntries_fst_nodup (s : List α) :
    ((suffixEntries s).map Prod.fst).Nodup := by
  rw [suffixEntries_map_fst]
  exact nodup_terminated_drops s

/-- **Suffix tree.** For a list $s = (s_0, \dots, s_{n-1})$ over $\alpha$, let
$\hat s = (\mathrm{some}\,s_0, \dots, \mathrm{some}\,s_{n-1}, \mathrm{none})$ be its
terminated string over $\mathrm{Option}\,\alpha$. The suffix tree of $s$ is the radix trie
with keys over $\mathrm{Option}\,\alpha$ and natural-number values obtained from the empty
trie by inserting, for $i = n, n - 1, \dots, 0$ in this order, the suffix of $\hat s$
starting at index $i$ with value $i$. -/
def suffixTree (s : List α) : RadixTrie (Option α) Nat :=
  RadixTrie.buildFrom (suffixEntries s)

theorem valid_suffixTree (s : List α) : RadixTrie.Valid (suffixTree s) :=
  RadixTrie.Valid.buildFrom _

/-- **Lookup of a suffix returns its starting index.** Let $s$ be a list over $\alpha$ and $i$ a
natural number with $i \le |s|$. Looking up, in the suffix tree of $s$, the terminated string of
$s$ with its first $i$ symbols removed returns $i$. -/
theorem lookup_suffix {s : List α} {i : Nat} (hi : i ≤ s.length) :
    (suffixTree s).lookup ((terminated s).drop i) = some i :=
  RadixTrie.lookup_buildFrom_of_mem (suffixEntries_fst_nodup s)
    (mem_suffixEntries.mpr ⟨hi, rfl⟩)

/-- **Lookup in the suffix tree returns starting indices.** Let $s$ be a list over $\alpha$, let
$k$ be a list over $\alpha$ extended by a fresh terminator symbol, and let $i$ be a natural number.
If looking up $k$ in the suffix tree of $s$ returns $i$, then $i \le |s|$ and $k$ is the
terminated string of $s$ with its first $i$ symbols removed. -/
theorem eq_drop_of_lookup_suffixTree {s : List α} {k : List (Option α)} {i : Nat}
    (h : (suffixTree s).lookup k = some i) :
    i ≤ s.length ∧ k = (terminated s).drop i :=
  mem_suffixEntries.mp (RadixTrie.mem_of_lookup_buildFrom h)

/-- **The stored keys of a suffix tree are its terminated suffixes.** Let $s$ be a list over
$\alpha$. A key $k$ is stored in the suffix tree of $s$ if and only if there is a natural number
$i \le |s|$ such that $k$ is the terminated string of $s$ with its first $i$ symbols removed. -/
theorem mem_suffixTree_keys {s : List α} {k : List (Option α)} :
    k ∈ (suffixTree s).keys ↔ ∃ i ≤ s.length, k = (terminated s).drop i := by
  rw [suffixTree, RadixTrie.mem_keys_buildFrom]
  constructor
  · rintro ⟨v, hv⟩
    rw [mem_suffixEntries] at hv
    exact ⟨v, hv.1, hv.2⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, mem_suffixEntries.mpr ⟨hi, rfl⟩⟩

/-- **Stored keys of the suffix tree.** For a list $s$ over $\alpha$, the stored keys of $s$ form
the list of keys stored in the suffix tree of $s$, in stored sibling order.

They are exactly the terminated suffixes. This concerns stored keys, not structural trie leaves:
a valid radix trie may carry values at internal nodes, and no leaf characterization is claimed.
-/
def storedKeys (s : List α) : List (List (Option α)) :=
  (suffixTree s).keys

theorem mem_storedKeys_iff {s : List α} {k : List (Option α)} :
    k ∈ storedKeys s ↔ ∃ i ≤ s.length, k = (terminated s).drop i :=
  mem_suffixTree_keys

theorem storedKeys_nodup (s : List α) : (storedKeys s).Nodup :=
  (valid_suffixTree s).keys_nodup

/-- **The suffix tree stores one key per suffix.** For a list $s$ over $\alpha$, the list of
stored keys of the suffix tree of $s$ has length $|s| + 1$.

There is one key for each terminated suffix. -/
theorem storedKeys_length (s : List α) : (storedKeys s).length = s.length + 1 := by
  apply Nat.le_antisymm
  · have h := (storedKeys_nodup s).length_le_of_subset
      (l₂ := (List.range (s.length + 1)).map (fun i => (terminated s).drop i))
      (fun k hk => by
        obtain ⟨i, hi, rfl⟩ := mem_storedKeys_iff.mp hk
        exact List.mem_map.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩)
    simpa using h
  · have h := (nodup_terminated_drops s).length_le_of_subset (l₂ := storedKeys s)
      (fun k hk => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
        exact mem_storedKeys_iff.mpr
          ⟨i, Nat.le_of_lt_succ (List.mem_range.mp hi), rfl⟩)
    simpa using h

omit [DecidableEq α] in
/-- **A tagged pattern cannot reach past the terminator.** For lists $p$ and $q$ over $\alpha$,
view their symbols in $\alpha$ extended by a fresh terminator symbol. If $p$ is a prefix of $q$
followed by the terminator, then $p$ is a prefix of $q$.

The terminator differs from every symbol of $\alpha$, so the pattern cannot reach past it. -/
theorem isPrefix_of_map_some_prefix_append_none {p q : List α} :
    (p.map some) <+: (q.map some ++ [none]) → p <+: q := by
  induction p generalizing q with
  | nil => intro _; exact ⟨q, rfl⟩
  | cons a p ih =>
      intro h
      obtain ⟨t, ht⟩ := h
      cases q with
      | nil => simp at ht
      | cons b q =>
          simp only [List.map_cons, List.cons_append] at ht
          obtain ⟨hab, ht'⟩ := List.cons.inj ht
          have hab : a = b := Option.some.inj hab
          subst hab
          obtain ⟨t₂, ht₂⟩ := ih (q := q) ⟨t, ht'⟩
          exact ⟨t₂, by rw [List.cons_append, ht₂]⟩

omit [DecidableEq α] in
/-- **Infixes are prefixes of suffixes.** For lists $s$ and $p$, $p$ is an infix (a contiguous
sublist) of $s$ if and only if there is a natural number $i$ such that $p$ is a prefix of the list
obtained from $s$ by removing its first $i$ symbols. -/
theorem isInfix_iff_exists_isPrefix_drop {s p : List α} :
    p <:+: s ↔ ∃ i, p <+: s.drop i := by
  constructor
  · rintro ⟨pre, post, h⟩
    refine ⟨pre.length, ?_⟩
    rw [← h, List.append_assoc, List.drop_append_length]
    exact ⟨post, rfl⟩
  · rintro ⟨i, t, ht⟩
    exact ⟨s.take i, t, by rw [List.append_assoc, ht, List.take_append_drop]⟩

/-- **Suffix-tree search finds exactly the prefixes of suffixes.** For lists $s$ and $p$ over
$\alpha$, prefix search for $p$ (each symbol viewed in the alphabet extended by the terminator) in
the suffix tree of $s$ succeeds if and only if there is a natural number $i$ such that $p$ is a
prefix of the list obtained from $s$ by removing its first $i$ symbols. -/
theorem hasPrefix_suffixTree_iff_exists {s p : List α} :
    (suffixTree s).hasPrefix (p.map some) = true ↔ ∃ i, p <+: s.drop i := by
  rw [RadixTrie.hasPrefix_eq_true_iff (valid_suffixTree s)]
  constructor
  · rintro ⟨k, hk, hpre⟩
    obtain ⟨i, hi, rfl⟩ := mem_suffixTree_keys.mp hk
    rw [terminated_drop s hi] at hpre
    exact ⟨i, isPrefix_of_map_some_prefix_append_none hpre⟩
  · rintro ⟨i, hpre⟩
    by_cases hi : i ≤ s.length
    · obtain ⟨t, ht⟩ := hpre
      refine ⟨(terminated s).drop i, mem_suffixTree_keys.mpr ⟨i, hi, rfl⟩, ?_⟩
      rw [terminated_drop s hi]
      exact ⟨t.map some ++ [none], by
        rw [← List.append_assoc, ← List.map_append, ht]⟩
    · have hlen : p.length ≤ (s.drop i).length := hpre.length_le
      rw [List.length_drop] at hlen
      have hp : p = [] := by
        have h0 : p.length = 0 := by omega
        exact List.length_eq_zero_iff.mp h0
      subst hp
      refine ⟨[none], ?_, ⟨[none], by simp⟩⟩
      apply mem_suffixTree_keys.mpr
      refine ⟨s.length, le_refl _, ?_⟩
      rw [terminated_drop s (le_refl _)]
      simp

/-- **Suffix-tree search finds exactly the infixes.** For lists $s$ and $p$ over $\alpha$, prefix
search for $p$ (each symbol viewed in the alphabet extended by the terminator) in the suffix tree
of $s$ succeeds if and only if $p$ occurs in $s$ as a contiguous sublist (an infix). -/
theorem hasPrefix_suffixTree_iff_isInfix {s p : List α} :
    (suffixTree s).hasPrefix (p.map some) = true ↔ p <:+: s :=
  hasPrefix_suffixTree_iff_exists.trans isInfix_iff_exists_isPrefix_drop.symm

end SuffixTree

end Cslib.Algorithms.Lean
