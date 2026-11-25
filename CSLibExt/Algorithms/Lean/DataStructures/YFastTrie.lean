/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.XFastTrie

/-!
# Y-fast tries with sorted-list groups

A y-fast trie (Willard; Demaine, MIT 6.851 *Advanced Data Structures*, Lecture 11)
stores only Θ(n / w) representative keys in an x-fast trie and keeps the remaining
keys in balanced search trees ("groups") of Θ(w) keys each, where `w` is the key
length in bits. `XFastTrie.lean` already contains a `YFastTrie` skeleton whose
buckets are `Finset`s, with the bucket ordering invariant, the balanced-tree buckets,
and split/merge maintenance explicitly deferred. This file develops the grouped
refinement of that skeleton under the name `GroupedYFastTrie`: buckets become groups.

The tractable form proved here: the stored keys are partitioned into groups, each a
strictly sorted list of at most `B` keys (classically `B = Θ(w)`; here `B` is a
separate parameter), the groups appear in increasing order (every key of an earlier
group is smaller than every key of a later one), and the representative of a group is
its maximum (its last element). The representatives are stored in an `XFastTrie`. The
sorted lists are the stand-in for the classical balanced search trees: membership
scans a group list for the key and successor scans it for the first key above the
query. What is verified is exact semantics: `member` decides membership in `contents`
(the flattened groups), and `successor` returns the least stored key greater than the
query. Both queries follow the classical route: locate the relevant representative in
the x-fast trie (`repGe` for membership, from the deepest-level probe plus successor;
`XFastTrie.successor` for successor), fetch its group (`findGroup`), then scan the
group.

`ofSortedList B l` builds a trie from a strictly sorted list by cutting it into
consecutive chunks of length at most `B` — this bound, and validity of the
result, require `0 < B` (`valid_ofSortedList`). At `B = 0`, `chunkGroups`
degenerates to a single chunk `[l]` (no nonempty group has length at most
`0`), so `ofSortedList 0 l` is invalid for nonempty `l`
(`not_valid_ofSortedList_zero`); its contents are still exactly `l`, and the
member/successor specifications specialize to statements about `l` under
their stated `0 < B` hypotheses.

No complexity bound is claimed anywhere. In particular the representative successor
lookup is the order-theoretic `XFastTrie.successor` of the parent module (defined
from `contents`, not by binary search over levels), and group scans are linear list
scans, so neither the classical O(log w) query bound nor the O(n) space bound is
formalized. Insertion and deletion with the split/merge maintenance that keeps groups
at Θ(w) keys, and predecessor, are deferred.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

/-- A nonempty list has a last element. -/
private theorem getLast?_isSome {α : Type*} :
    ∀ {l : List α}, l ≠ [] → ∃ r, l.getLast? = some r
  | [], h => absurd rfl h
  | [a], _ => ⟨a, rfl⟩
  | _ :: b :: l, _ => getLast?_isSome (l := b :: l) (by simp)

/-- The last element of a weakly sorted list is a member and an upper bound. -/
private theorem getLast?_mem_le {α : Type*} [Preorder α] {l : List α}
    (hsorted : l.Pairwise (· ≤ ·)) {r : α} (hr : l.getLast? = some r) :
    r ∈ l ∧ ∀ a ∈ l, a ≤ r := by
  induction l with
  | nil => simp at hr
  | cons a l ih =>
      cases l with
      | nil =>
          have har : a = r := by simpa using hr
          subst har
          simp
      | cons b l =>
          have hlast : (a :: b :: l).getLast? = (b :: l).getLast? := rfl
          rw [hlast] at hr
          obtain ⟨head_le, tail_sorted⟩ := List.pairwise_cons.mp hsorted
          obtain ⟨hr_mem, hr_le⟩ := ih tail_sorted hr
          refine ⟨List.mem_cons_of_mem a hr_mem, fun x hx => ?_⟩
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact head_le r hr_mem
          · exact hr_le x hx

/-- Scanning a sorted list for the first element above `x` returns the least such
element when it succeeds. -/
private theorem find?_succ_some {α : Type*} [LinearOrder α] {l : List α}
    (hsorted : l.Pairwise (· ≤ ·)) {x y : α}
    (h : l.find? (fun z => decide (x < z)) = some y) :
    y ∈ l ∧ x < y ∧ ∀ z ∈ l, x < z → y ≤ z := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
      obtain ⟨head_le, tail_sorted⟩ := List.pairwise_cons.mp hsorted
      by_cases hxa : x < a
      · have hfind : (a :: l).find? (fun z => decide (x < z)) = some a := by
          simp [hxa]
        rw [hfind] at h
        have hay : a = y := Option.some.inj h
        subst hay
        refine ⟨List.mem_cons_self, hxa, fun z hz _ => ?_⟩
        rw [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact le_rfl
        · exact head_le z hz
      · have hfind : (a :: l).find? (fun z => decide (x < z)) =
            l.find? (fun z => decide (x < z)) := by
          simp [hxa]
        rw [hfind] at h
        obtain ⟨hy_mem, hxy, hy_least⟩ := ih tail_sorted h
        refine ⟨List.mem_cons_of_mem a hy_mem, hxy, fun z hz hxz => ?_⟩
        rw [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact (hxa hxz).elim
        · exact hy_least z hz hxz

/-- Scanning fails exactly when no element is above the query. -/
private theorem find?_succ_none {α : Type*} [LinearOrder α] {l : List α} {x : α}
    (h : l.find? (fun z => decide (x < z)) = none) : ∀ z ∈ l, ¬ x < z := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases hxa : x < a
      · have hfind : (a :: l).find? (fun z => decide (x < z)) = some a := by
          simp [hxa]
        rw [hfind] at h
        simp at h
      · have hfind : (a :: l).find? (fun z => decide (x < z)) =
            l.find? (fun z => decide (x < z)) := by
          simp [hxa]
        rw [hfind] at h
        intro z hz
        rw [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hxa
        · exact ih h z hz

/-- If some element of a list satisfies a boolean predicate, `find?` returns one. -/
private theorem find?_spec_of_exists {α : Type*} {p : α → Bool} {l : List α}
    (h : ∃ a ∈ l, p a = true) : ∃ a, l.find? p = some a ∧ a ∈ l ∧ p a = true := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
      cases hpa : p a with
      | true => exact ⟨a, by simp [hpa], List.mem_cons_self, hpa⟩
      | false =>
          obtain ⟨b, hb_mem, hb⟩ := h
          have hb' : ∃ c ∈ l, p c = true := by
            rw [List.mem_cons] at hb_mem
            rcases hb_mem with rfl | hb_mem
            · rw [hpa] at hb
              simp at hb
            · exact ⟨b, hb_mem, hb⟩
          obtain ⟨c, hc, hc_mem, hc_p⟩ := ih hb'
          exact ⟨c, by simp [hpa, hc], List.mem_cons_of_mem a hc_mem, hc_p⟩

/-- **Grouped y-fast trie.** For natural numbers $w$ and $B$, a grouped y-fast trie over $w$-bit
keys with group bound $B$ consists of an x-fast trie over $w$-bit keys, which holds the
representatives, and a list of groups, each a list of $w$-bit keys. The structure itself imposes
no condition on these fields; the intended invariants (the representative trie is a valid x-fast
trie whose keys are exactly the group maxima, every group is nonempty, strictly sorted and of
length at most $B$, and the groups are in increasing order) are imposed by the validity
predicate.

Each group is a sorted list standing in for a balanced search tree; no complexity bound is
claimed. -/
public structure GroupedYFastTrie (w B : Nat) where
  /-- The x-fast trie over representative keys (group maxima). -/
  reps : XFastTrie w
  /-- The groups, in increasing order. -/
  groups : List (List (Fin (2 ^ w)))

namespace GroupedYFastTrie

/-- **Keys of a grouped y-fast trie.** The key set of a grouped y-fast trie $t$ is the finite
set of all keys that occur in some group of $t$. -/
public def contents {w B : Nat} (t : GroupedYFastTrie w B) : Finset (Fin (2 ^ w)) :=
  t.groups.flatten.toFinset

/-- **Stored keys are the keys of the groups.** For every grouped y-fast trie $t$ over $w$-bit
keys and every key $x$, $x$ lies in the contents of $t$ if and only if $x$ belongs to some group
of $t$. -/
public theorem mem_contents_iff {w B : Nat} (t : GroupedYFastTrie w B)
    (x : Fin (2 ^ w)) : x ∈ t.contents ↔ ∃ g ∈ t.groups, x ∈ g := by
  simp [contents, List.mem_flatten]

/-- **Ordered list of groups.** A list of groups, each a list of $w$-bit keys, is group ordered
when every key of an earlier group is smaller than every key of a later group. -/
public def GroupOrdered {w : Nat} (gs : List (List (Fin (2 ^ w)))) : Prop :=
  gs.Pairwise (fun g₁ g₂ => ∀ a ∈ g₁, ∀ b ∈ g₂, a < b)

/-- **Validity of a grouped y-fast trie.** A grouped y-fast trie $t$ over keys in
$\{0, \dots, 2^w - 1\}$ with group bound $B$ is valid when its representative trie is a valid
x-fast trie; a key $r$ is stored in the representative trie exactly when $r$ is the last element
of some group of $t$; every group of $t$ is nonempty, has at most $B$ keys, and is strictly
increasing; and the groups of $t$ are ordered, that is, every key of an earlier group is smaller
than every key of a later group. -/
public def Valid {w B : Nat} (t : GroupedYFastTrie w B) : Prop :=
  t.reps.Valid ∧
    (∀ r, r ∈ t.reps.contents ↔ ∃ g ∈ t.groups, g.getLast? = some r) ∧
    (∀ g ∈ t.groups, g ≠ [] ∧ g.length ≤ B ∧ g.Pairwise (· < ·)) ∧
    GroupOrdered t.groups

/-- Every group of a valid trie has a maximum that is a representative. -/
private theorem Valid.group_last_spec {w B : Nat} {t : GroupedYFastTrie w B}
    (hv : t.Valid) {g : List (Fin (2 ^ w))} (hg : g ∈ t.groups) :
    ∃ r, g.getLast? = some r ∧ r ∈ g ∧ (∀ a ∈ g, a ≤ r) ∧ r ∈ t.reps.contents := by
  obtain ⟨hne, -, hsorted⟩ := hv.2.2.1 g hg
  obtain ⟨r, hr⟩ := getLast?_isSome hne
  obtain ⟨hr_mem, hr_le⟩ := getLast?_mem_le (hsorted.imp (fun h => h.le)) hr
  exact ⟨r, hr, hr_mem, hr_le, (hv.2.1 r).mpr ⟨g, hg, hr⟩⟩

/-- Two groups of an ordered group list are equal or lie in disjoint order. -/
private theorem groupOrdered_trichotomy {w : Nat} {gs : List (List (Fin (2 ^ w)))}
    (h : GroupOrdered gs) {g g' : List (Fin (2 ^ w))} (hg : g ∈ gs) (hg' : g' ∈ gs) :
    g = g' ∨ (∀ a ∈ g, ∀ b ∈ g', a < b) ∨ (∀ a ∈ g', ∀ b ∈ g, a < b) := by
  induction gs with
  | nil => simp at hg
  | cons hd gs ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
      rw [List.mem_cons] at hg hg'
      rcases hg with rfl | hg <;> rcases hg' with rfl | hg'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (hhead g' hg'))
      · exact Or.inr (Or.inr (hhead g hg))
      · exact ih htail hg hg'

/-- **Group of a representative.** For a grouped y-fast trie $t$ and a key $r$, the group of $r$
is the first group of $t$, in the order of the groups, whose last element is $r$, or the empty
list if no group of $t$ ends with $r$.

In a valid trie every group is strictly increasing, so its last element is its maximum. -/
public def findGroup {w B : Nat} (t : GroupedYFastTrie w B) (r : Fin (2 ^ w)) :
    List (Fin (2 ^ w)) :=
  (t.groups.find? (fun g => decide (g.getLast? = some r))).getD []

/-- The group of a genuine representative is in the group list and is owned by it. -/
private theorem findGroup_spec {w B : Nat} {t : GroupedYFastTrie w B} (hv : t.Valid)
    {r : Fin (2 ^ w)} (hr : r ∈ t.reps.contents) :
    t.findGroup r ∈ t.groups ∧ (t.findGroup r).getLast? = some r := by
  obtain ⟨g, hg_mem, hg_last⟩ := (hv.2.1 r).mp hr
  have hex : ∃ g' ∈ t.groups, (fun g => decide (g.getLast? = some r)) g' = true :=
    ⟨g, hg_mem, by simp [hg_last]⟩
  obtain ⟨g', hg'_find, hg'_mem, hg'_p⟩ := find?_spec_of_exists hex
  have hg'_last : g'.getLast? = some r := of_decide_eq_true hg'_p
  have hfg : t.findGroup r = g' := by
    rw [findGroup, hg'_find]
    rfl
  rw [hfg]
  exact ⟨hg'_mem, hg'_last⟩

/-- **Least representative at or above a key.** For a grouped y-fast trie $t$ and a key $x$,
the result is $x$ itself if the membership test of the representative x-fast trie of $t$ (a
single probe of its deepest level) reports $x$ as present. Otherwise it is the successor of $x$
in the representative x-fast trie, that is, the least representative greater than $x$, or
nothing if there is none.

When $t$ is valid, the result is the least representative $r$ with $x \le r$, and nothing
when there is no such representative. -/
public def repGe {w B : Nat} (t : GroupedYFastTrie w B) (x : Fin (2 ^ w)) :
    Option (Fin (2 ^ w)) :=
  if t.reps.member x = true then some x else t.reps.successor x

/-- `repGe` returns the least representative at least the query when it succeeds. -/
private theorem repGe_spec_some {w B : Nat} {t : GroupedYFastTrie w B} (hv : t.Valid)
    {x r : Fin (2 ^ w)} (h : t.repGe x = some r) :
    r ∈ t.reps.contents ∧ x ≤ r ∧ ∀ z ∈ t.reps.contents, x ≤ z → r ≤ z := by
  unfold repGe at h
  split at h
  · rename_i hmem
    have hxr : x = r := Option.some.inj h
    subst hxr
    have hx : x ∈ t.reps.contents := (XFastTrie.member_iff t.reps hv.1 x).mp hmem
    exact ⟨hx, le_rfl, fun z _ hxz => hxz⟩
  · rename_i hmem
    have hnotmem : x ∉ t.reps.contents := by
      rw [← XFastTrie.member_iff t.reps hv.1 x]
      exact hmem
    obtain ⟨hr_mem, hxr, hr_least⟩ :=
      (XFastTrie.successor_eq_some_iff t.reps x r).mp h
    refine ⟨hr_mem, hxr.le, fun z hz hxz => ?_⟩
    exact hr_least z hz (lt_of_le_of_ne hxz (fun hzx => hnotmem (hzx.symm ▸ hz)))

/-- `repGe` fails exactly when no representative is at least the query. -/
private theorem repGe_spec_none {w B : Nat} {t : GroupedYFastTrie w B} (hv : t.Valid)
    {x : Fin (2 ^ w)} (h : t.repGe x = none) :
    ∀ z ∈ t.reps.contents, ¬ x ≤ z := by
  unfold repGe at h
  split at h
  · simp at h
  · rename_i hmem
    have hnotmem : x ∉ t.reps.contents := by
      rw [← XFastTrie.member_iff t.reps hv.1 x]
      exact hmem
    have hnone := (XFastTrie.successor_eq_none_iff t.reps x).mp h
    intro z hz hxz
    exact hnone z hz (lt_of_le_of_ne hxz (fun hzx => hnotmem (hzx.symm ▸ hz)))

/-- **Membership query of a grouped y-fast trie.** Given a grouped y-fast trie $t$ over $w$-bit
keys and a key $x$, the query first finds a representative $r$: $r = x$ if the membership probe of
the representative x-fast trie accepts $x$, and otherwise $r$ is the successor of $x$ in the
representative trie. If there is no such $r$, the query returns false. Otherwise it returns
whether $x$ belongs to the group owned by $r$, namely the first group of $t$ whose last element is
$r$ (the empty list if there is none). -/
public def member {w B : Nat} (t : GroupedYFastTrie w B) (x : Fin (2 ^ w)) : Bool :=
  match t.repGe x with
  | none => false
  | some r => decide (x ∈ t.findGroup r)

/-- **Correctness of the y-fast trie membership query.** Let $t$ be a valid grouped y-fast trie
over $w$-bit keys. Then for every key $x$, the membership query on $t$ (locate the least
representative at least $x$, then scan its group) returns true at $x$ if and only if $x$ lies in
the contents of $t$. -/
public theorem member_iff {w B : Nat} {t : GroupedYFastTrie w B} (hv : t.Valid)
    (x : Fin (2 ^ w)) : t.member x = true ↔ x ∈ t.contents := by
  constructor
  · intro h
    cases hrep : t.repGe x with
    | none => simp [member, hrep] at h
    | some r =>
        have hx : x ∈ t.findGroup r :=
          of_decide_eq_true (by simpa [member, hrep] using h)
        have hr : r ∈ t.reps.contents := (repGe_spec_some hv hrep).1
        exact (mem_contents_iff t x).mpr ⟨t.findGroup r, (findGroup_spec hv hr).1, hx⟩
  · intro hx
    obtain ⟨g₀, hg₀_mem, hxg₀⟩ := (mem_contents_iff t x).mp hx
    obtain ⟨r₀, -, hr₀_mem, hr₀_le, hr₀_reps⟩ := hv.group_last_spec hg₀_mem
    have hx_le_r₀ : x ≤ r₀ := hr₀_le x hxg₀
    obtain ⟨r, hrep⟩ : ∃ r, t.repGe x = some r := by
      cases hrep : t.repGe x with
      | some r => exact ⟨r, rfl⟩
      | none => exact absurd hx_le_r₀ (repGe_spec_none hv hrep r₀ hr₀_reps)
    obtain ⟨hr_reps, hx_le_r, hr_least⟩ := repGe_spec_some hv hrep
    have hr_le_r₀ : r ≤ r₀ := hr_least r₀ hr₀_reps hx_le_r₀
    obtain ⟨hg_mem, hg_last⟩ := findGroup_spec hv hr_reps
    obtain ⟨r₁, hr₁_last, hr₁_mem, -, -⟩ := hv.group_last_spec hg_mem
    have hr₁ : r = r₁ := (Option.some.inj (hr₁_last.symm.trans hg_last)).symm
    subst hr₁
    have hxg : x ∈ t.findGroup r := by
      rcases groupOrdered_trichotomy hv.2.2.2 hg_mem hg₀_mem with heq | hlt | hgt
      · exact heq.symm ▸ hxg₀
      · exact absurd (hlt r hr₁_mem x hxg₀) (not_lt_of_ge hx_le_r)
      · exact absurd (hgt r₀ hr₀_mem r hr₁_mem) (not_lt_of_ge hr_le_r₀)
    simp [member, hrep, hxg]

/-- **Successor query in a grouped y-fast trie.** For a grouped y-fast trie $t$ and a key
$x$, let $r$ be the least key greater than $x$ stored in the representative x-fast trie of
$t$; if there is none, the query returns nothing. Otherwise let $g$ be the first group of $t$
whose last element is $r$, or the empty list if no group has last element $r$. The query then
returns the first key of $g$ greater than $x$, or nothing if $g$ has no such key. -/
public def successor {w B : Nat} (t : GroupedYFastTrie w B) (x : Fin (2 ^ w)) :
    Option (Fin (2 ^ w)) :=
  match t.reps.successor x with
  | none => none
  | some r => (t.findGroup r).find? (fun z => decide (x < z))

/-- **Successor query returns the least larger stored key.** Let $t$ be a valid grouped y-fast
trie and let $x$, $y$ be keys. The successor query for $x$ in $t$ returns $y$ if and only if
$y$ is stored in $t$, $x < y$, and $y \le z$ for every key $z$ stored in $t$ with $x < z$. -/
public theorem successor_eq_some_iff {w B : Nat} {t : GroupedYFastTrie w B}
    (hv : t.Valid) (x y : Fin (2 ^ w)) :
    t.successor x = some y ↔
      y ∈ t.contents ∧ x < y ∧ ∀ z ∈ t.contents, x < z → y ≤ z := by
  constructor
  · intro h
    cases hrep : t.reps.successor x with
    | none => simp [successor, hrep] at h
    | some r =>
        have hfind : (t.findGroup r).find? (fun z => decide (x < z)) = some y := by
          simpa [successor, hrep] using h
        obtain ⟨hr_reps, -, hr_least⟩ :=
          (XFastTrie.successor_eq_some_iff t.reps x r).mp hrep
        obtain ⟨hg_mem, hg_last⟩ := findGroup_spec hv hr_reps
        obtain ⟨r₁, hr₁_last, hr₁_mem, -, -⟩ := hv.group_last_spec hg_mem
        have hr₁ : r = r₁ := (Option.some.inj (hr₁_last.symm.trans hg_last)).symm
        subst hr₁
        obtain ⟨-, -, hsorted⟩ := hv.2.2.1 (t.findGroup r) hg_mem
        obtain ⟨hy_mem, hxy, hy_least⟩ :=
          find?_succ_some (hsorted.imp (fun hh => hh.le)) hfind
        refine ⟨(mem_contents_iff t y).mpr ⟨t.findGroup r, hg_mem, hy_mem⟩, hxy, ?_⟩
        intro z hz hxz
        obtain ⟨g', hg'_mem, hzg'⟩ := (mem_contents_iff t z).mp hz
        obtain ⟨r', -, hr'_mem, hr'_le, hr'_reps⟩ := hv.group_last_spec hg'_mem
        have hr_le_r' : r ≤ r' := hr_least r' hr'_reps (hxz.trans_le (hr'_le z hzg'))
        rcases groupOrdered_trichotomy hv.2.2.2 hg_mem hg'_mem with heq | hlt | hgt
        · exact hy_least z (heq.symm ▸ hzg') hxz
        · exact (hlt y hy_mem z hzg').le
        · exact absurd (hgt r' hr'_mem r hr₁_mem) (not_lt_of_ge hr_le_r')
  · rintro ⟨hy_contents, hxy, hy_least⟩
    obtain ⟨g₀, hg₀_mem, hyg₀⟩ := (mem_contents_iff t y).mp hy_contents
    obtain ⟨r₀, -, hr₀_mem, hr₀_le, hr₀_reps⟩ := hv.group_last_spec hg₀_mem
    have hx_lt_r₀ : x < r₀ := hxy.trans_le (hr₀_le y hyg₀)
    obtain ⟨r, hrep⟩ : ∃ r, t.reps.successor x = some r := by
      cases hrep : t.reps.successor x with
      | some r => exact ⟨r, rfl⟩
      | none =>
          exact absurd hx_lt_r₀
            ((XFastTrie.successor_eq_none_iff t.reps x).mp hrep r₀ hr₀_reps)
    obtain ⟨hr_reps, hxr, hr_least⟩ :=
      (XFastTrie.successor_eq_some_iff t.reps x r).mp hrep
    have hr_le_r₀ : r ≤ r₀ := hr_least r₀ hr₀_reps hx_lt_r₀
    obtain ⟨hg_mem, hg_last⟩ := findGroup_spec hv hr_reps
    obtain ⟨r₁, hr₁_last, hr₁_mem, -, -⟩ := hv.group_last_spec hg_mem
    have hr₁ : r = r₁ := (Option.some.inj (hr₁_last.symm.trans hg_last)).symm
    subst hr₁
    obtain ⟨-, -, hsorted⟩ := hv.2.2.1 (t.findGroup r) hg_mem
    have hsorted_le := hsorted.imp (fun hh => hh.le)
    obtain ⟨y', hfind⟩ :
        ∃ y', (t.findGroup r).find? (fun z => decide (x < z)) = some y' := by
      cases hfind : (t.findGroup r).find? (fun z => decide (x < z)) with
      | some y' => exact ⟨y', rfl⟩
      | none => exact absurd hxr (find?_succ_none hfind r hr₁_mem)
    obtain ⟨hy'_mem, hxy', hy'_least⟩ := find?_succ_some hsorted_le hfind
    have hy_le_y' : y ≤ y' :=
      hy_least y' ((mem_contents_iff t y').mpr ⟨t.findGroup r, hg_mem, hy'_mem⟩) hxy'
    have hy'_le_y : y' ≤ y := by
      rcases groupOrdered_trichotomy hv.2.2.2 hg_mem hg₀_mem with heq | hlt | hgt
      · exact hy'_least y (heq.symm ▸ hyg₀) hxy
      · exact (hlt y' hy'_mem y hyg₀).le
      · exact absurd (hgt r₀ hr₀_mem r hr₁_mem) (not_lt_of_ge hr_le_r₀)
    have hyy : y' = y := le_antisymm hy'_le_y hy_le_y'
    simp [successor, hrep, hfind, hyy]

/-- **Successor query fails exactly when no larger key is stored.** Let $t$ be a valid grouped
y-fast trie and $x$ a key. The successor query for $x$ in $t$ returns nothing if and only if no
key stored in $t$ is greater than $x$. -/
public theorem successor_eq_none_iff {w B : Nat} {t : GroupedYFastTrie w B}
    (hv : t.Valid) (x : Fin (2 ^ w)) :
    t.successor x = none ↔ ∀ z ∈ t.contents, ¬ x < z := by
  constructor
  · intro h z hz hxz
    obtain ⟨g', hg'_mem, hzg'⟩ := (mem_contents_iff t z).mp hz
    obtain ⟨r', -, -, hr'_le, hr'_reps⟩ := hv.group_last_spec hg'_mem
    have hx_lt_r' : x < r' := hxz.trans_le (hr'_le z hzg')
    cases hrep : t.reps.successor x with
    | none =>
        exact ((XFastTrie.successor_eq_none_iff t.reps x).mp hrep r' hr'_reps)
          hx_lt_r'
    | some r =>
        have hfind : (t.findGroup r).find? (fun z => decide (x < z)) = none := by
          simpa [successor, hrep] using h
        obtain ⟨hr_reps, hxr, -⟩ :=
          (XFastTrie.successor_eq_some_iff t.reps x r).mp hrep
        obtain ⟨hg_mem, hg_last⟩ := findGroup_spec hv hr_reps
        obtain ⟨r₁, hr₁_last, hr₁_mem, -, -⟩ := hv.group_last_spec hg_mem
        have hr₁ : r = r₁ := (Option.some.inj (hr₁_last.symm.trans hg_last)).symm
        subst hr₁
        exact find?_succ_none hfind r hr₁_mem hxr
  · intro h
    cases hrep : t.reps.successor x with
    | none => simp [successor, hrep]
    | some r =>
        obtain ⟨hr_reps, hxr, -⟩ :=
          (XFastTrie.successor_eq_some_iff t.reps x r).mp hrep
        obtain ⟨hg_mem, hg_last⟩ := findGroup_spec hv hr_reps
        obtain ⟨r₁, hr₁_last, hr₁_mem, -, -⟩ := hv.group_last_spec hg_mem
        have hr₁ : r = r₁ := (Option.some.inj (hr₁_last.symm.trans hg_last)).symm
        subst hr₁
        exact absurd hxr
          (h r ((mem_contents_iff t r).mpr ⟨t.findGroup r, hg_mem, hr₁_mem⟩))

/-- **The empty grouped y-fast trie.** For every key length $w$ and group bound $B$, the empty
grouped y-fast trie has the empty x-fast trie as its trie of representatives and has no
groups. -/
public def empty {w B : Nat} : GroupedYFastTrie w B :=
  ⟨XFastTrie.empty, []⟩

/-- **The empty grouped y-fast trie is valid.** For every key width $w$ and group bound $B$,
the empty grouped y-fast trie satisfies the grouped y-fast trie invariant. -/
public theorem valid_empty {w B : Nat} : (empty : GroupedYFastTrie w B).Valid := by
  refine ⟨XFastTrie.valid_empty, ?_, ?_, List.Pairwise.nil⟩
  · intro r
    simp [empty, XFastTrie.empty]
  · intro g hg
    simp [empty] at hg

@[simp] public theorem contents_empty {w B : Nat} :
    (empty : GroupedYFastTrie w B).contents = ∅ := by
  simp [contents, empty]

/-- **The empty grouped y-fast trie has no members.** For all natural numbers $w$ and $B$ and
every $w$-bit key $x$, the membership query on the empty grouped y-fast trie over $w$-bit keys
with group bound $B$ returns false at $x$. -/
public theorem member_empty {w B : Nat} (x : Fin (2 ^ w)) :
    (empty : GroupedYFastTrie w B).member x = false := by
  cases h : (empty : GroupedYFastTrie w B).member x with
  | false => rfl
  | true =>
      have hx := (member_iff valid_empty x).mp h
      simp at hx

/-- **The empty grouped y-fast trie has no successors.** For every key $x$, the successor query
for $x$ in the empty grouped y-fast trie returns nothing. -/
public theorem successor_empty {w B : Nat} (x : Fin (2 ^ w)) :
    (empty : GroupedYFastTrie w B).successor x = none :=
  (successor_eq_none_iff valid_empty x).mpr (by simp)

/-- **Representative trie of a list.** For a list $rs$ of $w$-bit keys, the representative
x-fast trie of $rs$ is obtained from the empty x-fast trie over $w$-bit keys by inserting the
elements of $rs$ one at a time, from first to last. -/
public def mkReps {w : Nat} (rs : List (Fin (2 ^ w))) : XFastTrie w :=
  rs.foldl (fun t r => t.insert r) XFastTrie.empty

private theorem valid_foldl_insert {w : Nat} (rs : List (Fin (2 ^ w)))
    (t : XFastTrie w) (hv : t.Valid) :
    (rs.foldl (fun t r => t.insert r) t).Valid := by
  induction rs generalizing t with
  | nil => exact hv
  | cons r rs ih => exact ih _ (XFastTrie.valid_insert t hv r)

/-- **Inserting a list of keys into the empty x-fast trie gives a valid trie.** For every list
of $w$-bit keys, the x-fast trie obtained from the empty x-fast trie by inserting the keys of
the list one at a time satisfies the x-fast trie invariant: each level holds exactly the
prefixes of that length of the stored keys. -/
public theorem valid_mkReps {w : Nat} (rs : List (Fin (2 ^ w))) : (mkReps rs).Valid :=
  valid_foldl_insert rs _ XFastTrie.valid_empty

private theorem contents_foldl_insert {w : Nat} (rs : List (Fin (2 ^ w)))
    (t : XFastTrie w) :
    (rs.foldl (fun t r => t.insert r) t).contents = t.contents ∪ rs.toFinset := by
  induction rs generalizing t with
  | nil => simp
  | cons r rs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      ext z
      simp only [XFastTrie.contents_insert, Finset.mem_union, Finset.mem_insert,
        List.mem_toFinset, List.mem_cons]
      tauto

/-- **Keys of the trie of representatives.** For every list $L$ of $w$-bit keys, the x-fast
trie obtained by inserting the elements of $L$ one by one into the empty x-fast trie stores
exactly the elements of $L$: its key set is the set of elements of $L$. -/
public theorem contents_mkReps {w : Nat} (rs : List (Fin (2 ^ w))) :
    (mkReps rs).contents = rs.toFinset := by
  rw [mkReps, contents_foldl_insert]
  simp [XFastTrie.empty]

/-- **Grouped y-fast trie from a list of groups.** For a list of groups $g_1, \dots, g_k$,
each a list of $w$-bit keys, and any group-size bound $B$, this is the grouped y-fast trie
whose groups are $g_1, \dots, g_k$ in this order and whose representative x-fast trie is
obtained from the empty x-fast trie by inserting the last element of each nonempty group,
in order. No condition on the groups is checked here; when a group is sorted, its last
element is its maximum. -/
public def ofGroups {w B : Nat} (gs : List (List (Fin (2 ^ w)))) :
    GroupedYFastTrie w B :=
  ⟨mkReps (gs.filterMap List.getLast?), gs⟩

/-- **Assembling a valid grouped y-fast trie from groups.** Let $w$ and $B$ be natural numbers
and let $g_1, \dots, g_k$ be a list of groups, each a list of keys in $\{0, \dots, 2^w - 1\}$.
Suppose every group is nonempty, has at most $B$ keys, and is strictly increasing, and the
groups are ordered: every key of an earlier group is smaller than every key of a later group.
Then the grouped y-fast trie with group bound $B$ assembled from these groups, whose
representatives are the last elements of the groups, is valid. -/
public theorem valid_ofGroups {w B : Nat} {gs : List (List (Fin (2 ^ w)))}
    (hgroups : ∀ g ∈ gs, g ≠ [] ∧ g.length ≤ B ∧ g.Pairwise (· < ·))
    (hord : GroupOrdered gs) : (ofGroups gs : GroupedYFastTrie w B).Valid := by
  refine ⟨valid_mkReps _, ?_, hgroups, hord⟩
  change ∀ r, r ∈ (mkReps (gs.filterMap List.getLast?)).contents ↔
    ∃ g ∈ gs, g.getLast? = some r
  intro r
  rw [contents_mkReps]
  simp [List.mem_filterMap]

@[simp] public theorem contents_ofGroups {w B : Nat} (gs : List (List (Fin (2 ^ w)))) :
    (ofGroups gs : GroupedYFastTrie w B).contents = gs.flatten.toFinset := rfl

/-- **Fuel-bounded chunking.** Given a bound $B$, a fuel $n$ and a list $l$ of $w$-bit keys, the
fuel-bounded chunking is the empty list of chunks when $n = 0$ or $l$ is empty; otherwise it is
the chunk formed by the first $\min(B, |l|)$ elements of $l$, followed by the fuel-bounded
chunking with bound $B$ and fuel $n - 1$ of the remaining elements of $l$. -/
def chunkGroupsAux {w : Nat} (B : Nat) :
    Nat → List (Fin (2 ^ w)) → List (List (Fin (2 ^ w)))
  | 0, _ => []
  | _, [] => []
  | fuel + 1, l => l.take B :: chunkGroupsAux B fuel (l.drop B)

private theorem chunkGroupsAux_zero {w : Nat} (B : Nat) (l : List (Fin (2 ^ w))) :
    chunkGroupsAux B 0 l = [] := rfl

private theorem chunkGroupsAux_nil {w : Nat} (B fuel : Nat) :
    chunkGroupsAux B fuel ([] : List (Fin (2 ^ w))) = [] := by
  cases fuel <;> rfl

private theorem chunkGroupsAux_succ_cons {w : Nat} (B fuel : Nat) (a : Fin (2 ^ w))
    (l : List (Fin (2 ^ w))) :
    chunkGroupsAux B (fuel + 1) (a :: l) =
      (a :: l).take B :: chunkGroupsAux B fuel ((a :: l).drop B) := rfl

private theorem flatten_chunkGroupsAux {w : Nat} {B : Nat} (hB : 0 < B) :
    ∀ (fuel : Nat) (l : List (Fin (2 ^ w))), l.length ≤ fuel →
      (chunkGroupsAux B fuel l).flatten = l := by
  intro fuel
  induction fuel with
  | zero =>
      intro l hl
      cases l with
      | nil => rfl
      | cons a l => simp at hl
  | succ fuel ih =>
      intro l hl
      cases l with
      | nil => rfl
      | cons a l =>
          rw [chunkGroupsAux_succ_cons, List.flatten_cons,
            ih ((a :: l).drop B) (by
              rw [List.length_drop]
              simp only [List.length_cons] at hl ⊢
              omega), List.take_append_drop]

private theorem chunkGroupsAux_spec {w : Nat} {B : Nat} (hB : 0 < B) :
    ∀ (fuel : Nat) (l : List (Fin (2 ^ w))), l.length ≤ fuel →
      ∀ g ∈ chunkGroupsAux B fuel l, g ≠ [] ∧ g.length ≤ B ∧ g.Sublist l := by
  intro fuel
  induction fuel with
  | zero =>
      intro l _ g hg
      rw [chunkGroupsAux_zero] at hg
      simp at hg
  | succ fuel ih =>
      intro l hl g hg
      cases l with
      | nil =>
          rw [chunkGroupsAux_nil] at hg
          simp at hg
      | cons a l =>
          rw [chunkGroupsAux_succ_cons, List.mem_cons] at hg
          have hdrop_len : ((a :: l).drop B).length ≤ fuel := by
            rw [List.length_drop]
            simp only [List.length_cons] at hl ⊢
            omega
          rcases hg with rfl | hg
          · refine ⟨?_, ?_, List.take_sublist B (a :: l)⟩
            · cases B with
              | zero => simp at hB
              | succ B =>
                  change (a :: l.take B) ≠ []
                  simp
            · have hlen := List.length_take (i := B) (l := a :: l)
              omega
          · obtain ⟨hne, hlen, hsub⟩ := ih ((a :: l).drop B) hdrop_len g hg
            exact ⟨hne, hlen, hsub.trans (List.drop_sublist B (a :: l))⟩

/-- **Chunking a list into groups.** Given a bound $B$ and a list $l$ of $w$-bit keys, when
$B > 0$ the chunking of $l$ cuts $l$ from the left into consecutive chunks of exactly $B$
elements each, except that the last chunk holds the remaining one to $B$ elements; there are no
chunks when $l$ is empty. When $B = 0$, the chunking has no chunks if $l$ is empty and is the
single chunk $l$ otherwise.

So every chunk has at most $B$ elements when $B > 0$, but not when $B = 0$ and $l$ is
nonempty. -/
public def chunkGroups {w : Nat} (B : Nat) (l : List (Fin (2 ^ w))) :
    List (List (Fin (2 ^ w))) :=
  if B = 0 then (if l = [] then [] else [l]) else chunkGroupsAux B l.length l

/-- **Chunking with bound zero.** For every nonempty list $l$ of $w$-bit keys, the chunking of
$l$ with bound $B = 0$ consists of the single chunk $l$. -/
public theorem chunkGroups_zero_of_ne {w : Nat} {l : List (Fin (2 ^ w))}
    (hl : l ≠ []) : chunkGroups 0 l = [l] := by
  unfold chunkGroups
  rw [ite_eq_left rfl, ite_eq_right hl]

/-- **Chunking preserves the list.** For every bound $B$ (including $B = 0$) and every list $l$
of $w$-bit keys, concatenating the chunks of the chunking of $l$ with bound $B$, in order,
gives back $l$. -/
public theorem flatten_chunkGroups {w : Nat} (B : Nat) (l : List (Fin (2 ^ w))) :
    (chunkGroups B l).flatten = l := by
  unfold chunkGroups
  split
  · split
    · rename_i hl
      simp [hl]
    · simp
  · rename_i hB
    exact flatten_chunkGroupsAux (Nat.pos_of_ne_zero hB) l.length l le_rfl

/-- **Chunks of a sorted list.** Let $B > 0$ and let $l$ be a strictly increasing list of
$w$-bit keys. Then every chunk of the chunking of $l$ into groups of at most $B$ keys is
nonempty, has at most $B$ elements, and is strictly increasing. -/
public theorem chunkGroups_spec {w : Nat} {B : Nat} (hB : 0 < B)
    (l : List (Fin (2 ^ w))) (hsorted : l.Pairwise (· < ·)) :
    ∀ g ∈ chunkGroups B l, g ≠ [] ∧ g.length ≤ B ∧ g.Pairwise (· < ·) := by
  intro g hg
  have hchunk : chunkGroups B l = chunkGroupsAux B l.length l := by
    unfold chunkGroups
    rw [ite_eq_right (by omega)]
  rw [hchunk] at hg
  obtain ⟨hne, hlen, hsub⟩ := chunkGroupsAux_spec hB l.length l le_rfl g hg
  exact ⟨hne, hlen, hsorted.sublist hsub⟩

/-- Flattened strict sortedness gives the cross-group order. -/
private theorem groupOrdered_of_flatten_pairwise {w : Nat}
    {gs : List (List (Fin (2 ^ w)))} (h : gs.flatten.Pairwise (· < ·)) :
    GroupOrdered gs := by
  induction gs with
  | nil => exact List.Pairwise.nil
  | cons g gs ih =>
      rw [List.flatten_cons] at h
      obtain ⟨-, hgs_pair, hcross⟩ := List.pairwise_append.mp h
      exact List.pairwise_cons.mpr ⟨fun g' hg' a ha b hb =>
        hcross a ha b (List.mem_flatten.mpr ⟨g', hg', hb⟩), ih hgs_pair⟩

/-- **Chunks of a sorted list are ordered.** Let $B$ be a natural number and let $l$ be a
strictly increasing list of $w$-bit keys. Then the chunk groups of $l$ with bound $B$ are group
ordered: every key of an earlier chunk is smaller than every key of a later chunk. -/
public theorem groupOrdered_chunkGroups {w : Nat} (B : Nat) (l : List (Fin (2 ^ w)))
    (hsorted : l.Pairwise (· < ·)) : GroupOrdered (chunkGroups B l) :=
  groupOrdered_of_flatten_pairwise ((flatten_chunkGroups B l).symm ▸ hsorted)

/-- **Grouped y-fast trie from a sorted list.** For a group bound $B$ and a list $l$ of
$w$-bit keys, this is the grouped y-fast trie whose groups, in order, are consecutive pieces of
$l$ that together make up $l$, and whose representative x-fast trie is obtained from the empty
x-fast trie by inserting the last element of each group, in order. If $B > 0$, the groups are
obtained by repeatedly cutting off the first $B$ keys, so every group has exactly $B$ keys
except possibly the last, which has between one and $B$ keys. If $B = 0$, the only group is $l$
itself. In both cases there are no groups when $l$ is empty.

The construction is intended for strictly increasing $l$. It yields a valid trie when $B > 0$
and $l$ is strictly increasing, and an invalid one when $B = 0$ and $l$ is nonempty. -/
public def ofSortedList {w : Nat} (B : Nat) (l : List (Fin (2 ^ w))) :
    GroupedYFastTrie w B :=
  ofGroups (chunkGroups B l)

/-- **Building from a sorted list gives a valid grouped y-fast trie.** Let $w$ and $B$ be
natural numbers with $0 < B$, and let $l$ be a strictly increasing list of keys in
$\{0, \dots, 2^w - 1\}$. Then the grouped y-fast trie with group bound $B$ built from $l$ by
cutting it into consecutive groups of at most $B$ keys is valid. -/
public theorem valid_ofSortedList {w B : Nat} (hB : 0 < B) {l : List (Fin (2 ^ w))}
    (hsorted : l.Pairwise (· < ·)) : (ofSortedList B l).Valid :=
  valid_ofGroups (chunkGroups_spec hB l hsorted) (groupOrdered_chunkGroups B l hsorted)

/-- **Building from a nonempty list with group bound zero gives an invalid trie.** For every
natural number $w$ and every nonempty list $l$ of $w$-bit keys, the grouped y-fast trie with
group bound $B = 0$ built from $l$ is not valid.

With $B = 0$ the only group is $l$ itself, which has more than $0$ keys. For $B > 0$ and strictly
increasing $l$, the grouped y-fast trie built from $l$ is valid. -/
public theorem not_valid_ofSortedList_zero {w : Nat} {l : List (Fin (2 ^ w))}
    (hl : l ≠ []) : ¬ (ofSortedList 0 l).Valid := by
  intro hv
  have hgroups : (ofSortedList 0 l).groups = [l] := chunkGroups_zero_of_ne hl
  have hmem : l ∈ (ofSortedList 0 l).groups := by
    rw [hgroups]
    simp
  obtain ⟨-, hlen, -⟩ := hv.2.2.1 l hmem
  have hpos : 0 < l.length := List.length_pos_of_ne_nil hl
  omega

/-- **Keys of the grouped y-fast trie built from a list.** For every group bound $B$ (including
$B = 0$) and every list $l$ of $w$-bit keys, sorted or not, the key set of the grouped y-fast
trie built from $l$ with group bound $B$ is exactly the set of elements of $l$. -/
public theorem contents_ofSortedList {w B : Nat} (l : List (Fin (2 ^ w))) :
    (ofSortedList B l).contents = l.toFinset := by
  rw [ofSortedList, contents_ofGroups, flatten_chunkGroups]

/-- **Membership in a trie built from a sorted list.** Let $B > 0$ and let $l$ be a strictly
increasing list of $w$-bit keys. Then for every key $x$, the membership query on the grouped
y-fast trie built from $l$ with group bound $B$ returns true at $x$ if and only if $x$ belongs
to $l$. -/
public theorem member_ofSortedList_iff {w B : Nat} (hB : 0 < B)
    {l : List (Fin (2 ^ w))} (hsorted : l.Pairwise (· < ·)) (x : Fin (2 ^ w)) :
    (ofSortedList B l).member x = true ↔ x ∈ l := by
  have h1 := member_iff (valid_ofSortedList hB hsorted) x
  rw [contents_ofSortedList] at h1
  simpa only [List.mem_toFinset] using h1

/-- **Successor in the trie built from a sorted list.** Let $B > 0$, let $l$ be a strictly
increasing list of $w$-bit keys, and let $x$, $y$ be keys. The successor query for $x$ in the
grouped y-fast trie built from $l$ with group bound $B$ returns $y$ if and only if $y$ belongs
to $l$, $x < y$, and $y \le z$ for every $z$ in $l$ with $x < z$. -/
public theorem successor_ofSortedList_eq_some_iff {w B : Nat} (hB : 0 < B)
    {l : List (Fin (2 ^ w))} (hsorted : l.Pairwise (· < ·)) (x y : Fin (2 ^ w)) :
    (ofSortedList B l).successor x = some y ↔
      y ∈ l ∧ x < y ∧ ∀ z ∈ l, x < z → y ≤ z := by
  have h1 := successor_eq_some_iff (valid_ofSortedList hB hsorted) x y
  rw [contents_ofSortedList] at h1
  simpa only [List.mem_toFinset] using h1

end GroupedYFastTrie

end Cslib.Algorithms.Lean
