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

/--
A grouped y-fast trie over `w`-bit keys: an x-fast trie of representatives plus the
list of groups in increasing order, with group size bounded by `B`. Each group is a
sorted list standing in for a balanced search tree; no complexity bound is claimed.
-/
public structure GroupedYFastTrie (w B : Nat) where
  /-- The x-fast trie over representative keys (group maxima). -/
  reps : XFastTrie w
  /-- The groups, in increasing order. -/
  groups : List (List (Fin (2 ^ w)))

namespace GroupedYFastTrie

/-- All stored keys: the flattened groups. -/
public def contents {w B : Nat} (t : GroupedYFastTrie w B) : Finset (Fin (2 ^ w)) :=
  t.groups.flatten.toFinset

/-- A key is stored exactly when it lies in some group. -/
public theorem mem_contents_iff {w B : Nat} (t : GroupedYFastTrie w B)
    (x : Fin (2 ^ w)) : x ∈ t.contents ↔ ∃ g ∈ t.groups, x ∈ g := by
  simp [contents, List.mem_flatten]

/-- Cross-group order: every key of an earlier group is smaller than every key of a
later group. -/
public def GroupOrdered {w : Nat} (gs : List (List (Fin (2 ^ w)))) : Prop :=
  gs.Pairwise (fun g₁ g₂ => ∀ a ∈ g₁, ∀ b ∈ g₂, a < b)

/--
The group invariant: the representative trie is a valid x-fast trie whose keys are
exactly the group maxima; every group is nonempty, has at most `B` keys, and is
strictly sorted; and the groups are ordered.
-/
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

/-- The group owned by representative `r` (the first group whose maximum is `r`), or
the empty list when there is none. -/
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

/-- The least representative at least `x`: `x` itself when the deepest-level probe
finds it among the representatives, otherwise the representative successor. -/
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

/-- Membership: locate the least representative at least `x`, then scan its group. -/
public def member {w B : Nat} (t : GroupedYFastTrie w B) (x : Fin (2 ^ w)) : Bool :=
  match t.repGe x with
  | none => false
  | some r => decide (x ∈ t.findGroup r)

/-- Under `Valid`, representative lookup plus group scan decides membership in
`contents` exactly. -/
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

/-- Successor: locate the least representative above `x` in the x-fast trie, then
scan its group for the first key above `x`. -/
public def successor {w B : Nat} (t : GroupedYFastTrie w B) (x : Fin (2 ^ w)) :
    Option (Fin (2 ^ w)) :=
  match t.reps.successor x with
  | none => none
  | some r => (t.findGroup r).find? (fun z => decide (x < z))

/-- The successor is `some y` exactly when `y` is the least stored key above `x`. -/
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

/-- The successor is `none` exactly when no stored key is greater than `x`. -/
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

/-- The empty grouped y-fast trie: empty representative trie, no groups. -/
public def empty {w B : Nat} : GroupedYFastTrie w B :=
  ⟨XFastTrie.empty, []⟩

/-- The empty trie is valid. -/
public theorem valid_empty {w B : Nat} : (empty : GroupedYFastTrie w B).Valid := by
  refine ⟨XFastTrie.valid_empty, ?_, ?_, List.Pairwise.nil⟩
  · intro r
    simp [empty, XFastTrie.empty]
  · intro g hg
    simp [empty] at hg

@[simp] public theorem contents_empty {w B : Nat} :
    (empty : GroupedYFastTrie w B).contents = ∅ := by
  simp [contents, empty]

/-- Nothing is a member of the empty trie. -/
public theorem member_empty {w B : Nat} (x : Fin (2 ^ w)) :
    (empty : GroupedYFastTrie w B).member x = false := by
  cases h : (empty : GroupedYFastTrie w B).member x with
  | false => rfl
  | true =>
      have hx := (member_iff valid_empty x).mp h
      simp at hx

/-- Nothing succeeds in the empty trie. -/
public theorem successor_empty {w B : Nat} (x : Fin (2 ^ w)) :
    (empty : GroupedYFastTrie w B).successor x = none :=
  (successor_eq_none_iff valid_empty x).mpr (by simp)

/-- Build the representative x-fast trie by inserting a list of representatives. -/
public def mkReps {w : Nat} (rs : List (Fin (2 ^ w))) : XFastTrie w :=
  rs.foldl (fun t r => t.insert r) XFastTrie.empty

private theorem valid_foldl_insert {w : Nat} (rs : List (Fin (2 ^ w)))
    (t : XFastTrie w) (hv : t.Valid) :
    (rs.foldl (fun t r => t.insert r) t).Valid := by
  induction rs generalizing t with
  | nil => exact hv
  | cons r rs ih => exact ih _ (XFastTrie.valid_insert t hv r)

/-- The folded representative trie is a valid x-fast trie. -/
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

/-- The representative trie built from a list stores exactly that list's keys. -/
public theorem contents_mkReps {w : Nat} (rs : List (Fin (2 ^ w))) :
    (mkReps rs).contents = rs.toFinset := by
  rw [mkReps, contents_foldl_insert]
  simp [XFastTrie.empty]

/-- Assemble a grouped trie from a group list, taking the group maxima as
representatives. -/
public def ofGroups {w B : Nat} (gs : List (List (Fin (2 ^ w)))) :
    GroupedYFastTrie w B :=
  ⟨mkReps (gs.filterMap List.getLast?), gs⟩

/-- Groups satisfying the size, sortedness, and order conditions assemble into a
valid trie. -/
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

/-- Fuel-bounded chunking: cut off a chunk of length at most `B` and continue. -/
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

/-- Split a list into consecutive chunks (groups) of length at most `B`.
The length bound holds only for `0 < B` (see `chunkGroups_spec`): at
`B = 0` this degenerates to a single chunk `[l]` for nonempty `l`
(`chunkGroups_zero_of_ne`), whose length exceeds `0`. Callers needing the
bound must supply `0 < B`. -/
public def chunkGroups {w : Nat} (B : Nat) (l : List (Fin (2 ^ w))) :
    List (List (Fin (2 ^ w))) :=
  if B = 0 then (if l = [] then [] else [l]) else chunkGroupsAux B l.length l

/-- The degenerate `B = 0` chunking of a nonempty list is one chunk. -/
public theorem chunkGroups_zero_of_ne {w : Nat} {l : List (Fin (2 ^ w))}
    (hl : l ≠ []) : chunkGroups 0 l = [l] := by
  unfold chunkGroups
  rw [ite_eq_left rfl, ite_eq_right hl]

/-- Chunking partitions the list: flattening recovers it. -/
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

/-- Chunks of a strictly sorted list are nonempty, bounded, and strictly sorted. -/
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

/-- Chunks appear in increasing order when the original list is strictly sorted. -/
public theorem groupOrdered_chunkGroups {w : Nat} (B : Nat) (l : List (Fin (2 ^ w)))
    (hsorted : l.Pairwise (· < ·)) : GroupOrdered (chunkGroups B l) :=
  groupOrdered_of_flatten_pairwise ((flatten_chunkGroups B l).symm ▸ hsorted)

/-- Build a grouped y-fast trie from a sorted list by cutting it into groups
of at most `B` keys. The bound and validity require `0 < B`
(`valid_ofSortedList`); at `B = 0` the groups degenerate to `[l]` and the
result is invalid for nonempty `l` (`not_valid_ofSortedList_zero`). -/
public def ofSortedList {w : Nat} (B : Nat) (l : List (Fin (2 ^ w))) :
    GroupedYFastTrie w B :=
  ofGroups (chunkGroups B l)

/-- Building from a strictly sorted list with a positive bound gives a valid trie. -/
public theorem valid_ofSortedList {w B : Nat} (hB : 0 < B) {l : List (Fin (2 ^ w))}
    (hsorted : l.Pairwise (· < ·)) : (ofSortedList B l).Valid :=
  valid_ofGroups (chunkGroups_spec hB l hsorted) (groupOrdered_chunkGroups B l hsorted)

/-- At `B = 0`, building from a nonempty list cannot be valid: the single
degenerate group `l` has positive length, violating the `≤ 0` group bound
in `Valid`. Use `0 < B` (see `valid_ofSortedList`). -/
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

/-- The trie built from a list stores exactly that list. -/
public theorem contents_ofSortedList {w B : Nat} (l : List (Fin (2 ^ w))) :
    (ofSortedList B l).contents = l.toFinset := by
  rw [ofSortedList, contents_ofGroups, flatten_chunkGroups]

/-- Membership in the trie built from a list is membership in the list. -/
public theorem member_ofSortedList_iff {w B : Nat} (hB : 0 < B)
    {l : List (Fin (2 ^ w))} (hsorted : l.Pairwise (· < ·)) (x : Fin (2 ^ w)) :
    (ofSortedList B l).member x = true ↔ x ∈ l := by
  have h1 := member_iff (valid_ofSortedList hB hsorted) x
  rw [contents_ofSortedList] at h1
  simpa only [List.mem_toFinset] using h1

/-- The successor in the trie built from a list is the least element of the list
above the query. -/
public theorem successor_ofSortedList_eq_some_iff {w B : Nat} (hB : 0 < B)
    {l : List (Fin (2 ^ w))} (hsorted : l.Pairwise (· < ·)) (x y : Fin (2 ^ w)) :
    (ofSortedList B l).successor x = some y ↔
      y ∈ l ∧ x < y ∧ ∀ z ∈ l, x < z → y ≤ z := by
  have h1 := successor_eq_some_iff (valid_ofSortedList hB hsorted) x y
  rw [contents_ofSortedList] at h1
  simpa only [List.mem_toFinset] using h1

end GroupedYFastTrie

end Cslib.Algorithms.Lean
