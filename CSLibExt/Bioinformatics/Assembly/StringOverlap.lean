/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# String overlap and merge

Overlap formulation of the shortest common superstring problem: the overlap of
two strings is the longest suffix of the first that is also a prefix of the
second, and merging splices the second string onto the first along that
overlap. Folding `merge` over a fixed ordering yields a common superstring of
the inputs (soundness along that ordering; no optimality claim).

Reference: Dan Gusfield, Algorithms on Strings, Trees and Sequences: Computer
Science and Computational Biology, Cambridge University Press, 1997, Ch. 1.
-/

namespace Cslib.Bioinformatics.Assembly.StringOverlap

/-- `OverlapMatch a b k`: `k` is a valid overlap length for `a`, `b`. -/
def OverlapMatch {α : Type*} [DecidableEq α] (a b : List α) (k : Nat) : Prop :=
  k ≤ a.length ∧ k ≤ b.length ∧ a.drop (a.length - k) = b.take k

/-- Search candidate overlap lengths `0 .. n`, largest first. -/
def overlapAux {α : Type*} [DecidableEq α] (a b : List α) : Nat → Nat
  | 0 => 0
  | (n + 1) =>
    if (n + 1) ≤ min a.length b.length ∧
        a.drop (a.length - (n + 1)) = b.take (n + 1) then (n + 1)
    else overlapAux a b n

/-- Largest overlap length between `a` and `b`. -/
def overlap {α : Type*} [DecidableEq α] (a b : List α) : Nat :=
  overlapAux a b (min a.length b.length)

theorem overlapAux_le {α : Type*} [DecidableEq α] (a b : List α) (n : Nat) :
    overlapAux a b n ≤ n := by
  induction n with
  | zero => simp [overlapAux]
  | succ n ih =>
    unfold overlapAux
    split_ifs with h <;> omega

theorem overlapAux_le_min {α : Type*} [DecidableEq α] (a b : List α) (n : Nat) :
    overlapAux a b n ≤ min a.length b.length := by
  induction n with
  | zero => simp [overlapAux]
  | succ n ih =>
    unfold overlapAux
    split_ifs with h
    · exact h.1
    · exact ih

theorem overlapAux_match {α : Type*} [DecidableEq α] (a b : List α) (n : Nat) :
    n ≤ min a.length b.length → OverlapMatch a b (overlapAux a b n) := by
  induction n with
  | zero =>
    intro hn
    simp only [overlapAux]
    refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
    simp
  | succ n ih =>
    intro hn
    have hn' : n ≤ min a.length b.length := by omega
    unfold overlapAux
    split_ifs with h
    · exact ⟨Nat.le_trans hn (Nat.min_le_left _ _),
        Nat.le_trans hn (Nat.min_le_right _ _), h.2⟩
    · exact ih hn'

theorem overlapAux_ge {α : Type*} [DecidableEq α] (a b : List α) (n : Nat) :
    ∀ (k : Nat), OverlapMatch a b k → k ≤ n → n ≤ min a.length b.length →
      k ≤ overlapAux a b n := by
  induction n with
  | zero =>
    intro k hk hkn hn
    have hk0 : k = 0 := by omega
    subst hk0
    simp [overlapAux]
  | succ n ih =>
    intro k hk hkn hn
    unfold overlapAux
    split_ifs with h
    · omega
    · by_cases hkn1 : k = n + 1
      · subst hkn1
        have hmin : n + 1 ≤ min a.length b.length :=
          Nat.le_min.mpr ⟨hk.1, hk.2.1⟩
        exact absurd ⟨hmin, hk.2.2⟩ h
      · have hkn' : k ≤ n := by omega
        have hn' : n ≤ min a.length b.length := by omega
        exact ih k hk hkn' hn'

theorem overlap_match {α : Type*} [DecidableEq α] (a b : List α) :
    OverlapMatch a b (overlap a b) :=
  overlapAux_match a b (min a.length b.length) (Nat.le_refl _)

theorem overlap_le_left {α : Type*} [DecidableEq α] (a b : List α) :
    overlap a b ≤ a.length :=
  (overlap_match a b).1

theorem overlap_le_right {α : Type*} [DecidableEq α] (a b : List α) :
    overlap a b ≤ b.length :=
  (overlap_match a b).2.1

theorem overlap_ge_of_match {α : Type*} [DecidableEq α] (a b : List α) (k : Nat)
    (hk : OverlapMatch a b k) : k ≤ overlap a b :=
  overlapAux_ge a b (min a.length b.length) k hk
    (Nat.le_min.mpr ⟨hk.1, hk.2.1⟩) (Nat.le_refl _)

/-- Characterization: `overlap` is the greatest matching length. -/
theorem overlap_spec {α : Type*} [DecidableEq α] (a b : List α) (k : Nat) :
    k = overlap a b ↔
      OverlapMatch a b k ∧ ∀ k' : Nat, OverlapMatch a b k' → k' ≤ k := by
  constructor
  · intro h
    subst h
    exact ⟨overlap_match a b, fun k' hk' => overlap_ge_of_match a b k' hk'⟩
  · intro h
    obtain ⟨hmatch, hmax⟩ := h
    have hle1 : overlap a b ≤ k := hmax _ (overlap_match a b)
    have hle2 : k ≤ overlap a b := overlap_ge_of_match a b k hmatch
    omega

/-- Splice `b` onto `a` along their overlap. -/
def merge {α : Type*} [DecidableEq α] (a b : List α) : List α :=
  a ++ b.drop (overlap a b)

theorem length_merge {α : Type*} [DecidableEq α] (a b : List α) :
    (merge a b).length = a.length + b.length - overlap a b := by
  have hle : overlap a b ≤ b.length := overlap_le_right a b
  simp only [merge, List.length_append, List.length_drop]
  omega

theorem isPrefix_merge_self {α : Type*} [DecidableEq α] (a b : List α) :
    a <+: merge a b :=
  List.prefix_append a (b.drop (overlap a b))

theorem isSuffix_merge {α : Type*} [DecidableEq α] (a b : List α) :
    b <:+ merge a b := by
  obtain ⟨hale, hble, hmatch⟩ := overlap_match a b
  refine ⟨a.take (a.length - overlap a b), ?_⟩
  have ha : a.take (a.length - overlap a b) ++
      a.drop (a.length - overlap a b) = a :=
    List.take_append_drop _ _
  have hb : b.take (overlap a b) ++ b.drop (overlap a b) = b :=
    List.take_append_drop _ _
  simp only [merge]
  calc a.take (a.length - overlap a b) ++ b
      = a.take (a.length - overlap a b) ++
        (b.take (overlap a b) ++ b.drop (overlap a b)) := by rw [hb]
    _ = (a.take (a.length - overlap a b) ++ b.take (overlap a b)) ++
        b.drop (overlap a b) := by simp [List.append_assoc]
    _ = (a.take (a.length - overlap a b) ++
        a.drop (a.length - overlap a b)) ++ b.drop (overlap a b) := by
        rw [hmatch]
    _ = a ++ b.drop (overlap a b) := by rw [ha]

/-- Left fold of `merge` over a fixed ordering. -/
def mergeAll {α : Type*} [DecidableEq α] (l : List (List α)) : List α :=
  l.foldl merge []

theorem foldl_merge_prefix {α : Type*} [DecidableEq α] (l : List (List α)) :
    ∀ (init : List α), init <+: l.foldl merge init := by
  induction l with
  | nil =>
    intro init
    simp only [List.foldl_nil]
    exact List.prefix_rfl
  | cons hd tl ih =>
    intro init
    simp only [List.foldl_cons]
    exact (isPrefix_merge_self init hd).trans (ih _)

theorem foldl_merge_contains {α : Type*} [DecidableEq α] (l : List (List α)) :
    ∀ (init s : List α), s ∈ l → s <:+: (l.foldl merge init) := by
  induction l with
  | nil =>
    intro init s hmem
    simp at hmem
  | cons hd tl ih =>
    intro init s hmem
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    cases hmem with
    | inl heq =>
      rw [heq]
      exact (List.IsSuffix.isInfix (isSuffix_merge init hd)).trans
        (List.IsPrefix.isInfix (foldl_merge_prefix tl (merge init hd)))
    | inr hmem' => exact ih _ _ hmem'

/-- Every input string appears in the folded merge (superstring soundness). -/
theorem mem_mergeAll_contains {α : Type*} [DecidableEq α] (l : List (List α))
    (s : List α) (hmem : s ∈ l) : s <:+: mergeAll l :=
  foldl_merge_contains l [] s hmem

/-- Regrouping coherence of the fold along a fixed ordering: merging along
`l₁ ++ l₂` equals folding `l₂` onto the merge of `l₁`. Binary `merge` itself
is not associative (see `merge_not_associative`); the well-defined object is
the fold along a fixed ordering. -/
theorem mergeAll_append {α : Type*} [DecidableEq α] (l₁ l₂ : List (List α)) :
    mergeAll (l₁ ++ l₂) = l₂.foldl merge (mergeAll l₁) := by
  simp [mergeAll, List.foldl_append]

/-- Length unfolds one step along the fold; `length_merge` gives the
single-step length from the current accumulator. -/
theorem length_foldl_merge_cons {α : Type*} [DecidableEq α] (init s : List α)
    (l : List (List α)) :
    ((s :: l).foldl merge init).length =
      (l.foldl merge (merge init s)).length := by
  simp only [List.foldl_cons]

/-- Length of `mergeAll` over a cons ordering, in fold form. -/
theorem length_mergeAll_cons {α : Type*} [DecidableEq α] (s : List α)
    (l : List (List α)) :
    (mergeAll (s :: l)).length = (l.foldl merge (merge [] s)).length := by
  simp [mergeAll, List.foldl_cons]

/-- One fold step tracking the merged length alongside the accumulator: each
step adds `s.length - overlap` with the current accumulator. -/
def mergeLenStep {α : Type*} [DecidableEq α] (p : List α × Nat) (s : List α) :
    List α × Nat :=
  (merge p.1 s, p.2 + s.length - overlap p.1 s)

/-- The tracked length equals the actual folded length. -/
theorem foldl_mergeLenStep_snd {α : Type*} [DecidableEq α] (l : List (List α)) :
    ∀ (init : List α),
      (l.foldl mergeLenStep (init, init.length)).2 =
        (l.foldl merge init).length := by
  induction l with
  | nil =>
    intro init
    rfl
  | cons hd tl ih =>
    intro init
    simp only [List.foldl_cons, mergeLenStep]
    have h := length_merge init hd
    rw [← h]
    exact ih (merge init hd)

/-- Length of `mergeAll` as a tracked fold from the empty accumulator. -/
theorem length_mergeAll_fold {α : Type*} [DecidableEq α] (l : List (List α)) :
    (mergeAll l).length = (l.foldl mergeLenStep ([], 0)).2 := by
  have h := foldl_mergeLenStep_snd l []
  have hlen : ([] : List α).length = 0 := rfl
  rw [hlen] at h
  simp only [mergeAll]
  exact h.symm

/-- Binary `merge` is not associative: the two bracketings below evaluate to
`[1, 2]` and `[1, 2, 1, 2]` respectively. -/
theorem merge_not_associative :
    merge (merge [1] [2]) [1, 2] ≠ merge [1] (merge [2] [1, 2]) := by
  decide

/-- Full overlap holds exactly for suffixes. -/
theorem overlap_eq_right_length_iff_suffix {α : Type*} [DecidableEq α]
    (a b : List α) : overlap a b = b.length ↔ b <:+ a := by
  constructor
  · intro h
    obtain ⟨hale, hble, hmatch⟩ := overlap_match a b
    rw [h] at hmatch
    rw [List.take_length] at hmatch
    have hsplit : a.take (a.length - b.length) ++
        a.drop (a.length - b.length) = a :=
      List.take_append_drop _ _
    rw [hmatch] at hsplit
    exact ⟨a.take (a.length - b.length), hsplit⟩
  · intro h
    obtain ⟨pre, hpre⟩ := h
    have hlen_eq : pre.length + b.length = a.length := by
      have hcon := congrArg List.length hpre
      simp [List.length_append] at hcon
      exact hcon
    have hblen : b.length ≤ a.length := by omega
    have hmatch : OverlapMatch a b b.length := by
      refine ⟨hblen, Nat.le_refl _, ?_⟩
      rw [List.take_length]
      have hlen : a.length - b.length = pre.length := by omega
      rw [hlen, ← hpre, List.drop_left]
    have hge : b.length ≤ overlap a b := overlap_ge_of_match a b _ hmatch
    have hle : overlap a b ≤ b.length := overlap_le_right a b
    omega

/-- Substring-free inputs overlap strictly below full length, both ways. -/
theorem overlap_lt_of_substring_free {α : Type*} [DecidableEq α]
    (a b : List α) (hb : ¬b <:+: a) (ha : ¬a <:+: b) :
    overlap a b < b.length ∧ overlap b a < a.length := by
  constructor
  · have hle : overlap a b ≤ b.length := overlap_le_right a b
    have hne : overlap a b ≠ b.length := by
      intro hcon
      exact hb (List.IsSuffix.isInfix
        ((overlap_eq_right_length_iff_suffix a b).mp hcon))
    omega
  · have hle : overlap b a ≤ a.length := overlap_le_right b a
    have hne : overlap b a ≠ a.length := by
      intro hcon
      exact ha (List.IsSuffix.isInfix
        ((overlap_eq_right_length_iff_suffix b a).mp hcon))
    omega

end Cslib.Bioinformatics.Assembly.StringOverlap
