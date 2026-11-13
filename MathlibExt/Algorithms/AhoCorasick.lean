/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

@[expose] public section


open List

variable {α : Type*} [DecidableEq α]

/-- `s` is a prefix of some pattern. -/
def patPrefix (pats : List (List α)) (s : List α) : Prop :=
  ∃ p ∈ pats, s <+: p

/-- All suffixes of a list, longest first. -/
def suffixesOf : List α → List (List α)
  | [] => [[]]
  | (a :: l) => (a :: l) :: suffixesOf l

/-- Membership in `suffixesOf` is exactly the suffix relation. -/
theorem mem_suffixesOf {s w : List α} :
    s ∈ suffixesOf w ↔ s <:+ w := by
  induction w generalizing s with
  | nil =>
    simp [suffixesOf, List.suffix_nil]
  | cons a l ih =>
    simp [suffixesOf, ih, List.suffix_cons_iff]

/-- The Aho-Corasick state after reading `w`: the longest suffix
of `w` that is a prefix of some pattern (the empty list, always a
suffix, is the fallback state). -/
noncomputable def stateOf (pats : List (List α)) (w : List α) :
    List α :=
  open Classical in
  ((suffixesOf w).filter (fun s => s = [] ∨ patPrefix pats s)).headD []

/-- The automaton reports pattern `p` ending at position `i` of
`text` when `p` is a nonempty pattern and a suffix of the state
after the first `i + 1` characters. -/
def Reports (pats : List (List α)) (text : List α) (i : ℕ)
    (p : List α) : Prop :=
  i < text.length ∧ p ∈ pats ∧ p ≠ [] ∧
    p <:+ stateOf pats (text.take (i + 1))

private theorem stateOf_nil (pats : List (List α)) :
    stateOf pats [] = [] := by
  classical
  simp [stateOf, suffixesOf]

private theorem stateOf_cons_of_mem (pats : List (List α)) (a : α) (l : List α)
    (h : patPrefix pats (a :: l)) : stateOf pats (a :: l) = a :: l := by
  classical
  simp [stateOf, suffixesOf, h]

private theorem stateOf_cons_of_not_mem (pats : List (List α)) (a : α) (l : List α)
    (h : ¬ patPrefix pats (a :: l)) : stateOf pats (a :: l) = stateOf pats l := by
  classical
  simp [stateOf, suffixesOf, h]

/-- The state is a suffix of the input. -/
theorem stateOf_isSuffix (pats : List (List α)) (w : List α) :
    stateOf pats w <:+ w := by
  classical
  induction w with
  | nil =>
    rw [stateOf_nil]
    exact ⟨[], rfl⟩
  | cons a l ih =>
    by_cases h : patPrefix pats (a :: l)
    · rw [stateOf_cons_of_mem _ _ _ h]
      exact ⟨[], rfl⟩
    · rw [stateOf_cons_of_not_mem _ _ _ h]
      exact List.IsSuffix.trans ih ⟨[a], rfl⟩

/-- The state is the empty fallback or a prefix of some
pattern. -/
theorem stateOf_isPrefix (pats : List (List α)) (w : List α) :
    stateOf pats w = [] ∨ patPrefix pats (stateOf pats w) := by
  classical
  induction w with
  | nil =>
    rw [stateOf_nil]
    exact Or.inl rfl
  | cons a l ih =>
    by_cases h : patPrefix pats (a :: l)
    · rw [stateOf_cons_of_mem _ _ _ h]
      exact Or.inr h
    · rw [stateOf_cons_of_not_mem _ _ _ h]
      exact ih

/-- Maximality: every suffix of `w` that is a pattern prefix is a
suffix of the state. -/
theorem stateOf_maximal (pats : List (List α)) (w : List α)
    (s : List α) (hs : s <:+ w) (hsp : patPrefix pats s) :
    s <:+ stateOf pats w := by
  classical
  induction w generalizing s with
  | nil =>
    rw [stateOf_nil]
    exact hs
  | cons a l ih =>
    by_cases h : patPrefix pats (a :: l)
    · rw [stateOf_cons_of_mem _ _ _ h]
      exact hs
    · rw [stateOf_cons_of_not_mem _ _ _ h]
      rw [List.suffix_cons_iff] at hs
      cases hs with
      | inl heq =>
        rw [heq] at hsp
        exact absurd hsp h
      | inr hs' =>
        exact ih _ hs' hsp

/-- Correctness of the scan: a nonempty pattern is reported
ending at position `i` iff it occurs in the text ending exactly
at `i`. -/
theorem reports_iff_occurs {pats : List (List α)}
    {text : List α} {i : ℕ} {p : List α} (hp : p ∈ pats)
    (hne : p ≠ []) (hi : i < text.length) :
    Reports pats text i p ↔
      ∃ pre, text.take (i + 1) = pre ++ p := by
  classical
  unfold Reports
  constructor
  · intro h
    obtain ⟨-, -, -, hsuf⟩ := h
    have hstate : stateOf pats (text.take (i + 1)) <:+ text.take (i + 1) :=
      stateOf_isSuffix _ _
    have hp_take : p <:+ text.take (i + 1) :=
      List.IsSuffix.trans hsuf hstate
    rw [List.suffix_iff_exists_append_eq] at hp_take
    obtain ⟨pre, hpre⟩ := hp_take
    exact ⟨pre, hpre.symm⟩
  · intro h
    obtain ⟨pre, hpre⟩ := h
    have hp_take : p <:+ text.take (i + 1) := by
      rw [List.suffix_iff_exists_append_eq]
      exact ⟨pre, hpre.symm⟩
    have hpp : patPrefix pats p := ⟨p, hp, List.prefix_refl p⟩
    have hsuf : p <:+ stateOf pats (text.take (i + 1)) :=
      stateOf_maximal pats _ p hp_take hpp
    exact ⟨hi, hp, hne, hsuf⟩
