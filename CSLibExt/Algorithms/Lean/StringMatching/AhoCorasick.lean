/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.Basic

/-!
# Aho–Corasick: semantic specification of the state and the reports

For a list of patterns `pats`, the Aho–Corasick automaton (Aho and Corasick, 1975) is designed so
that after reading `w` its state represents the longest suffix of `w` that is a prefix of some
pattern. This file defines that state semantically, as `stateSpec pats w`, and the reports it
determines, `ReportsSpec pats text i p`: the nonempty pattern `p` is a suffix of the state after
the first `i + 1` symbols of `text`. It proves that the state is a suffix of the input, is empty or
a pattern prefix, and has every pattern-prefix suffix of the input as a suffix, and that the
reports are exactly the occurrences of the patterns ending at position `i`, in the `MatchAt`
semantics of `Cslib.Algorithms.Lean.StringMatching.Basic`.

This is a specification, not an implementation: there is no trie, goto or failure function,
output function or scan procedure here, and no correctness theorem for an executable scanner. A
scanner proved correct against this file would show that its state after reading `w` represents
`stateSpec pats w` and that it reports exactly `ReportsSpec`.

## Main results

* `stateSpec_isSuffix`, `stateSpec_isPrefix`, `stateSpec_maximal`: the state is a suffix of the
  input, empty or a pattern prefix, and maximal among the pattern-prefix suffixes.
* `reportsSpec_iff_occurs`: a nonempty pattern is reported ending at position `i` iff it is a
  suffix of the first `i + 1` symbols of the text.
* `reportsSpec_iff_matchAt`: the same occurrence as a `MatchAt` at offset `i + 1 - p.length`.

## References

* A. V. Aho and M. J. Corasick, *Efficient string matching: an aid to bibliographic search*,
  Comm. ACM 18 (1975), 333–340.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.StringMatching.AhoCorasick

universe u

variable {α : Type u} [DecidableEq α]

/-- `s` is a prefix of some pattern in `pats`. -/
def IsPatternPrefix (pats : List (List α)) (s : List α) : Prop :=
  ∃ p ∈ pats, s <+: p

instance (pats : List (List α)) (s : List α) : Decidable (IsPatternPrefix pats s) :=
  inferInstanceAs (Decidable (∃ p ∈ pats, s <+: p))

/-- The specified Aho–Corasick state after reading `w`: the longest suffix of `w` that is a prefix
of some pattern, with the empty list, always a suffix, as the fallback. `w.tails` lists the
suffixes of `w` longest first, so this is the first suffix that passes the test. -/
def stateSpec (pats : List (List α)) (w : List α) : List α :=
  (w.tails.filter (fun s => s = [] ∨ IsPatternPrefix pats s)).headD []

/-- The specified reports: the nonempty pattern `p` is reported ending at position `i` of `text`
when it is a suffix of the specified state after the first `i + 1` symbols. -/
def ReportsSpec (pats : List (List α)) (text : List α) (i : ℕ) (p : List α) : Prop :=
  i < text.length ∧ p ∈ pats ∧ p ≠ [] ∧ p <:+ stateSpec pats (text.take (i + 1))

instance (pats : List (List α)) (text : List α) (i : ℕ) (p : List α) :
    Decidable (ReportsSpec pats text i p) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem stateSpec_nil (pats : List (List α)) :
    stateSpec pats [] = [] := by
  simp [stateSpec]

private theorem stateSpec_cons_of_mem (pats : List (List α)) (a : α) (l : List α)
    (h : IsPatternPrefix pats (a :: l)) : stateSpec pats (a :: l) = a :: l := by
  simp [stateSpec, h]

private theorem stateSpec_cons_of_not_mem (pats : List (List α)) (a : α) (l : List α)
    (h : ¬ IsPatternPrefix pats (a :: l)) : stateSpec pats (a :: l) = stateSpec pats l := by
  simp [stateSpec, h]

/-- The state is a suffix of the input. -/
theorem stateSpec_isSuffix (pats : List (List α)) (w : List α) :
    stateSpec pats w <:+ w := by
  induction w with
  | nil =>
    rw [stateSpec_nil]
  | cons a l ih =>
    by_cases h : IsPatternPrefix pats (a :: l)
    · rw [stateSpec_cons_of_mem _ _ _ h]
    · rw [stateSpec_cons_of_not_mem _ _ _ h]
      exact List.IsSuffix.trans ih ⟨[a], rfl⟩

/-- The state is the empty fallback or a prefix of some pattern. -/
theorem stateSpec_isPrefix (pats : List (List α)) (w : List α) :
    stateSpec pats w = [] ∨ IsPatternPrefix pats (stateSpec pats w) := by
  induction w with
  | nil =>
    rw [stateSpec_nil]
    exact Or.inl rfl
  | cons a l ih =>
    by_cases h : IsPatternPrefix pats (a :: l)
    · rw [stateSpec_cons_of_mem _ _ _ h]
      exact Or.inr h
    · rw [stateSpec_cons_of_not_mem _ _ _ h]
      exact ih

/-- Maximality: every suffix of `w` that is a pattern prefix is a suffix of the state. -/
theorem stateSpec_maximal (pats : List (List α)) (w : List α)
    (s : List α) (hs : s <:+ w) (hsp : IsPatternPrefix pats s) :
    s <:+ stateSpec pats w := by
  induction w generalizing s with
  | nil =>
    rw [stateSpec_nil]
    exact hs
  | cons a l ih =>
    by_cases h : IsPatternPrefix pats (a :: l)
    · rw [stateSpec_cons_of_mem _ _ _ h]
      exact hs
    · rw [stateSpec_cons_of_not_mem _ _ _ h]
      rw [List.suffix_cons_iff] at hs
      cases hs with
      | inl heq =>
        rw [heq] at hsp
        exact absurd hsp h
      | inr hs' =>
        exact ih _ hs' hsp

/-- The specified reports are the occurrences: a nonempty pattern is reported ending at position
`i` iff it occurs in the text ending exactly at `i`. This characterizes `ReportsSpec`; it is not
a correctness theorem for an Aho–Corasick scanner. -/
theorem reportsSpec_iff_occurs {pats : List (List α)}
    {text : List α} {i : ℕ} {p : List α} (hp : p ∈ pats)
    (hne : p ≠ []) (hi : i < text.length) :
    ReportsSpec pats text i p ↔
      ∃ pre, text.take (i + 1) = pre ++ p := by
  unfold ReportsSpec
  constructor
  · intro h
    obtain ⟨-, -, -, hsuf⟩ := h
    have hstate : stateSpec pats (text.take (i + 1)) <:+ text.take (i + 1) :=
      stateSpec_isSuffix _ _
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
    have hpp : IsPatternPrefix pats p := ⟨p, hp, List.prefix_refl p⟩
    have hsuf : p <:+ stateSpec pats (text.take (i + 1)) :=
      stateSpec_maximal pats _ p hp_take hpp
    exact ⟨hi, hp, hne, hsuf⟩

/-- The specified reports in the shared string-matching semantics: a nonempty pattern `p` is
reported ending at position `i` iff it fits before `i + 1` and matches at the offset
`i + 1 - p.length` in the sense of `MatchAt`. -/
theorem reportsSpec_iff_matchAt {pats : List (List α)}
    {text : List α} {i : ℕ} {p : List α} (hp : p ∈ pats)
    (hne : p ≠ []) (hi : i < text.length) :
    ReportsSpec pats text i p ↔ p.length ≤ i + 1 ∧ MatchAt p text (i + 1 - p.length) := by
  rw [reportsSpec_iff_occurs hp hne hi, matchAt_iff]
  constructor
  · rintro ⟨pre, hpre⟩
    have hlen : pre.length + p.length = i + 1 := by
      have := congrArg List.length hpre
      rw [List.length_take, List.length_append] at this
      omega
    have hdrop : text.drop pre.length = p ++ text.drop (i + 1) := by
      have h := congrArg (List.drop pre.length) (List.take_append_drop (i + 1) text)
      rw [hpre, List.append_assoc, List.drop_left] at h
      exact h.symm
    have hoff : i + 1 - p.length = pre.length := by omega
    refine ⟨by omega, by omega, ?_⟩
    rw [hoff]
    exact ⟨text.drop (i + 1), hdrop.symm⟩
  · rintro ⟨hlen, -, hpre⟩
    refine ⟨text.take (i + 1 - p.length), ?_⟩
    have hk : i + 1 = (i + 1 - p.length) + p.length := by omega
    conv_lhs => rw [hk]
    rw [List.take_add, ← List.prefix_iff_eq_take.mp hpre]

end Cslib.Algorithms.Lean.StringMatching.AhoCorasick
