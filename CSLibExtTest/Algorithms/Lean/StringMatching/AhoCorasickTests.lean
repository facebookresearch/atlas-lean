/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.AhoCorasick

/-!
# Aho–Corasick specification tests

The patterns `he`, `she`, `his`, `hers` over the text `ushers`, the example of Aho and Corasick
(1975), with the letters encoded as `h = 1`, `e = 2`, `s = 3`, `i = 4`, `r = 5`, `u = 6`. The
checks cover the state after a mismatch (fallback), overlapping occurrences, a pattern that is a
suffix of another, positions with no report, and the index boundaries `0` and `text.length`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open Cslib.Algorithms.Lean.StringMatching
open Cslib.Algorithms.Lean.StringMatching.AhoCorasick

/-- `he`, `she`, `his`, `hers`. -/
private abbrev acPatterns : List (List Nat) := [[1, 2], [3, 1, 2], [1, 4, 3], [1, 2, 5, 3]]

/-- `ushers`. -/
private abbrev acText : List Nat := [6, 3, 1, 2, 5, 3]

/-! ### States -/

/-- `u` starts no pattern: the state is the empty fallback. -/
example : stateSpec acPatterns (acText.take 1) = [] := by decide

/-- After `ushe` the state is `she`, the longest suffix that is a pattern prefix. -/
example : stateSpec acPatterns (acText.take 4) = [3, 1, 2] := by decide

/-- Fallback after a mismatch: `sher` is no pattern prefix, so after `usher` the state falls back
from `she` to `her`, a prefix of `hers`. -/
example : stateSpec acPatterns (acText.take 5) = [1, 2, 5] := by decide

/-- After `ushers` the state is `hers`. -/
example : stateSpec acPatterns acText = [1, 2, 5, 3] := by decide

/-! ### Reports -/

/-- `she` ends at position `3`. -/
example : ReportsSpec acPatterns acText 3 [3, 1, 2] := by decide

/-- `he`, a suffix of `she`, ends at position `3` as well. -/
example : ReportsSpec acPatterns acText 3 [1, 2] := by decide

/-- `hers` ends at position `5`, the last index; it overlaps `she` (positions `1` to `3`). -/
example : ReportsSpec acPatterns acText 5 [1, 2, 5, 3] := by decide

/-- `his` does not occur, so it is never reported. -/
example : ∀ i < acText.length, ¬ ReportsSpec acPatterns acText i [1, 4, 3] := by decide

/-- No pattern ends at position `4` (`usher`). -/
example : ∀ p ∈ acPatterns, ¬ ReportsSpec acPatterns acText 4 p := by decide

/-- Lower boundary: no pattern ends at position `0`. -/
example : ∀ p ∈ acPatterns, ¬ ReportsSpec acPatterns acText 0 p := by decide

/-- Upper boundary: position `text.length` is out of range, although the whole text ends with
`hers`. -/
example : ¬ ReportsSpec acPatterns acText acText.length [1, 2, 5, 3] := by decide

/-- The empty pattern is never reported, even when it is listed. -/
example : ¬ ReportsSpec ([] :: acPatterns) acText 3 [] := by decide

/-- The reports at position `3` in the `MatchAt` semantics: `she` matches at offset `1`. -/
example : MatchAt [3, 1, 2] acText 1 :=
  ((reportsSpec_iff_matchAt (by decide) (by decide) (by decide)).mp
    (show ReportsSpec acPatterns acText 3 [3, 1, 2] by decide)).2

/-! ### API -/

example {α : Type u} [DecidableEq α] (pats : List (List α)) (w : List α) :
    stateSpec pats w <:+ w :=
  stateSpec_isSuffix pats w

example {α : Type u} [DecidableEq α] (pats : List (List α)) (w : List α) :
    stateSpec pats w = [] ∨ IsPatternPrefix pats (stateSpec pats w) :=
  stateSpec_isPrefix pats w

example {α : Type u} [DecidableEq α] (pats : List (List α)) (w s : List α) (hs : s <:+ w)
    (hsp : IsPatternPrefix pats s) : s <:+ stateSpec pats w :=
  stateSpec_maximal pats w s hs hsp

example {α : Type u} [DecidableEq α] {pats : List (List α)} {text p : List α} {i : Nat}
    (hp : p ∈ pats) (hne : p ≠ []) (hi : i < text.length) :
    ReportsSpec pats text i p ↔ ∃ pre, text.take (i + 1) = pre ++ p :=
  reportsSpec_iff_occurs hp hne hi

example {α : Type u} [DecidableEq α] {pats : List (List α)} {text p : List α} {i : Nat}
    (hp : p ∈ pats) (hne : p ≠ []) (hi : i < text.length) :
    ReportsSpec pats text i p ↔ p.length ≤ i + 1 ∧ MatchAt p text (i + 1 - p.length) :=
  reportsSpec_iff_matchAt hp hne hi
