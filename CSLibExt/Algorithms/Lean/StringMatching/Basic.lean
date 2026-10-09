/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Infix

/-!
# String-matching semantics

This module defines the shared meaning of a list pattern matching at a zero-based offset.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.StringMatching

universe u

variable {α : Type u}

/-- `MatchAt pattern text offset` means that `pattern` is a prefix of `text` starting at the
zero-based `offset`. The explicit bound excludes offsets beyond the end for an empty pattern. -/
def MatchAt (pattern text : List α) (offset : Nat) : Prop :=
  offset ≤ text.length ∧ pattern <+: text.drop offset

/-- The definition of a match at a zero-based offset. -/
theorem matchAt_iff (pattern text : List α) (offset : Nat) :
    MatchAt pattern text offset ↔ offset ≤ text.length ∧ pattern <+: text.drop offset :=
  Iff.rfl

/-- A pattern occurs as an infix exactly when it matches at some bounded offset. -/
theorem exists_matchAt_iff_isInfix (pattern text : List α) :
    (∃ offset, MatchAt pattern text offset) ↔ pattern <:+: text := by
  rw [List.infix_iff_prefix_suffix]
  constructor
  · rintro ⟨offset, hoffset, hprefix⟩
    exact ⟨text.drop offset, hprefix, text.drop_suffix offset⟩
  · rintro ⟨suffix, hprefix, ⟨head, rfl⟩⟩
    refine ⟨head.length, ?_, ?_⟩
    · simp
    · simpa using hprefix

end Cslib.Algorithms.Lean.StringMatching
