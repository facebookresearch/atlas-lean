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

/-- **Pattern match at an offset.** For lists $p$ (the pattern) and $t$ (the text) over a type
$\alpha$ and a natural number $k$, the pattern $p$ matches the text $t$ at the zero-based offset
$k$ when $k$ is at most the length of $t$ and $p$ is a prefix of the list obtained from $t$ by
dropping its first $k$ entries.

The explicit bound on $k$ excludes offsets beyond the end of the text for an empty pattern. -/
def MatchAt (pattern text : List α) (offset : Nat) : Prop :=
  offset ≤ text.length ∧ pattern <+: text.drop offset

/-- **Characterization of a match at an offset.** For lists $p$ and $t$ and a natural number $k$,
the pattern $p$ matches the text $t$ at the zero-based offset $k$ if and only if $k$ is at most
the length of $t$ and $p$ is a prefix of the list obtained from $t$ by dropping its first $k$
entries. -/
theorem matchAt_iff (pattern text : List α) (offset : Nat) :
    MatchAt pattern text offset ↔ offset ≤ text.length ∧ pattern <+: text.drop offset :=
  Iff.rfl

/-- **A pattern occurs in a text iff it matches at some offset.** For lists $p$ and $t$, there
is an offset $k$ such that the pattern $p$ matches the text $t$ at $k$ if and only if $p$ is an
infix of $t$, that is, $t$ is the concatenation of some list $u$, then $p$, then some list $v$. -/
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
