/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LTL: run semantics versus ω-word semantics
-/
module

public import CSLibExt.Logics.LTL.Basic
public import CSLibExt.Logics.LTL.OmegaWord
public import CSLibExt.Foundations.Semantics.LTS.CslibBridge

/-!
# The run semantics of LTL agrees with the ω-word semantics

`Cslib.LTL.Satisfies` (in `CSLibExt.Logics.LTL.Basic`) interprets LTL over
state runs `ℕ → State` of canonical `Cslib.LTS`, moving along suffixes with
`Cslib.Semantics.shiftSeq`. `Cslib.LTL.Word.Satisfies` (in
`CSLibExt.Logics.LTL.OmegaWord`) interprets the same formulas over canonical CSLib
ω-words `Cslib.ωSequence`. This file proves they agree on every formula
(`Cslib.LTL.satisfies_iff_word_satisfies`) through
`Cslib.Semantics.LTS.shiftSeq_eq_drop`, the state-sequence/ω-word identity in
`CSLibExt.Foundations.Semantics.LTS.CslibBridge`.
-/

@[expose] public section

namespace Cslib
namespace LTL

variable {Atom State : Type*}

/-- The run semantics of LTL is the ω-word semantics on the run read as an ω-word. -/
theorem satisfies_iff_word_satisfies (valuation : State → Atom → Prop) :
    ∀ (φ : Formula Atom) (run : ℕ → State),
      Satisfies valuation run φ ↔ Word.Satisfies valuation ⟨run⟩ φ
  | .atom _, _ => Iff.rfl
  | .top, _ => Iff.rfl
  | .not φ, run => not_congr (satisfies_iff_word_satisfies valuation φ run)
  | .and φ ψ, run =>
      and_congr (satisfies_iff_word_satisfies valuation φ run)
        (satisfies_iff_word_satisfies valuation ψ run)
  | .next φ, run => by
      rw [Satisfies.next_iff, SatisfiesAt, satisfies_iff_word_satisfies valuation φ,
        Semantics.LTS.shiftSeq_eq_drop]
      rfl
  | .until φ ψ, run => by
      rw [Satisfies.until_iff, Word.Satisfies.until_iff]
      simp only [SatisfiesAt, Word.SatisfiesAt, satisfies_iff_word_satisfies valuation φ,
        satisfies_iff_word_satisfies valuation ψ, Semantics.LTS.shiftSeq_eq_drop]

/-- Positional form of `satisfies_iff_word_satisfies`: for every valuation, run, position `k`
and formula, the formula holds at position `k` of the run under the run semantics iff it holds
at position `k` of the ω-word of the run's states under the word semantics with the same
valuation. -/
theorem satisfiesAt_iff_word_satisfiesAt (valuation : State → Atom → Prop) (run : ℕ → State)
    (k : ℕ) (φ : Formula Atom) :
    SatisfiesAt valuation run k φ ↔ Word.SatisfiesAt valuation ⟨run⟩ k φ := by
  rw [SatisfiesAt, satisfies_iff_word_satisfies, Semantics.LTS.shiftSeq_eq_drop]
  rfl

end LTL
end Cslib
