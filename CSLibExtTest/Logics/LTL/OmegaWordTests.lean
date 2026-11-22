/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.OmegaWord

/-!
# Consumer tests for the LTL ω-word semantics

Concrete words over the alphabet `Set Bool` (letters are sets of true atoms)
exercise the boundary cases of the semantics: atoms at position zero,
`next`/`drop` movement, `until` discharged immediately or at a successor,
`release`, and the `GF`/`FG` filter characterizations.
-/

open Filter Cslib Cslib.LTL Cslib.LTL.Word

namespace LTLWordTests

/-- The membership valuation: an atom holds at a letter when it is in the set. -/
def val : Set Bool → Bool → Prop := fun s a => a ∈ s

/-- The constant word where `true` always holds. -/
def allTrue : ωSequence (Set Bool) := ωSequence.const {true}

/-- The word where `true` holds from position `1` on, but not at position `0`. -/
def late : ωSequence (Set Bool) := ⟨fun n => if n = 0 then ∅ else {true}⟩

/-- An atom is read at the first letter. -/
example : Satisfies val allTrue (.atom true) := by
  simp [Satisfies, val, allTrue]

example : ¬ Satisfies val allTrue (.atom false) := by
  simp [Satisfies, val, allTrue]

/-- `next` moves to the tail: on `late`, `true` holds one step later. -/
example : Satisfies val late (.next (.atom true)) := by
  simp [Satisfies, val, late, ωSequence.tail]

/-- Satisfaction at position `1` of `late`, via the positional API. -/
example : SatisfiesAt val late 1 (.atom true) := by
  simp [satisfiesAt_atom, val, late]

/-- Position `j` of the suffix at `k` is position `k + j`. -/
example : SatisfiesAt val (late.drop 1) 0 (.atom true) := by
  rw [satisfiesAt_drop]
  simp [satisfiesAt_atom, val, late]

/-- `until` discharged at index zero needs no `φ` positions. -/
example : Satisfies val allTrue (.until (.atom false) (.atom true)) := by
  rw [Satisfies.until_iff]
  exact ⟨0, by simp [satisfiesAt_atom, val, allTrue], by simp⟩

/-- `until` discharged at a successor, with `φ` holding before it. -/
example : Satisfies val late (.until .top (.atom true)) := by
  rw [Satisfies.until_iff]
  refine ⟨1, by simp [satisfiesAt_atom, val, late], ?_⟩
  intro j hj
  obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
  simp [SatisfiesAt, Satisfies]

/-- `eventually` from the first succeeding position. -/
example : Satisfies val late (Formula.eventually (.atom true)) := by
  rw [Satisfies.eventually_iff]
  exact ⟨1, by simp [satisfiesAt_atom, val, late]⟩

/-- `always` on the constant word. -/
example : Satisfies val allTrue (Formula.always (.atom true)) := by
  rw [Satisfies.always_iff]
  intro k
  simp [satisfiesAt_atom, val, allTrue]

/-- `release` where the released formula holds everywhere. -/
example : Satisfies val allTrue (Formula.release (.atom true) (.atom true)) := by
  rw [Satisfies.release_iff]
  intro k
  exact Or.inl (by simp [satisfiesAt_atom, val, allTrue])

/-- `GF`: on the constant word, `true` holds infinitely often. -/
example : Satisfies val allTrue (Formula.always (Formula.eventually (.atom true))) := by
  rw [Satisfies.always_eventually_iff, Filter.frequently_atTop]
  intro k
  exact ⟨k, le_refl k, by simp [satisfiesAt_atom, val, allTrue]⟩

/-- `FG`: on `late`, `true` holds at all but finitely many positions. -/
example : Satisfies val late (Formula.eventually (Formula.always (.atom true))) := by
  rw [Satisfies.eventually_always_iff, Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro k hk
  simp [satisfiesAt_atom, val, late, show k ≠ 0 by omega]

/-- Language membership is satisfaction. -/
example : allTrue ∈ language val (.atom true) := by
  show Satisfies val allTrue (.atom true)
  simp [Satisfies, val, allTrue, ωSequence.const]

example : late ∉ language val (.atom true) := by
  show ¬ Satisfies val late (.atom true)
  simp [Satisfies, val, late]

end LTLWordTests
