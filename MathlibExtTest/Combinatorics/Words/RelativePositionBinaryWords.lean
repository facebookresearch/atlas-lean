/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords

/-! # Tests for positions in binary words -/

namespace MetaMathlibExt.relativePosition_of_dimers

-- The periodic word abbaabba… has both block orientations, with a repeated b at the join.
private def abba (i : ℕ) : Bool := decide (i % 4 = 0 ∨ i % 4 = 3)

example : relativePosition abba 1 = 1 ∧ relativePosition abba 2 = -1 := by
  have blocks (i : ℕ) : abba (2 * i) ≠ abba (2 * i + 1) := by
    simp only [abba, ne_eq, decide_eq_decide]
    omega
  exact ⟨relativePosition_of_dimers blocks 1 (by decide),
    relativePosition_of_dimers blocks 2 (by decide)⟩

-- Only the second block is partially present in this prefix.
example : letterCount abba true 3 = 1 ∧ letterCount abba false 3 = 2 := by decide

-- When b is absent, its position defaults to zero at every occurrence index.
example (n : ℕ) : letterPosition (fun _ => true) false n = 0 := by
  simp [letterPosition]

-- Removing the leading a of abbaabba… exposes the first b.
example : deleteFirst abba true 0 = false :=
  congrFun (deleteFirst_of_head (w := abba) (α := true) rfl) 0

-- The growth condition rules out a substitution that erases every letter.
example (w v : ℕ → Bool) : ¬IsSubstitutionImage (fun _ => []) w v := by
  intro h
  obtain ⟨m, hm⟩ := h.1 1
  have erases : ((List.ofFn fun j : Fin m => w j).flatMap fun _ => ([] : List Bool)) = [] := by
    simp
  simp [erases] at hm

private theorem abba_infinite : BothLettersInfinite abba := by
  constructor
  · refine (Set.infinite_range_of_injective (f := fun n : ℕ => 4 * n) ?_).mono ?_
    · intro a b h
      change 4 * a = 4 * b at h
      omega
    · rintro _ ⟨n, rfl⟩
      simp [abba]
  · refine (Set.infinite_range_of_injective (f := fun n : ℕ => 4 * n + 1) ?_).mono ?_
    · intro a b h
      change 4 * a + 1 = 4 * b + 1 at h
      omega
    · rintro _ ⟨n, rfl⟩
      simp [abba, Nat.add_mod]

-- The run bb gives both a gap greater than two between a's and adjacent b's.
example : (∃ n, 1 ≤ n ∧ 2 < letterPosition abba true (n + 1) - letterPosition abba true n) ∧
    ∃ n, 1 ≤ n ∧ letterPosition abba false (n + 1) - letterPosition abba false n = 1 := by
  have run : ∃ i, ∀ j < 2, abba (i + j) = false := by
    refine ⟨1, fun j hj => ?_⟩
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl <;> decide
  have equivs := subword_run_iff_letterPosition_diff abba_infinite rfl (k := 2) (by decide)
  obtain ⟨n, hn, h⟩ := equivs.2.1.mp run
  exact ⟨equivs.1.mp run, n, hn, by simpa only [Nat.add_zero] using h 0 (by decide)⟩

-- A length-one run needs no adjacent occurrence gaps.
example : ∃ i, ∀ j < 1, abba (i + j) = true := by
  apply (subword_run_iff_letterPosition_diff abba_infinite rfl (k := 1) (by decide)).2.2.mpr
  exact ⟨1, by decide, fun j hj => by omega⟩

end MetaMathlibExt.relativePosition_of_dimers
