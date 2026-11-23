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

end MetaMathlibExt.relativePosition_of_dimers
