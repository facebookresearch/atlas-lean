/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.RelativePositionIncrements

/-! # Tests for relative position increments -/

namespace MetaMathlibExt.abs_relativePosition_diff_sub_le

private def abba (i : ℕ) : Bool := decide (i % 4 = 0 ∨ i % 4 = 3)

private theorem abba_dimers (i : ℕ) : abba (2 * i) ≠ abba (2 * i + 1) := by
  simp only [abba, ne_eq, decide_eq_decide]
  omega

private theorem abba_infinite : BothLettersInfinite abba := by
  constructor
  · apply Set.infinite_of_forall_exists_gt
    intro i
    exact ⟨4 * (i + 1), by simp [abba], by omega⟩
  · apply Set.infinite_of_forall_exists_gt
    intro i
    exact ⟨4 * (i + 1) + 1, by simp [abba, Nat.add_mod], by omega⟩

private theorem abba_no_three_false : ¬ ∃ i, ∀ j < 3, abba (i + j) = false := by
  rintro ⟨i, hi⟩
  have h₀ := hi 0 (by decide)
  have h₁ := hi 1 (by decide)
  have h₂ := hi 2 (by decide)
  simp [abba] at h₀ h₁ h₂
  omega

-- At the first increment of abbaabba…, the bound is attained: the signed increment is −2
-- and the false-letter gap is 1.
example : |(relativePosition abba 2 - relativePosition abba 1) -
    ((letterPosition abba false 2 : ℤ) - letterPosition abba false 1)| = 3 := by
  have b₁ : letterPosition abba false 1 = 1 := by
    have hc : Nat.count (fun i => abba i = false) 1 = 0 := by decide
    change Nat.nth (fun i => abba i = false) 0 = 1
    simpa only [hc] using Nat.nth_count (p := fun i => abba i = false) (n := 1) (by decide)
  have b₂ : letterPosition abba false 2 = 2 := by
    have hc : Nat.count (fun i => abba i = false) 2 = 1 := by decide
    change Nat.nth (fun i => abba i = false) 1 = 2
    simpa only [hc] using Nat.nth_count (p := fun i => abba i = false) (n := 2) (by decide)
  apply le_antisymm
  · exact (abs_relativePosition_diff_sub_le abba_infinite rfl abba_no_three_false).1 1 le_rfl
  · rw [relativePosition_of_dimers abba_dimers 1 le_rfl,
      relativePosition_of_dimers abba_dimers 2 (by decide), b₁, b₂]
    decide

-- The boundedness equivalence accepts an integer bound even when relative increments change sign.
example : ∃ C : ℕ, ∀ n, 1 ≤ n →
    letterPosition abba false (n + 1) - letterPosition abba false n ≤ C := by
  apply (abs_relativePosition_diff_sub_le abba_infinite rfl abba_no_three_false).2.mp
  refine ⟨2, fun n hn => ?_⟩
  rw [relativePosition_of_dimers abba_dimers (n + 1) (by omega),
    relativePosition_of_dimers abba_dimers n hn]
  split <;> split <;> decide

-- Independently bound the false-letter gaps using the period, then use the reverse implication.
example : ∃ C : ℤ, ∀ n, 1 ≤ n → |relativePosition abba (n + 1) - relativePosition abba n| ≤ C := by
  apply (abs_relativePosition_diff_sub_le abba_infinite rfl abba_no_three_false).2.mpr
  refine ⟨4, fun n hn => ?_⟩
  let p (i : ℕ) : Prop := abba i = false
  have hinf : (Set.ofPred p).Infinite := abba_infinite.2
  have hmem : p (Nat.nth p (n - 1)) := Nat.nth_mem_of_infinite hinf _
  have hnext : p (Nat.nth p (n - 1) + 4) := by
    simpa [p, abba, Nat.add_mod] using hmem
  have hle := (Nat.nth_add_one_le_iff hinf (n := n - 1) hnext).2 (by omega)
  change Nat.nth p (n + 1 - 1) - Nat.nth p (n - 1) ≤ 4
  rw [show n + 1 - 1 = n - 1 + 1 by omega]
  omega

end MetaMathlibExt.abs_relativePosition_diff_sub_le
