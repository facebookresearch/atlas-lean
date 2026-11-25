/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.RelativePositionReflection

/-! # Tests for reflection of binary words -/

namespace MetaMathlibExt

private def abba (i : ℕ) : Bool := decide (i % 4 = 0 ∨ i % 4 = 3)

private theorem abba_infinite : BothLettersInfinite abba := by
  constructor <;> apply Set.infinite_of_forall_exists_gt <;> intro n
  · exact ⟨4 * (n + 1), by simp [abba], by omega⟩
  · exact ⟨4 * (n + 1) + 1, by simp [abba, Nat.add_mod], by omega⟩

-- Both image equalities give a preimage; the first letter must be opposite.
example :
    (∃ w : ℕ → Bool, BothLettersInfinite w ∧ w 0 = false ∧ (fun i => !w i) = abba) ∧
    (∃ w : ℕ → Bool, BothLettersInfinite w ∧ w 0 = true ∧
      (fun i => !w i) = (fun i => !abba i)) := by
  have ha : abba ∈ {w | BothLettersInfinite w ∧ w 0 = true} := ⟨abba_infinite, rfl⟩
  have hb : (fun i => !abba i) ∈ {w | BothLettersInfinite w ∧ w 0 = false} := by
    rw [← reflection_image_and_relativePosition.1]
    exact ⟨abba, ha, rfl⟩
  rw [← reflection_image_and_relativePosition.2.1] at ha
  rw [← reflection_image_and_relativePosition.1] at hb
  obtain ⟨u, ⟨hu, hu₀⟩, hueq⟩ := ha
  obtain ⟨v, ⟨hv, hv₀⟩, hveq⟩ := hb
  exact ⟨⟨u, hu, hu₀, hueq⟩, ⟨v, hv, hv₀, hveq⟩⟩

-- In abbaabba…, the first two positions have opposite signs, and both flip.
example : relativePosition (fun i => !abba i) 1 = -1 ∧
    relativePosition (fun i => !abba i) 2 = 1 := by
  have hw : BothLettersInfinite (fun i => !abba i) := by
    have h : (fun i => !abba i) ∈ {w | BothLettersInfinite w ∧ w 0 = false} := by
      rw [← reflection_image_and_relativePosition.1]
      exact ⟨abba, ⟨abba_infinite, rfl⟩, rfl⟩
    exact h.1
  have blocks (i : ℕ) : abba (2 * i) ≠ abba (2 * i + 1) := by
    simp only [abba, ne_eq, decide_eq_decide]
    omega
  have signs := (reflection_image_and_relativePosition.2.2 (fun i => !abba i) abba hw
    abba_infinite).mp (funext fun i => Bool.not_not (abba i))
  exact ⟨(signs 1 (by decide)).trans (by rw [relativePosition_of_dimers blocks 1 (by decide)]; decide),
    (signs 2 (by decide)).trans (by rw [relativePosition_of_dimers blocks 2 (by decide)]; decide)⟩

-- Conversely, sign reversal recovers the complemented word pointwise.
example {w : ℕ → Bool} (hw : BothLettersInfinite w)
    (h : ∀ n, 1 ≤ n → relativePosition abba n = -relativePosition w n) : w 0 = false := by
  have heq := (reflection_image_and_relativePosition.2.2 abba w abba_infinite hw).mpr h
  exact (congrFun heq 0).symm

end MetaMathlibExt
