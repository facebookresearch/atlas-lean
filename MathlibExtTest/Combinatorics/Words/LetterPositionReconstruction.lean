/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.LetterPositionReconstruction

/-! # Tests for reconstructing the occurrence positions of a binary word -/

namespace MetaMathlibExt.letterPosition_reconstruction

private theorem forall_one {P : ℕ → Prop} : (∀ j, 1 ≤ j → j ≤ 1 → P j) ↔ P 1 :=
  ⟨fun h => h 1 le_rfl le_rfl, fun h _ hj hj' => (le_antisymm hj' hj) ▸ h⟩

-- With offsets 3, 3 (as in aaabb…), the second a fills the gap at 1 before the first b.
example {w : ℕ → Bool} (hw : BothLettersInfinite w)
    (h₁ : relativePosition w 1 = 3) (h₂ : relativePosition w 2 = 3) :
    letterPosition w true 2 = 1 ∧ letterPosition w false 2 = 4 := by
  obtain ⟨pos, _, step⟩ := letterPosition_reconstruction hw
  obtain ⟨ha, hb⟩ := pos (by omega)
  have next := (step 1 le_rfl).1 (by change 0 < relativePosition w 2; omega)
  have least : IsLeast {m : ℕ | (m : ℤ) ≠ 0 ∧ (m : ℤ) ≠ 3} 1 :=
    ⟨by decide, fun m hm => by obtain ⟨h, _⟩ := hm; omega⟩
  simp only [Nat.reduceAdd, forall_one, ha, hb, h₁, least.csInf_eq, h₂] at next
  omega

-- If the first two letters occupy 0 and 1 in either order, an offset of -2 next
-- puts the second b at 2 and the second a at 4 (as in abbba… or babba…).
example {w : ℕ → Bool} (hw : BothLettersInfinite w)
    (h₁ : relativePosition w 1 = 1 ∨ relativePosition w 1 = -1)
    (h₂ : relativePosition w 2 = -2) :
    letterPosition w true 2 = 4 ∧ letterPosition w false 2 = 2 := by
  obtain ⟨pos, neg, step⟩ := letterPosition_reconstruction hw
  have next := (step 1 le_rfl).2 (by change relativePosition w 2 < 0; omega)
  have least : IsLeast {m : ℕ | (m : ℤ) ≠ 0 ∧ (m : ℤ) ≠ 1} 2 :=
    ⟨by decide, fun m hm => by obtain ⟨h, h'⟩ := hm; omega⟩
  rcases h₁ with h | h
  · obtain ⟨ha, hb⟩ := pos (by omega)
    simp only [Nat.reduceAdd, forall_one, ha, hb, h, least.csInf_eq, h₂] at next
    omega
  · obtain ⟨ha, hb⟩ := neg (by omega)
    simp only [Nat.reduceAdd, forall_one, ha, hb, h, neg_neg, and_comm, least.csInf_eq, h₂] at next
    omega

end MetaMathlibExt.letterPosition_reconstruction

namespace MetaMathlibExt

-- The value at index zero is deliberately out of order: only positive indices count.
private def alternatingPositions (offset n : ℕ) : ℕ :=
  if n = 0 then 42 else 2 * (n - 1) + offset

private theorem alternating_conditions (offset : ℕ) :
    (∀ n, 1 ≤ n → alternatingPositions offset n < alternatingPositions offset (n + 1)) ∧
      {n | 1 ≤ n ∧ 1 < (alternatingPositions offset (n + 1) -
        alternatingPositions offset n)}.Infinite := by
  constructor
  · intro n hn
    simp only [alternatingPositions, ite_eq_right (by omega : n ≠ 0),
      ite_eq_right (Nat.add_one_ne_zero n)]
    omega
  · refine (Set.infinite_range_of_injective (f := fun n : ℕ => n + 1)
      (fun _ _ h => Nat.add_right_cancel h)).mono ?_
    rintro _ ⟨n, rfl⟩
    simp [alternatingPositions]
    omega

-- Even positions are allowed for the initial letter, but not for the other letter.
example : (∃ w, BothLettersInfinite w ∧ w 0 = true ∧
    ∀ n, 1 ≤ n → letterPosition w true n = alternatingPositions 0 n) ∧
    ¬(∃ w, BothLettersInfinite w ∧ w 0 = true ∧
      ∀ n, 1 ≤ n → letterPosition w false n = alternatingPositions 0 n) := by
  obtain ⟨hmono, hgap⟩ := alternating_conditions 0
  have h := exists_word_letterPosition_eq_iff (alternatingPositions 0)
  exact ⟨h.1.mpr ⟨hmono, rfl, hgap⟩,
    fun hw => by simpa [alternatingPositions] using (h.2.mp hw).2.1⟩

-- Odd positions are allowed for the other letter, but not for the initial letter.
example : (∃ w, BothLettersInfinite w ∧ w 0 = true ∧
    ∀ n, 1 ≤ n → letterPosition w false n = alternatingPositions 1 n) ∧
    ¬(∃ w, BothLettersInfinite w ∧ w 0 = true ∧
      ∀ n, 1 ≤ n → letterPosition w true n = alternatingPositions 1 n) := by
  obtain ⟨hmono, hgap⟩ := alternating_conditions 1
  have h := exists_word_letterPosition_eq_iff (alternatingPositions 1)
  exact ⟨h.2.mpr ⟨hmono, by decide, hgap⟩,
    fun hw => by simpa [alternatingPositions] using (h.1.mp hw).2.1⟩

-- The strictly increasing sequence 0, 2, 3, … starts correctly but has only one large gap.
example : ¬∃ w, BothLettersInfinite w ∧ w 0 = true ∧
    ∀ n, 1 ≤ n → letterPosition w true n = (if n = 1 then 0 else n) := by
  intro hw
  have h := ((exists_word_letterPosition_eq_iff (fun n => if n = 1 then 0 else n)).1.mp hw).2.2
  apply h ((Set.finite_singleton 1).subset ?_)
  intro n hn
  rcases hn with ⟨hn, hgap⟩
  change n = 1
  by_contra hne
  have hnext : n + 1 ≠ 1 := by omega
  rw [ite_eq_right hnext, ite_eq_right hne, Nat.add_sub_cancel_left] at hgap
  exact (lt_irrefl 1) hgap

end MetaMathlibExt
