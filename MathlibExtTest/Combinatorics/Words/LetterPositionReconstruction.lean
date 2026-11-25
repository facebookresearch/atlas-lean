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
