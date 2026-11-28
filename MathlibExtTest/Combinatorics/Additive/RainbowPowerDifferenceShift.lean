/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.RainbowPowerDifference
import MathlibExt.Combinatorics.Additive.RainbowPowerDifferenceShift

/-! # Tests for shifts of monochromatic strings -/

namespace MathlibExtTest.RainbowPowerDifferenceShift

open MetaMathlibExt

/-- Red on odd residues, blue on `2`, and green on `0` modulo four. -/
private def residueColor (a : ZMod 4) : Fin 3 :=
  if a = 0 then 2 else if a = 2 then 1 else 0

/-- Lift the residue coloring to positive integers and assign red to zero. -/
private def shiftColor (n : ℕ) : Fin 3 :=
  if n = 0 then 0 else residueColor n

private theorem shiftColor_rainbowFree (k : ℕ) (hk : k = 1 ∨ k = 2)
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x = y + z ^ k) :
    ¬ (shiftColor x ≠ shiftColor y ∧ shiftColor y ≠ shiftColor z ∧ shiftColor x ≠ shiftColor z) := by
  have hrf : ∀ a b d : ZMod 4, a - b = d ^ k →
      ¬ (residueColor a ≠ residueColor b ∧ residueColor b ≠ residueColor d ∧
        residueColor a ≠ residueColor d) := by
    rcases hk with rfl | rfl <;> decide
  simpa only [shiftColor, ite_eq_right hx.ne', ite_eq_right hy.ne', ite_eq_right hz.ne'] using
    rainbowFree_powDiff_lift_of_zmod 4 k residueColor hrf x y z hx hy hz h

private theorem shiftColor_dominant (k : ℕ) (hk : k = 1 ∨ k = 2) (s ℓ : ℕ) (hs : 0 < s)
    (hcard : ((Finset.Ico s (s + ℓ)).image shiftColor).card = 2) :
    0 ∈ (Finset.Ico s (s + ℓ)).image shiftColor := by
  have hcolors : ∀ e : Fin 3, ∃ n : Fin 4, shiftColor ((n : ℕ) + 1) = e := by decide
  have hexact (e : Fin 3) : ∃ n : ℕ, 0 < n ∧ shiftColor n = e := by
    obtain ⟨n, hn⟩ := hcolors e
    exact ⟨n + 1, Nat.succ_pos _, hn⟩
  have h := color_one_dominant_of_rainbowFree_powDiff 3 k shiftColor hexact
    (shiftColor_rainbowFree k hk) s ℓ hs hcard
  simpa only [show shiftColor 1 = 0 by decide] using h

-- Directly compute both shifts of the green singleton at 4 by the step 2^1.
example : (Finset.Ico (4 + 2 ^ 1) (4 + 2 ^ 1 + 1)).image shiftColor = {1} ∧
    (Finset.Ico (4 - 2 ^ 1) (4 - 2 ^ 1 + 1)).image shiftColor = {1} := by
  decide

-- The public theorem applies to the same singleton with both shifts in range.
example : (∃ e : Fin 3, (e = 1 ∨ e = 2) ∧ shiftColor 6 = e) ∧
    (∃ e : Fin 3, (e = 1 ∨ e = 2) ∧ shiftColor 2 = e) := by
  have hG (t : ℕ) (ht : t < 1) : shiftColor (4 + t) = 2 := by
    obtain rfl : t = 0 := by omega
    decide
  obtain ⟨⟨e, he, hr⟩, hl⟩ := monochromatic_shift_of_rainbowFree_powDiff 1 shiftColor
    (shiftColor_rainbowFree 1 (Or.inl rfl)) 0 1 2 (by decide) (by decide) (by decide)
    (shiftColor_dominant 1 (Or.inl rfl)) 2 (by decide) (by decide) 4 1 (by decide) hG
  obtain ⟨e', he', hleft⟩ := hl (by decide)
  exact ⟨⟨e, he, hr 0 (by decide)⟩, ⟨e', he', hleft 0 (by decide)⟩⟩

-- Both translated intervals are empty when the length is zero.
example : (Finset.Ico (4 + 2 ^ 1) (4 + 2 ^ 1)).image shiftColor = ∅ ∧
    (Finset.Ico (4 - 2 ^ 1) (4 - 2 ^ 1)).image shiftColor = ∅ := by
  decide

-- For step 2² = 4 the right shift is green, but the left shift lands at zero (red).
-- Replacing the strict positive-start guard by 2² ≤ 4 would permit this red singleton.
example : (Finset.Ico (4 + 2 ^ 2) (4 + 2 ^ 2 + 1)).image shiftColor = {2} ∧
    (Finset.Ico (4 - 2 ^ 2) (4 - 2 ^ 2 + 1)).image shiftColor = {0} := by
  decide

end MathlibExtTest.RainbowPowerDifferenceShift
