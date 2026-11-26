/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ChocolateBarNSPropertyImageXorEq

/-!
# Tests for nim-sum images of an NS function

These examples transfer image membership and exercise a clamped halving function.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (20).
-/

namespace MathlibExtTest.GameTheory.ChocolateBarNSPropertyImageXorEq

open MetaMathlibExt

example {g : ℕ → ℕ} (hg : HasNSProperty g) {x z w : ℕ}
    (hx : x ≤ g z) (hw : w < z) :
    ∃ v < z, x ^^^ w = min (g v) x ^^^ v := by
  have h : x ^^^ w ∈ {c | ∃ u < z, c = x ^^^ u} := ⟨w, hw, rfl⟩
  rw [hg.image_xor_eq hx] at h
  exact h

example : ∃ w < 4, 0 = min (w / 2) 2 ^^^ w := by
  have hg : HasNSProperty (fun w ↦ w / 2) := by
    simpa only [pow_one] using hasNSProperty_div_two_pow (m := 1) (by decide)
  change (0 : ℕ) ∈ {c | ∃ w < 4, c = min (w / 2) 2 ^^^ w}
  rw [← hg.image_xor_eq (x := 2) (z := 4) (by decide)]
  exact ⟨2, by decide, by decide⟩

example {g : ℕ → ℕ} (hg : HasNSProperty g) {z c : ℕ} (hc : c < z) :
    ∃ w < z, c = min (g w) 0 ^^^ w := by
  have h : c ∈ {d | ∃ w < z, d = (0 : ℕ) ^^^ w} := ⟨c, hc, by simp⟩
  rw [hg.image_xor_eq (Nat.zero_le (g z))] at h
  exact h

end MathlibExtTest.GameTheory.ChocolateBarNSPropertyImageXorEq
