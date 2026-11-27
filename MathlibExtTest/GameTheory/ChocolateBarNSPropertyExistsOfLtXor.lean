/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtXor

/-! # Tests for the chocolate-bar Mex step

The Mex step specializes to constant and halving functions, including a move that clamps
the coordinate.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 3 (a).
-/

namespace MathlibExtTest.GameTheory.ChocolateBarNSPropertyExistsOfLtXor

open MetaMathlibExt

example {k x z c : ℕ} (hx : x ≤ k) (hc : c < x ^^^ z) :
    (∃ u < x, c = u ^^^ z) ∨ ∃ w < z, c = x ^^^ w := by
  simpa only [min_eq_right hx] using (hasNSProperty_const k).exists_of_lt_xor hx hc

example {x z c : ℕ} (hx : x ≤ z / 2) (hc : c < x ^^^ z) :
    (∃ u < x, c = u ^^^ z) ∨ ∃ w < z, c = min (w / 2) x ^^^ w := by
  exact (hasNSProperty_div_two_pow (m := 1) (by decide)).exists_of_lt_xor hx hc

example : ∃ w < 8, 1 = min (w / 2) 2 ^^^ w := by
  have h := (hasNSProperty_div_two_pow (m := 1) (by decide)).exists_of_lt_xor
    (x := 2) (z := 8) (c := 1) (by decide) (by decide)
  rcases h with ⟨u, hu, he⟩ | h
  · have hu' : u / 2 ^ 3 = 0 := by omega
    have hdiv := Nat.xor_div_two_pow (a := u) (b := 8) (n := 3)
    rw [← he, hu'] at hdiv
    simp at hdiv
  · exact h

end MathlibExtTest.GameTheory.ChocolateBarNSPropertyExistsOfLtXor
