/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ChocolateBarNSPropertyImageXorXorEq

/-! # Tests for the nim-sum image identity for two NS functions

Concrete halving functions and a zero-attainment corollary exercise the image identity.
-/

namespace MathlibExtTest.GameTheory.ChocolateBarNSPropertyImageXorXorEq

open MetaMathlibExt

example : ∃ w < 5, 0 = min (w / 2) 2 ^^^ min (w / 4) 1 ^^^ w := by
  have h := HasNSProperty.image_xor_xor_eq
    (hasNSProperty_div_two_pow (m := 1) (by decide))
    (hasNSProperty_div_two_pow (m := 2) (by decide))
    (x := 2) (y := 1) (z := 5) (by decide) (by decide)
  have hmem : 0 ∈ {c : ℕ | ∃ w < 5, c = 2 ^^^ 1 ^^^ w} := ⟨3, by decide, by decide⟩
  rw [h] at hmem
  exact hmem

example {g h : ℕ → ℕ} (hg : HasNSProperty g) (hh : HasNSProperty h)
    {x y z : ℕ} (hx : x ≤ g z) (hy : y ≤ h z) (hxy : x ^^^ y < z) :
    ∃ w < z, 0 = min (g w) x ^^^ min (h w) y ^^^ w := by
  have hmem : 0 ∈ {c | ∃ w < z, c = x ^^^ y ^^^ w} :=
    ⟨x ^^^ y, hxy, (Nat.xor_self _).symm⟩
  rw [hg.image_xor_xor_eq hh hx hy] at hmem
  exact hmem

end MathlibExtTest.GameTheory.ChocolateBarNSPropertyImageXorXorEq
