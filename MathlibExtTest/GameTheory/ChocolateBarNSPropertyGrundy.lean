/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ChocolateBarNSPropertyGrundy

namespace MathlibExtTest.GameTheory.ChocolateBarNSPropertyGrundy

open MetaMathlibExt

-- The two bounds clamp differently when the width is cut.
example : chocolateBarGrundy ![fun n ↦ n / 2 ^ 1, fun n ↦ n / 2 ^ 2] ![2, 1] 6 = 5 :=
  (hasNSProperty_and_iff_chocolateBarGrundy_eq_xor
    (fun _ _ h ↦ Nat.div_le_div_right h) (fun _ _ h ↦ Nat.div_le_div_right h)).mp
      ⟨hasNSProperty_div_two_pow (by decide), hasNSProperty_div_two_pow (by decide)⟩
      2 1 6 (by decide) (by decide)

-- The identity as the second bound prevents a nim-sum formula at all legal positions.
example : ¬ ∀ x y z : ℕ, x ≤ 2 → y ≤ z →
    chocolateBarGrundy ![fun _ ↦ 2, id] ![x, y] z = x ^^^ y ^^^ z := by
  intro h
  exact not_hasNSProperty_id
    ((hasNSProperty_and_iff_chocolateBarGrundy_eq_xor monotone_const monotone_id).mpr h).2

end MathlibExtTest.GameTheory.ChocolateBarNSPropertyGrundy
