/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SierpinskiRieselRepdigitsInfiniteRieselRepunitsModTwoPow64SubOne

/-! # Tests for `MathlibExt.NumberTheory.SierpinskiRieselRepdigitsInfiniteRieselRepunitsModTwoPow64SubOne` -/

namespace MathlibExtTest.NumberTheory.SierpinskiRieselRepdigitsInfiniteRieselRepunitsModTwoPow64SubOne

open MetaMathlibExt

-- The least admissible base satisfies the congruence, so its repunits contain
-- infinitely many Riesel numbers.
example : {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧
    N = repstring 16518444216571 1 0 t ∧ IsRieselNumber N}.Infinite :=
  infinite_riesel_repunits_mod_two_pow_64_sub_one (b := 16518444216571) (by decide)

-- Hence there is a Riesel repunit above any bound; in particular above `10 ^ 6`.
example : ∃ N t : ℕ, 10 ^ 6 < N ∧ 1 ≤ t ∧
    N = repstring 16518444216571 1 0 t ∧ IsRieselNumber N := by
  have hinf := infinite_riesel_repunits_mod_two_pow_64_sub_one (b := 16518444216571)
    (by decide)
  obtain ⟨N, hNmem, hNgt⟩ := hinf.exists_gt (10 ^ 6)
  obtain ⟨t, ht1, hNeq, hR⟩ := hNmem
  exact ⟨N, t, hNgt, ht1, hNeq, hR⟩

end MathlibExtTest.NumberTheory.SierpinskiRieselRepdigitsInfiniteRieselRepunitsModTwoPow64SubOne
