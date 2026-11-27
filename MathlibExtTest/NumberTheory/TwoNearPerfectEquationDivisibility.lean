/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectEquationDivisibility

namespace MetaMathlibExt

example {b k p : ℕ} (hk : 0 < k) (hb : 0 < b) (hp : Odd p)
    (h : ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) = 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p ^ 2 + 1) :
    (p + 1 : ℤ) ∣ 2 ^ b + 2 :=
  succ_dvd_of_two_near_perfect_eq_twelve (b := b) (k := k) (p := p)
    (hk := hk) (hb := hb) (hp := hp) (h := h)

-- At b = 1, k = 2, p = 3, both sides of equation (12) are 91.
example : (3 + 1 : ℤ) ∣ 2 ^ (1 : ℕ) + 2 :=
  succ_dvd_of_two_near_perfect_eq_twelve (b := 1) (k := 2) (p := 3)
    (hk := by decide) (hb := by decide) (hp := ⟨1, by decide⟩) (h := by decide)

end MetaMathlibExt
