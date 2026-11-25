/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasDiscriminantGcd

namespace MetaMathlibExt

-- The bound is sharp: the discriminant is 12 and the gcd is 4.
example : Int.gcd 4 ((4 : ℤ) ^ 2 - 4 * 1) = 4 := by decide

example : (Int.gcd 4 12 : ℤ) ∣ 4 :=
  (gcd_p_discr_dvd_four 4 1 (by decide)).1

-- Both signs of an odd divisor are accepted, even when the discriminant is negative.
example : Int.gcd 1 3 = 1 :=
  (gcd_p_discr_dvd_four 1 1 (by decide)).2 3 ⟨1, by decide⟩ (by decide)

example : Int.gcd 1 (-3) = 1 :=
  (gcd_p_discr_dvd_four 1 1 (by decide)).2 (-3) ⟨-2, by decide⟩ (by decide)

example : (Int.gcd 0 (-4) : ℤ) ∣ 4 :=
  (gcd_p_discr_dvd_four 0 1 (by decide)).1

example : (Int.gcd (-1) 1 : ℤ) ∣ 4 :=
  (gcd_p_discr_dvd_four (-1) 0 (by decide)).1

end MetaMathlibExt
