/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Int.GCD

/-!
# Tests for integer divisibility through the gcd
-/

open MetaMathlibExt

example (c : ℤ) : (-12 : ℤ) ∣ 18 * c ↔ (-2 : ℤ) ∣ c :=
  int_dvd_mul_iff_div_gcd_dvd (-12) 18 c (Or.inl (by decide))

example (c : ℤ) : (0 : ℤ) ∣ (-7) * c ↔ c = 0 :=
  (int_dvd_mul_iff_div_gcd_dvd 0 (-7) c (Or.inr (by decide))).trans Int.zero_dvd

example (c : ℤ) : (-9 : ℤ) ∣ 0 * c ↔ (-1 : ℤ) ∣ c :=
  int_dvd_mul_iff_div_gcd_dvd (-9) 0 c (Or.inl (by decide))
