/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Notation

/-!
# Integer divisibility through the gcd
-/

namespace MetaMathlibExt

/-- **Divisibility of a product through the gcd.** Let $a, b, c$ be integers with $a$ and $b$ not
both zero. Then $a$ divides $bc$ if and only if $a / \gcd(a, b)$ divides $c$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 11
(`jis-2026-26.4.6-lem-11`). -/
public theorem int_dvd_mul_iff_div_gcd_dvd (a b c : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    a ∣ b * c ↔ a / (Int.gcd a b : ℤ) ∣ c := by
  have hg : (Int.gcd a b : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr (Int.gcd_pos_iff.mpr h)
  rw [Int.ediv_dvd_iff_dvd_mul (Int.gcd_dvd_left a b) hg, Int.dvd_gcd_mul_iff_dvd_mul]

end MetaMathlibExt
