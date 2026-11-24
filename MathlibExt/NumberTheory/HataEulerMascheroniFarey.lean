/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring

/-!
# Mediant telescoping for Farey intervals

The value on a Farey interval minus the values on its two mediant subintervals is
the reciprocal of the product of the three numerators and the three denominators.
-/

namespace MetaMathlibExt

/-- **Mediant telescoping identity for Farey intervals.** For an interval $[x/y, z/w]$ write
$f([x/y, z/w]) = (xw + yz)/(xyzw)$. Let $a, b, c, d$ be natural numbers with $a > 0$, $d > 0$
and $bc = ad + 1$. Then, computing in the real numbers, the value of $f$ on $[a/b, c/d]$ minus
its values on the two halves $[a/b, (a + c)/(b + d)]$ and $[(a + c)/(b + d), c/d]$ cut at the
mediant equals
$$
\frac{(bc - ad)^2}{abcd(a + c)(b + d)} = \frac{1}{abcd(a + c)(b + d)}.
$$

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Lemma 1. -/
public theorem farey_interval_mediant_telescoping {a b c d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hF : b * c = a * d + 1) :
    ((a * d + b * c : ℝ) / (a * b * c * d) -
          (a * (b + d) + b * (a + c)) / (a * b * (a + c) * (b + d)) -
          ((a + c) * d + (b + d) * c) / ((a + c) * (b + d) * c * d) =
        ((b * c : ℝ) - a * d) ^ 2 / (a * b * c * d * (a + c) * (b + d))) ∧
      ((b * c : ℝ) - a * d) ^ 2 / (a * b * c * d * (a + c) * (b + d)) =
        1 / (a * b * c * d * (a + c) * (b + d)) := by
  constructor
  · have hbc : 0 < b * c := hF ▸ Nat.succ_pos _
    have hb := Nat.pos_of_mul_pos_right hbc
    have hc := Nat.pos_of_mul_pos_left hbc
    field_simp
    ring
  · have hF' : (b * c : ℝ) = a * d + 1 := by exact_mod_cast hF
    rw [hF', add_sub_cancel_left, one_pow]

end MetaMathlibExt
