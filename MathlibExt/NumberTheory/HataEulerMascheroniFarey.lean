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
# Farey interval identities and bounds for Hata's formula

The value on a Farey interval minus the values on its two mediant subintervals is
the reciprocal of the product of the three numerators and the three denominators.
Every Farey interval in $[0,1]$ with positive left endpoint lies between consecutive
reciprocals of positive integers.
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

/-- **Farey intervals lie in reciprocal intervals.** Let $a, b, c, d$ be natural numbers with
$a > 0$, $c \le d$ and $bc = ad + 1$, so that $[a/b, c/d] \subseteq [0, 1]$ is a Farey interval
with positive left endpoint. Then there is a natural number $n \ge 1$ with $1/(n + 1) \le a/b$
and $c/d \le 1/n$, that is, $[a/b, c/d] \subseteq [1/(n + 1), 1/n]$.

The source's set $F \setminus F^*$ is rendered as these intervals: $F^*$ consists of the
intervals $[0/1, 1/n]$, the ones excluded in the source's proof of this corollary.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Corollary 2. -/
public theorem farey_interval_subset_reciprocal_interval {a b c d : ℕ} (ha : 0 < a)
    (hcd : c ≤ d) (hF : b * c = a * d + 1) :
    ∃ n : ℕ, 0 < n ∧ (1 : ℚ) / (n + 1) ≤ a / b ∧ (c : ℚ) / d ≤ 1 / n := by
  have hbc : 0 < b * c := hF ▸ Nat.succ_pos _
  have hb := Nat.pos_of_mul_pos_right hbc
  have hc := Nat.pos_of_mul_pos_left hbc
  have hd := hc.trans_le hcd
  let n := d / c
  have hn : 0 < n := Nat.div_pos hcd hc
  have hleft : b ≤ a * (n + 1) := by
    apply Nat.le_of_mul_le_mul_right _ hc
    calc
      b * c = a * d + 1 := hF
      _ ≤ a * (c * (n + 1)) :=
        Nat.mul_lt_mul_of_pos_left (Nat.lt_mul_div_succ d hc) ha
      _ = a * (n + 1) * c := by ac_rfl
  refine ⟨n, hn, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hb), one_mul]
    exact_mod_cast hleft
  · rw [div_le_div_iff₀ (by exact_mod_cast hd) (by exact_mod_cast hn), one_mul]
    exact_mod_cast Nat.mul_div_le d c

end MetaMathlibExt
