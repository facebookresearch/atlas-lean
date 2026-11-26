/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Union
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring

/-!
# Farey interval identities and bounds for Hata's formula

The value on a Farey interval minus the values on its two mediant subintervals is
the reciprocal of the product of the three numerators and the three denominators.
Every Farey interval in $[0,1]$ with positive left endpoint lies between consecutive
reciprocals of positive integers. Every interval in Stern-Brocot generation $n$ has
length at most $1/(n+1)$.
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

/-- **Stern-Brocot generations.** The $n$-th Stern-Brocot generation $F_n$ is a finite set of
intervals $[a/b, c/d]$, each stored as the quadruple $(a, b, c, d)$ of natural numbers. It is
defined by $F_0 = \{[0/1, 1/1]\}$, and $F_{n+1}$ is obtained by replacing each
$[a/b, c/d] \in F_n$ with its two mediant halves $[a/b, (a + c)/(b + d)]$ and
$[(a + c)/(b + d), c/d]$.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Section 2 (before Corollary 1). -/
@[expose] public def fareyGeneration : ℕ → Finset (ℕ × ℕ × ℕ × ℕ)
  | 0 => {(0, 1, 1, 1)}
  | n + 1 => (fareyGeneration n).biUnion fun q =>
      {(q.1, q.2.1, q.1 + q.2.2.1, q.2.1 + q.2.2.2),
        (q.1 + q.2.2.1, q.2.1 + q.2.2.2, q.2.2.1, q.2.2.2)}

/-- **The first two Stern-Brocot generations.** Writing $[a/b, c/d]$ for the quadruple
$(a, b, c, d)$, the first two Stern-Brocot generations are $F_1 = \{[0/1, 1/2], [1/2, 1/1]\}$
and $F_2 = \{[0/1, 1/3], [1/3, 1/2], [1/2, 2/3], [2/3, 1/1]\}$.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Section 2 (before Corollary 1). -/
public theorem fareyGeneration_one_two :
    fareyGeneration 1 = {(0, 1, 1, 2), (1, 2, 1, 1)} ∧
      fareyGeneration 2 = {(0, 1, 1, 3), (1, 3, 1, 2), (1, 2, 2, 3), (2, 3, 1, 1)} := by
  decide

/-- **Recurrence for the Stern-Brocot generations.** For every natural number $n$, the
generation $F_{n+1}$ is the union, over all intervals $[a/b, c/d] \in F_n$, of the two mediant
halves $[a/b, (a + c)/(b + d)]$ and $[(a + c)/(b + d), c/d]$, where each interval $[x/y, z/w]$
is stored as the quadruple $(x, y, z, w)$.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Section 2 (before Corollary 1). -/
public theorem fareyGeneration_succ (n : ℕ) :
    fareyGeneration (n + 1) = (fareyGeneration n).biUnion fun q =>
      {(q.1, q.2.1, q.1 + q.2.2.1, q.2.1 + q.2.2.2),
        (q.1 + q.2.2.1, q.2.1 + q.2.2.2, q.2.2.1, q.2.2.2)} :=
  rfl

private theorem fareyGeneration_length_le.invariants {n a b c d : ℕ}
    (hq : (a, b, c, d) ∈ fareyGeneration n) : b * c = a * d + 1 ∧ n + 1 ≤ b * d := by
  induction n generalizing a b c d with
  | zero =>
    simp only [fareyGeneration, Finset.mem_singleton, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
    decide
  | succ n ih =>
    obtain ⟨⟨p, r, s, t⟩, hparent, hchild⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hdet, hprod⟩ := ih hparent
    have hpos : 0 < r * t := (Nat.succ_pos n).trans_le hprod
    have hr := Nat.pos_of_mul_pos_right hpos
    have ht := Nat.pos_of_mul_pos_left hpos
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hchild
    obtain ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ := hchild
    · simp only [Nat.mul_add, Nat.mul_comm b a]
      have := Nat.mul_pos hr hr
      omega
    · simp only [Nat.add_mul, Nat.mul_comm d c]
      have := Nat.mul_pos ht ht
      omega

/-- **Length bound for the Stern-Brocot generations.** For every natural number $n$, every
interval $[a/b, c/d]$ of the $n$-th Stern-Brocot generation $F_n$, that is, every quadruple
$(a, b, c, d) \in F_n$, satisfies $c/d - a/b \le 1/(n + 1)$.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Corollary 1. -/
public theorem fareyGeneration_length_le {n : ℕ} {q : ℕ × ℕ × ℕ × ℕ}
    (hq : q ∈ fareyGeneration n) :
    (q.2.2.1 : ℚ) / q.2.2.2 - q.1 / q.2.1 ≤ 1 / (n + 1) := by
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨hdet, hprod⟩ := fareyGeneration_length_le.invariants hq
  have hpos : 0 < b * d := (Nat.succ_pos n).trans_le hprod
  have hb : (0 : ℚ) < b := by exact_mod_cast Nat.pos_of_mul_pos_right hpos
  have hd : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_mul_pos_left hpos
  have hdet' : (b * c : ℚ) = a * d + 1 := by exact_mod_cast hdet
  change (c : ℚ) / d - a / b ≤ 1 / (n + 1)
  rw [div_sub_div _ _ hd.ne' hb.ne', mul_comm (c : ℚ), mul_comm (d : ℚ) a,
    hdet', add_sub_cancel_left, mul_comm (d : ℚ)]
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hprod)

end MetaMathlibExt
