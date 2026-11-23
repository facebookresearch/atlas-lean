/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace MetaMathlibExt

@[expose] public section

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
public theorem_wanted farey_interval_mediant_telescoping {a b c d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hF : b * c = a * d + 1) :
    ((a * d + b * c : ℝ) / (a * b * c * d) -
          (a * (b + d) + b * (a + c)) / (a * b * (a + c) * (b + d)) -
          ((a + c) * d + (b + d) * c) / ((a + c) * (b + d) * c * d) =
        ((b * c : ℝ) - a * d) ^ 2 / (a * b * c * d * (a + c) * (b + d))) ∧
      ((b * c : ℝ) - a * d) ^ 2 / (a * b * c * d * (a + c) * (b + d)) =
        1 / (a * b * c * d * (a + c) * (b + d))

/-- **Farey intervals lie in reciprocal intervals.** Let $a, b, c, d$ be natural numbers with
$a > 0$, $c \le d$ and $bc = ad + 1$, so that $[a/b, c/d] \subseteq [0, 1]$ is a Farey interval
with positive left endpoint. Then there is a natural number $n \ge 1$ with $1/(n + 1) \le a/b$
and $c/d \le 1/n$, that is, $[a/b, c/d] \subseteq [1/(n + 1), 1/n]$.

The source's set $F \setminus F^*$ is rendered as these intervals: $F^*$ consists of the
intervals $[0/1, 1/n]$, the ones excluded in the source's proof of this corollary.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Corollary 2. -/
public theorem_wanted farey_interval_subset_reciprocal_interval {a b c d : ℕ} (ha : 0 < a)
    (hcd : c ≤ d) (hF : b * c = a * d + 1) :
    ∃ n : ℕ, 0 < n ∧ (1 : ℚ) / (n + 1) ≤ a / b ∧ (c : ℚ) / d ≤ 1 / n

/-- **Sum over the Farey intervals inside a reciprocal interval.** Let $n \ge 1$ and
$J_n = [1/(n + 1), 1/n]$. The family $1/(abcd(a + c)(b + d))$, indexed by the quadruples
$(a, b, c, d)$ of natural numbers with $bc = ad + 1$, $b \le (n + 1)a$ and $nc \le d$ (that is,
by the Farey intervals $[a/b, c/d] \subseteq J_n$, including $J_n$ itself), is summable with sum
$$
\frac{1}{n} + \frac{1}{n + 1} - 2 \log \frac{n + 1}{n}.
$$

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Lemma 3. -/
public theorem_wanted hasSum_farey_subintervals_reciprocal_interval {n : ℕ} (hn : 0 < n) :
    HasSum
      (fun q : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ |
          b * c = a * d + 1 ∧ b ≤ (n + 1) * a ∧ n * c ≤ d} =>
        match q.1 with
        | (a, b, c, d) => (1 : ℝ) / (a * b * c * d * (a + c) * (b + d)))
      (1 / n + 1 / (n + 1) - 2 * Real.log ((n + 1) / n))

/-- **Hata's formula for Euler's constant.** Let $S$ be the set of quadruples $(a, b, c, d)$ of
natural numbers with $bc = ad + 1$, $a > 0$ and $c \le d$; these are the Farey intervals
$[a/b, c/d] \subseteq [0, 1]$ with positive left endpoint. The family
$1/(abcd(a + c)(b + d))$, indexed by $(a, b, c, d) \in S$, is summable, and Euler's constant
$\gamma$ satisfies
$$
\gamma = \frac{1}{2} + \frac{1}{2} \sum_{(a, b, c, d) \in S} \frac{1}{abcd(a + c)(b + d)}.
$$

The set $S$ is the source's $F \setminus F^*$, where $F^*$ consists of the intervals $[0/1, 1/n]$.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Theorem 1, attributed there to
Hata. -/
public theorem_wanted euler_mascheroni_eq_hata_farey_sum :
    Summable
        (fun q : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | b * c = a * d + 1 ∧ 0 < a ∧ c ≤ d} =>
          match q.1 with
          | (a, b, c, d) => (1 : ℝ) / (a * b * c * d * (a + c) * (b + d))) ∧
      Real.eulerMascheroniConstant =
        1 / 2 + 1 / 2 * ∑' q : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | b * c = a * d + 1 ∧ 0 < a ∧ c ≤ d},
          match q.1 with
          | (a, b, c, d) => (1 : ℝ) / (a * b * c * d * (a + c) * (b + d))

/-- **Stern-Brocot generations.** The $n$-th Stern-Brocot generation $F_n$ is a finite set of
intervals $[a/b, c/d]$, each stored as the quadruple $(a, b, c, d)$ of natural numbers. It is
defined by $F_0 = \{[0/1, 1/1]\}$, and $F_{n+1}$ is obtained by replacing each
$[a/b, c/d] \in F_n$ with its two mediant halves $[a/b, (a + c)/(b + d)]$ and
$[(a + c)/(b + d), c/d]$.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Section 2 (before Corollary 1). -/
public def fareyGeneration : ℕ → Finset (ℕ × ℕ × ℕ × ℕ)
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

/-- **Length bound for the Stern-Brocot generations.** For every natural number $n$, every
interval $[a/b, c/d]$ of the $n$-th Stern-Brocot generation $F_n$, that is, every quadruple
$(a, b, c, d) \in F_n$, satisfies $c/d - a/b \le 1/(n + 1)$.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Corollary 1. -/
public theorem_wanted fareyGeneration_length_le {n : ℕ} {q : ℕ × ℕ × ℕ × ℕ}
    (hq : q ∈ fareyGeneration n) :
    (q.2.2.1 : ℚ) / q.2.2.2 - q.1 / q.2.1 ≤ 1 / (n + 1)

/-- **Riemann-sum bound for Farey partitions.** Let $a, b, c, d, m$ be natural numbers with
$a > 0$, $bc = ad + 1$, $c \le d$ and $m \ge 2$. Let $A, B : \mathbb{N} \to \mathbb{N}$ satisfy
$A(1) = a$, $B(1) = b$, $A(m) = c$, $B(m) = d$ and $B(k) A(k+1) = A(k) B(k+1) + 1$ for
$1 \le k \le m - 1$, and let $\delta$ be a real number with $1/(B(k) B(k+1)) \le \delta$ for
$1 \le k \le m - 1$. Then
$$
\left| \sum_{k=1}^{m-1} \frac{A(k) B(k+1) + B(k) A(k+1)}{A(k) B(k) A(k+1) B(k+1)} -
\int_{a/b}^{c/d} \frac{2}{t} \, dt \right| \le
\left( \frac{c}{d} - \frac{a}{b} \right) \frac{b^2}{a^2} \, \delta.
$$

In words: the fractions $A(k)/B(k)$ cut the Farey interval $[a/b, c/d]$ into consecutive Farey
intervals, the $k$-th summand is $f([A(k)/B(k), A(k+1)/B(k+1)])$ with
$f([x/y, z/w]) = (xw + yz)/(xyzw)$, and $\delta$ stands for any upper bound of
$\max_k 1/(B(k) B(k+1))$.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Lemma 2, inequality (2). -/
public theorem_wanted abs_sum_farey_partition_sub_integral_le {a b c d m : ℕ} {A B : ℕ → ℕ}
    {δ : ℝ} (ha : 0 < a) (hF : b * c = a * d + 1) (hcd : c ≤ d) (hm : 2 ≤ m)
    (hA1 : A 1 = a) (hB1 : B 1 = b) (hAm : A m = c) (hBm : B m = d)
    (hpart : ∀ k ∈ Finset.Icc 1 (m - 1), B k * A (k + 1) = A k * B (k + 1) + 1)
    (hδ : ∀ k ∈ Finset.Icc 1 (m - 1), (1 : ℝ) / (B k * B (k + 1)) ≤ δ) :
    |∑ k ∈ Finset.Icc 1 (m - 1),
        ((A k * B (k + 1) + B k * A (k + 1) : ℝ) / (A k * B k * A (k + 1) * B (k + 1))) -
      ∫ t in (a / b : ℝ)..(c / d : ℝ), 2 / t| ≤
      ((c : ℝ) / d - a / b) * ((b : ℝ) ^ 2 / a ^ 2) * δ

end

end MetaMathlibExt
