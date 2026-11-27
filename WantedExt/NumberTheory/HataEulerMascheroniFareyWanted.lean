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
public import MathlibExt.NumberTheory.HataEulerMascheroniFarey
public import MathlibExt.NumberTheory.HataEulerMascheroniFareyRiemannSum

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
