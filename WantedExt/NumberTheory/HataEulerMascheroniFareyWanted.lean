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

/-- Mediant telescoping identity for a Farey interval `[a/b, c/d]` (`b c - a d = 1`): with
`f([x/y, z/w]) = (x w + y z) / (x y z w)`, the value of `f` on the interval minus its values on
the two halves cut at the mediant `(a + c)/(b + d)` equals
`(b c - a d)^2 / (a b c d (a + c)(b + d)) = 1 / (a b c d (a + c)(b + d))`. Natural-number
entries with `0 < a` and `0 < d`, so that every denominator is nonzero.

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

/-- Every Farey interval `[a/b, c/d] ⊆ [0, 1]` (`b c - a d = 1`) with positive left endpoint
lies in some reciprocal interval `[1/(n + 1), 1/n]` with `n ≥ 1`. The set `F \ F*` of the source
is rendered as these intervals: `F*` consists of the intervals `[0/1, 1/n]`, the ones excluded in
the source's proof of this corollary.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Corollary 2. -/
public theorem_wanted farey_interval_subset_reciprocal_interval {a b c d : ℕ} (ha : 0 < a)
    (hcd : c ≤ d) (hF : b * c = a * d + 1) :
    ∃ n : ℕ, 0 < n ∧ (1 : ℚ) / (n + 1) ≤ a / b ∧ (c : ℚ) / d ≤ 1 / n

/-- For `n ≥ 1`, the sum of `1 / (a b c d (a + c)(b + d))` over all Farey intervals
`[a/b, c/d]` (`b c - a d = 1`) contained in `J_n = [1/(n + 1), 1/n]`, including `J_n` itself,
equals `1/n + 1/(n + 1) - 2 log((n + 1)/n)`. Containment is written as `b ≤ (n + 1) a` and
`n c ≤ d`.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Lemma 3. -/
public theorem_wanted hasSum_farey_subintervals_reciprocal_interval {n : ℕ} (hn : 0 < n) :
    HasSum
      (fun q : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ |
          b * c = a * d + 1 ∧ b ≤ (n + 1) * a ∧ n * c ≤ d} =>
        match q.1 with
        | (a, b, c, d) => (1 : ℝ) / (a * b * c * d * (a + c) * (b + d)))
      (1 / n + 1 / (n + 1) - 2 * Real.log ((n + 1) / n))

/-- Hata's formula: Euler's constant equals `1/2 + 1/2 ∑ 1 / (a b c d (a + c)(b + d))`, the sum
over Farey intervals `[a/b, c/d] ⊆ [0, 1]` (`b c - a d = 1`, `c ≤ d`) with positive left endpoint
`0 < a` (the source's `F \ F*`, with `F*` the intervals `[0/1, 1/n]`); the series is summable.

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

/-- The `n`-th Stern-Brocot generation `F_n` of Farey intervals `[a/b, c/d]`, stored as
quadruples `(a, b, c, d)`: `F_0 = {[0/1, 1/1]}` and `F_{n+1}` replaces each `[a/b, c/d] ∈ F_n`
by its two mediant halves `[a/b, (a + c)/(b + d)]` and `[(a + c)/(b + d), c/d]`.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Section 2 (before Corollary 1). -/
public def fareyGeneration : ℕ → Finset (ℕ × ℕ × ℕ × ℕ)
  | 0 => {(0, 1, 1, 1)}
  | n + 1 => (fareyGeneration n).biUnion fun q =>
      {(q.1, q.2.1, q.1 + q.2.2.1, q.2.1 + q.2.2.2),
        (q.1 + q.2.2.1, q.2.1 + q.2.2.2, q.2.2.1, q.2.2.2)}

/-- The first Stern-Brocot generations: `F_1 = {[0/1, 1/2], [1/2, 1/1]}` and
`F_2 = {[0/1, 1/3], [1/3, 1/2], [1/2, 2/3], [2/3, 1/1]}`.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Section 2 (before Corollary 1). -/
public theorem fareyGeneration_one_two :
    fareyGeneration 1 = {(0, 1, 1, 2), (1, 2, 1, 1)} ∧
      fareyGeneration 2 = {(0, 1, 1, 3), (1, 3, 1, 2), (1, 2, 2, 3), (2, 3, 1, 1)} := by
  decide

/-- The recurrence of the Stern-Brocot generations: `F_{n+1}` is the set of mediant halves of
the intervals of `F_n`.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Section 2 (before Corollary 1). -/
public theorem fareyGeneration_succ (n : ℕ) :
    fareyGeneration (n + 1) = (fareyGeneration n).biUnion fun q =>
      {(q.1, q.2.1, q.1 + q.2.2.1, q.2.1 + q.2.2.2),
        (q.1 + q.2.2.1, q.2.1 + q.2.2.2, q.2.2.1, q.2.2.2)} :=
  rfl

/-- Every interval `[a/b, c/d]` of the `n`-th Stern-Brocot generation `F_n` has length
`c/d - a/b` at most `1/(n + 1)`.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Corollary 1. -/
public theorem_wanted fareyGeneration_length_le {n : ℕ} {q : ℕ × ℕ × ℕ × ℕ}
    (hq : q ∈ fareyGeneration n) :
    (q.2.2.1 : ℚ) / q.2.2.2 - q.1 / q.2.1 ≤ 1 / (n + 1)

/-- Riemann-sum bound for Farey partitions: let `[a/b, c/d]` be a Farey interval
(`b c - a d = 1`, `c ≤ d`) with `a > 0`, and let `a/b = a_1/b_1 < ⋯ < a_m/b_m = c/d` be a
partition (`m ≥ 2`) whose consecutive pieces are Farey intervals
(`b_k a_{k+1} - a_k b_{k+1} = 1`). With `f([x/y, z/w]) = (x w + y z)/(x y z w)`,
`|∑_{k=1}^{m-1} f([a_k/b_k, a_{k+1}/b_{k+1}]) - ∫_{a/b}^{c/d} 2/t dt|
  ≤ (c/d - a/b) · (b^2/a^2) · max_k 1/(b_k b_{k+1})`. The maximum is written as any
`δ` bounding every `1/(b_k b_{k+1})` (equivalent, since the maximum is the least such `δ`).

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
