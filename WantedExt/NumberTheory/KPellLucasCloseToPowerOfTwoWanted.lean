/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.Combinatorics.Enumerative.PellLucasNumber

/-!
# `k`-Pell–Lucas numbers close to a power of 2

Statements from Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers
Close to a Power of 2*, INTEGERS 25 (2025), Article A67.

The `k`-generalized Pell–Lucas sequence starts with `k - 2` zeros followed by `Q_0 = Q_1 = 2`,
and `Q_n = 2 Q_{n-1} + Q_{n-2} + ⋯ + Q_{n-k}` for `n ≥ 2`; here it is `kPellLucas k n` for
`n ≥ 0`. Its characteristic polynomial is `Φ_k(x) = x^k - 2x^{k-1} - x^{k-2} - ⋯ - x - 1`, with
one positive real root `α`, and `g_k(z) = (z - 1) / ((k + 1) z² - 3kz + k - 1)`. An integer `a`
is close to `2^m` when `|a - 2^m| < 2^{m/2}`.
-/

namespace MetaMathlibExt

open Real

@[expose] public section

/-- The `k`-generalized Pell–Lucas numbers `Q^{(k)}_n` for `n ≥ 0`: `Q_0 = Q_1 = 2` and
`Q_{n+2} = 2 Q_{n+1} + Q_n + Q_{n-1} + ⋯ + Q_{n+2-k}`, where the terms of negative index (the
`k - 2` initial zeros) are dropped.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Introduction. -/
def kPellLucas (k : ℕ) : ℕ → ℕ
  | 0 => 2
  | 1 => 2
  | n + 2 =>
    2 * kPellLucas k (n + 1) + ∑ j ∈ Finset.range (min (k - 1) (n + 1)), kPellLucas k (n - j)
decreasing_by all_goals omega

/-- `Q^{(k)}_0 = 2`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Introduction. -/
theorem kPellLucas_zero (k : ℕ) : kPellLucas k 0 = 2 := by
  rw [kPellLucas]

/-- `Q^{(k)}_1 = 2`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Introduction. -/
theorem kPellLucas_one (k : ℕ) : kPellLucas k 1 = 2 := by
  rw [kPellLucas]

/-- The recurrence once all `k - 1` earlier terms have nonnegative index: for `k - 2 ≤ n`,
`Q_{n+2} = 2 Q_{n+1} + Q_n + ⋯ + Q_{n+2-k}`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Introduction. -/
theorem kPellLucas_add_two (k n : ℕ) (hn : k - 2 ≤ n) :
    kPellLucas k (n + 2) =
      2 * kPellLucas k (n + 1) + ∑ j ∈ Finset.range (k - 1), kPellLucas k (n - j) := by
  rw [kPellLucas, min_eq_left (by omega)]

/-- For `k = 2` the sequence is the Pell–Lucas sequence `2, 2, 6, 14, 34, …`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Introduction. -/
theorem kPellLucas_two : kPellLucas 2 = pellLucas := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [kPellLucas]; rfl
    | 1 => rw [kPellLucas]; rfl
    | n + 2 =>
      rw [kPellLucas, pellLucas_add_two, ih (n + 1) (by omega), ← ih n (by omega)]
      simp

/-- Small values: `Q^{(3)}_3 = 16` and `Q^{(3)}_6 = 260`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Theorem 1. -/
theorem kPellLucas_three_small : kPellLucas 3 3 = 16 ∧ kPellLucas 3 6 = 260 := by
  constructor <;> simp [kPellLucas, Finset.sum_range_succ]

/-- **Corollary 1.** For `k ≥ 2` and positive `n`, `m`, `Q^{(k)}_n = 2^m` only for
`Q^{(k)}_1 = 2^1` (every `k ≥ 2`) and `Q^{(k)}_3 = 2^4` (`k ≥ 3`).

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Corollary 1 (`integers-2025-A67-cor-1`). -/
public theorem_wanted kPellLucas_eq_two_pow_iff (k n m : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    kPellLucas k n = 2 ^ m ↔ (n = 1 ∧ m = 1) ∨ (n = 3 ∧ m = 4 ∧ 3 ≤ k)

/-- **Lemma 1.** Let `k ≥ 2` and let `α` be the positive real root of
`Φ_k(x) = x^k - 2x^{k-1} - x^{k-2} - ⋯ - 1`. Then (a) `0.276 < g_k(α) < 0.5` and
`|g_k(β)| < 1` for every other complex root `β` of `Φ_k`, and (b) `φ²(1 - φ^{-k}) < α < φ²`,
where `g_k(z) = (z - 1) / ((k + 1) z² - 3kz + k - 1)` and `φ` is the golden ratio.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 1 (`integers-2025-A67-lem-1`). -/
public theorem_wanted kPellLucas_dominantRoot_bounds (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hα : 0 < α)
    (hroot : α ^ k = 2 * α ^ (k - 1) + ∑ i ∈ Finset.range (k - 1), α ^ i) :
    (0.276 < (α - 1) / ((k + 1) * α ^ 2 - 3 * k * α + k - 1) ∧
      (α - 1) / ((k + 1) * α ^ 2 - 3 * k * α + k - 1) < 0.5 ∧
      ∀ β : ℂ, β ^ k = 2 * β ^ (k - 1) + ∑ i ∈ Finset.range (k - 1), β ^ i → β ≠ α →
        ‖(β - 1) / ((k + 1) * β ^ 2 - 3 * k * β + k - 1)‖ < 1) ∧
    goldenRatio ^ 2 * (1 - (goldenRatio ^ k)⁻¹) < α ∧ α < goldenRatio ^ 2

/-- **Lemma 2.** Let `α` be the positive real root of `Φ_k` and `g_k` as in Lemma 1. If
`k ≥ 50` and `1 < n < φ^{k/2}`, then (i) `|(2α - 2) αⁿ - 2φ^{2n+1}| < 4φ^{2n} / φ^{k/2}` and
(ii) `|g_k(α) - g_k(φ²)| < 4k / φ^k`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 2 (`integers-2025-A67-lem-2`). -/
public theorem_wanted kPellLucas_dominantRoot_golden_approx (k n : ℕ) (hk : 50 ≤ k) (hn : 1 < n)
    (hnk : (n : ℝ) < goldenRatio ^ ((k : ℝ) / 2)) (α : ℝ) (hα : 0 < α)
    (hroot : α ^ k = 2 * α ^ (k - 1) + ∑ i ∈ Finset.range (k - 1), α ^ i) :
    |(2 * α - 2) * α ^ n - 2 * goldenRatio ^ (2 * n + 1)| <
        4 * goldenRatio ^ (2 * n) / goldenRatio ^ ((k : ℝ) / 2) ∧
      |(α - 1) / ((k + 1) * α ^ 2 - 3 * k * α + k - 1) -
          (goldenRatio ^ 2 - 1) /
            ((k + 1) * (goldenRatio ^ 2) ^ 2 - 3 * k * goldenRatio ^ 2 + k - 1)| <
        4 * k / goldenRatio ^ k

/-- **Lemma 3.** Let `α` be the positive real root of `Φ_k` and `g_k` as in Lemma 1. If
`k ≥ 50` and `n < φ^{k/2}`, then `(2α - 2) g_k(α) αⁿ = 2φ^{2n+1} / (φ + 2) · (1 + ξ)` with
`|ξ| < 1.25 / φ^{k/2}`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 3 (`integers-2025-A67-lem-3`). -/
public theorem_wanted kPellLucas_dominantRoot_main_term (k n : ℕ) (hk : 50 ≤ k)
    (hnk : (n : ℝ) < goldenRatio ^ ((k : ℝ) / 2)) (α : ℝ) (hα : 0 < α)
    (hroot : α ^ k = 2 * α ^ (k - 1) + ∑ i ∈ Finset.range (k - 1), α ^ i) :
    ∃ ξ : ℝ, (2 * α - 2) * ((α - 1) / ((k + 1) * α ^ 2 - 3 * k * α + k - 1)) * α ^ n =
        2 * goldenRatio ^ (2 * n + 1) / (goldenRatio + 2) * (1 + ξ) ∧
      |ξ| < 1.25 / goldenRatio ^ ((k : ℝ) / 2)

/-- **Lemma 5 (ii).** Let `τ` be irrational with continued fraction `[a₀; a₁, a₂, …]` and
convergent denominators `q₀, q₁, …`, let `M > 0`, let `N` be the least positive integer with
`q_N > M`, and let `a(M) = max {a_k : 0 ≤ k ≤ N}`. Then `|τ - y/x| > 1 / ((a(M) + 2) x²)` for
all integers `x`, `y` with `0 < x < M`. Here `a₀ = ⌊τ⌋` and `a_{j+1}` is the `j`th partial
denominator of `GenContFract.of τ`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 5 (`integers-2025-A67-lem-5`). -/
public theorem_wanted lt_abs_sub_div_of_max_partialQuotient (τ : ℝ) (hτ : Irrational τ) (M : ℝ)
    (hM : 0 < M) (N : ℕ) (hN : 0 < N) (hqN : M < (GenContFract.of τ).dens N)
    (hNmin : ∀ j, 0 < j → j < N → (GenContFract.of τ).dens j ≤ M) (a : ℕ → ℝ)
    (ha₀ : a 0 = (GenContFract.of τ).h)
    (ha : ∀ j, (GenContFract.of τ).partDens.get? j = some (a (j + 1))) (x y : ℤ) (hx : 0 < x)
    (hxM : (x : ℝ) < M) :
    1 / (((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one a + 2) * (x : ℝ) ^ 2) <
      |τ - y / x|

/-- **Lemma 6.** If `0 < a < 1` and `0 < |x| < a`, then
`|log(1 + x)| < (-log(1 - a) / a) · |x|` and `|x| < (a / (1 - e^{-a})) · |eˣ - 1|`. The case
`x = 0`, where both strict inequalities read `0 < 0`, is excluded.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 6 (`integers-2025-A67-lem-6`). -/
public theorem_wanted abs_log_one_add_lt_and_abs_lt_exp_sub_one (a x : ℝ) (ha₀ : 0 < a)
    (ha₁ : a < 1) (hx : |x| < a) (hx₀ : x ≠ 0) :
    |Real.log (1 + x)| < -Real.log (1 - a) / a * |x| ∧
      |x| < a / (1 - Real.exp (-a)) * |Real.exp x - 1|

/-- **Lemma 7.** If `ℓ ≥ 1`, `T > (4ℓ²)^ℓ` and `T > x / (log x)^ℓ`, then
`x < 2^ℓ T (log T)^ℓ`; stated for `x > 1`, where `(log x)^ℓ` is a real power of a positive
number.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 7 (`integers-2025-A67-lem-7`). -/
public theorem_wanted lt_two_rpow_mul_mul_log_rpow (ℓ T x : ℝ) (hℓ : 1 ≤ ℓ) (hx : 1 < x)
    (hT : (4 * ℓ ^ 2) ^ ℓ < T) (hTx : x / Real.log x ^ ℓ < T) :
    x < 2 ^ ℓ * T * Real.log T ^ ℓ

/-- **Lemma 8.** If `|Q^{(k)}_n - 2^m| < 2^{m/2}` with `k ≥ 2`, `n ≥ 1`, `m ≥ 2` and
`n ≥ k + 1`, then `0.69n - 1.69 < m < 1.39n + 3.78`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 8 (`integers-2025-A67-lem-8`). -/
public theorem_wanted kPellLucas_close_two_pow_exponent_bounds (k n m : ℕ) (hk : 2 ≤ k)
    (hn : 1 ≤ n) (hm : 2 ≤ m) (hkn : k + 1 ≤ n)
    (hclose : |(kPellLucas k n : ℝ) - 2 ^ m| < (2 : ℝ) ^ ((m : ℝ) / 2)) :
    (0.69 : ℝ) * n - 1.69 < m ∧ (m : ℝ) < 1.39 * n + 3.78

/-- **Lemma 9.** If `|Q^{(k)}_n - 2^m| < 2^{m/2}` with `k ≥ 2`, positive `n`, `m` and
`n ≥ k + 1`, then `n < 1.7 · 10¹⁵ · k⁴ · log³ k` and `m < 2.37 · 10¹⁵ · k⁴ · log³ k`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 9 (`integers-2025-A67-lem-9`). -/
public theorem_wanted kPellLucas_close_two_pow_lt_bounds (k n m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (hkn : k + 1 ≤ n) (hclose : |(kPellLucas k n : ℝ) - 2 ^ m| < (2 : ℝ) ^ ((m : ℝ) / 2)) :
    (n : ℝ) < 1.7e15 * k ^ 4 * Real.log k ^ 3 ∧ (m : ℝ) < 2.37e15 * k ^ 4 * Real.log k ^ 3

/-- **Lemma 10.** There is no solution of `|Q^{(k)}_n - 2^m| < 2^{m/2}` with `k > 350` and
`n ≥ k + 1`.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 10 (`integers-2025-A67-lem-10`). -/
public theorem_wanted kPellLucas_not_close_two_pow_of_large_order (k n m : ℕ) (hk : 350 < k)
    (hkn : k + 1 ≤ n) : ¬ |(kPellLucas k n : ℝ) - 2 ^ m| < (2 : ℝ) ^ ((m : ℝ) / 2)

end

end MetaMathlibExt
