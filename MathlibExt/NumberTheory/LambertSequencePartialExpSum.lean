/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GoldenRatioLambertSequence

/-!
# Partial exponential sums at the Lambert sequence

Each exponential term up to degree `n - 2` at the lower-branch Lambert value exceeds
the sum of all preceding terms.
-/

namespace MetaMathlibExt

/-- **Partial exponential sums at the Lambert sequence.** Let $n \ge 5$ and $k$ be natural numbers
with $k < n - 2$, let $h(y) = y e^y$ be the Lambert map, and let $a$ be a real number with
$a \ge n - 1$ and
$$h\left(-\frac{a}{n-1}\right) = -\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}.$$
Then
$$\sum_{t=0}^{k} \frac{a^t}{t!} < \frac{a^{k+1}}{(k+1)!}.$$

The two conditions on $a$ say exactly that
$a = -(n-1)\, W_{-1}\left(-\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}\right)$, where $W_{-1}$
is the lower real branch of the Lambert $W$ function; this is the paper's $a(n)$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Lemma 9 (`jis-2024-24.5.7-lem-9`). -/
public theorem sum_pow_div_factorial_lt_lambertSequence (n k : ℕ) (hn : 5 ≤ n)
    (hk : k < n - 2) (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    ∑ t ∈ Finset.range (k + 1), a ^ t / (t.factorial : ℝ) <
      a ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  have ha₀ : 0 ≤ a := by
    have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hbound := two_mul_sub_four_lt_lambertSequence n (by omega) a ha hW
  suffices ∀ j : ℕ, j ≤ n - 2 →
      ∑ t ∈ Finset.range j, a ^ t / (t.factorial : ℝ) < a ^ j / (j.factorial : ℝ) by
    exact this (k + 1) hk
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    have hj' : (j : ℝ) + 1 + 2 ≤ n := by exact_mod_cast (show j + 1 + 2 ≤ n by omega)
    -- The ratio of consecutive terms is a / (j + 1), so the next term at least doubles.
    have hratio : 2 * ((j : ℝ) + 1) ≤ a := by linarith
    rw [Finset.sum_range_succ]
    refine (add_lt_add_left (ih (by omega)) _).trans_le ?_
    rw [← two_mul, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_left hratio (pow_nonneg ha₀ j)]

end MetaMathlibExt
