/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
public import MathlibExt.NumberTheory.Harmonic.OddHarmonic

/-!
# Central binomial sums with harmonic numbers

The closed forms for powers one to three follow by induction on the upper summation limit.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Weighted central binomial sum.** For a sequence $a = (a_k)_{k \ge 0}$ of rational numbers
and natural numbers $r$ and $n$, the weighted central binomial sum is the rational number
$$S_r^a(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r a_k,$$
with the convention $0^0 = 1$.

Taking $a_k = 1$, $a_k = O_k$ (the odd harmonic numbers), $a_k = H_k$ and $a_k = H_{2k}$ (the
harmonic numbers) gives the paper's sums $S_r(n)$, $S_r^O(n)$, $S_r^H(n)$ and $S_r^{2H}(n)$.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
equations (1), (8), (9), (10). -/
public def centralBinomPowSum (a : ℕ → ℚ) (r n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), (k.centralBinom : ℚ) / 4 ^ k * (k : ℚ) ^ r * a k

/-- **The weighted central binomial sum at zero.** For every sequence $a$ of rational numbers and
every natural number $r$, the weighted central binomial sum
$S_r^a(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r a_k$ satisfies $S_r^a(0) = 0^r a_0$, with
the convention $0^0 = 1$.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
equations (1), (8)-(10). -/
public theorem centralBinomPowSum_zero (a : ℕ → ℚ) (r : ℕ) :
    centralBinomPowSum a r 0 = (0 : ℚ) ^ r * a 0 := by
  simp [centralBinomPowSum]

/-- **Adding one term to the weighted central binomial sum.** For every sequence $a$ of rational
numbers and all natural numbers $r$ and $n$, the weighted central binomial sum
$S_r^a(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r a_k$ (with $0^0 = 1$) satisfies
$$S_r^a(n+1) = S_r^a(n) + \binom{2n+2}{n+1} 4^{-(n+1)} (n+1)^r a_{n+1}.$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
equations (1), (8)-(10). -/
public theorem centralBinomPowSum_succ (a : ℕ → ℚ) (r n : ℕ) :
    centralBinomPowSum a r (n + 1) =
      centralBinomPowSum a r n +
        ((n + 1).centralBinom : ℚ) / 4 ^ (n + 1) * ((n + 1 : ℕ) : ℚ) ^ r * a (n + 1) := by
  rw [centralBinomPowSum, sum_range_succ]
  rfl

private theorem CentralBinomHarmonicSums.normalizedCentralBinom_succ (n : ℕ) :
    ((n + 1).centralBinom : ℚ) / 4 ^ (n + 1) =
      (n.centralBinom / 4 ^ n : ℚ) * (2 * n + 1) / (2 * (n + 1)) := by
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  have hbin : ((n : ℚ) + 1) * (n + 1).centralBinom =
      2 * (2 * (n : ℚ) + 1) * n.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  rw [pow_succ]
  field_simp
  linear_combination 2 * hbin

open CentralBinomHarmonicSums

/-- **Central binomial sums with harmonic numbers for powers one to three.** For every natural
number $n$, let $H_m = \sum_{i=1}^{m} 1/i$ be the harmonic numbers, $c_n = \binom{2n}{n}/4^n$,
and $S_r^H(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r H_k$. Then
$$S_1^H(n) = \frac{1}{3} (2n+1)\, c_n \Big(n H_n - \frac{2n}{3} + 2\Big) - \frac{2}{3},$$
$$S_2^H(n) = \frac{1}{5} (2n+1)\, c_n \Big(\frac{n}{3} (3n+2) H_n -
\frac{2}{45} (9n^2 - 14n + 15)\Big) + \frac{2}{15},$$
$$S_3^H(n) = \frac{1}{7} (2n+1)\, c_n \Big(\frac{n}{15} (15n^2 + 18n + 2) H_n -
\frac{2}{1575} (225n^3 - 297n^2 + 37n + 105)\Big) + \frac{2}{105}.$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Corollary 2 (`integers-2026-A109-cor-2`). -/
public theorem centralBinomPowSum_harmonic_one_two_three (n : ℕ) :
    centralBinomPowSum harmonic 1 n =
        1 / 3 * (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) *
            (n * harmonic n - 2 * n / 3 + 2) - 2 / 3 ∧
      centralBinomPowSum harmonic 2 n =
        1 / 5 * (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) *
            (n / 3 * (3 * n + 2) * harmonic n - 2 / 45 * (9 * n ^ 2 - 14 * n + 15)) + 2 / 15 ∧
      centralBinomPowSum harmonic 3 n =
        1 / 7 * (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) *
            (n / 15 * (15 * n ^ 2 + 18 * n + 2) * harmonic n -
              2 / 1575 * (225 * n ^ 3 - 297 * n ^ 2 + 37 * n + 105)) + 2 / 105 := by
  induction n with
  | zero => norm_num [centralBinomPowSum_zero]
  | succ n ih =>
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    simp only [centralBinomPowSum_succ, ih₁, ih₂, ih₃, normalizedCentralBinom_succ,
      harmonic_succ, Nat.cast_succ]
    generalize (n.centralBinom / 4 ^ n : ℚ) = c
    refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **Odd harmonic central binomial sums for powers one to three.** For every natural number $n$,
let $O_m = \sum_{i=1}^{m} 1/(2i-1)$ be the odd harmonic numbers, $c_n = \binom{2n}{n}/4^n$, and
$S_r^O(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r O_k$. Then
$$S_1^O(n) = (2n+1)\, c_n \frac{n}{3} \Big(O_{n+1} - \frac{1}{3}\Big),$$
$$S_2^O(n) = (2n+1)\, c_n \frac{n}{15} \Big((3n+2) O_{n+1} - \frac{9n+16}{15}\Big),$$
$$S_3^O(n) = (2n+1)\, c_n \frac{n}{105} \Big((15n^2 + 18n + 2) O_{n+1} -
\frac{225n^2 + 648n + 352}{105}\Big).$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Corollary 1 (`integers-2026-A109-cor-1`). -/
public theorem centralBinomPowSum_oddHarmonic_one_two_three (n : ℕ) :
    centralBinomPowSum oddHarmonic 1 n =
        (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (n / 3) * (oddHarmonic (n + 1) - 1 / 3) ∧
      centralBinomPowSum oddHarmonic 2 n =
        (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (n / 15) *
          ((3 * n + 2) * oddHarmonic (n + 1) - (9 * n + 16) / 15) ∧
      centralBinomPowSum oddHarmonic 3 n =
        (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (n / 105) *
          ((15 * n ^ 2 + 18 * n + 2) * oddHarmonic (n + 1) -
            (225 * n ^ 2 + 648 * n + 352) / 105) := by
  induction n with
  | zero => norm_num [centralBinomPowSum_zero]
  | succ n ih =>
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih
    simp only [centralBinomPowSum_succ, ih₁, ih₂, ih₃, normalizedCentralBinom_succ,
      oddHarmonic_succ (n + 1), Nat.cast_succ]
    generalize (n.centralBinom / 4 ^ n : ℚ) = c
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    have hodd : 2 * ((n : ℚ) + 1) + 1 ≠ 0 := by positivity
    refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

end

end MetaMathlibExt
