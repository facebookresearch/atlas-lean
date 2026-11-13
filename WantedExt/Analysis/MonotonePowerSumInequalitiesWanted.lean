/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Fib.Basic

/-!
# Power sum inequalities for monotone sequences

Statements from Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101.

For a finite sequence `x` of positive reals, the paper's power sum is
`S_n^{[p]}(x) = ∑ x_k ^ p` (real exponent), and the weighted power sum is
`S_n^{[p]}(x; w) = ∑ w_k x_k ^ p` with total weight `W = ∑ w_k`; these are the
readings under which the paper's Fibonacci applications display `∑ F_k ^ r` and the
weighted Theorem 4 reduces to Theorem 2 at `w ≡ 1` (`W = n`). A sequence
`x_1 ≤ ⋯ ≤ x_n` with `n ≥ 1` terms is `x : Fin (n + 1) → ℝ`, so `x_n` is
`x (Fin.last n)` and the number of terms is `n + 1`.

Lemma 1 (parts (b), (c), (d), (e), (g)) and Theorem 1, both quoted from the paper's
references, are stated near the end. Not stated (see the source audit table): Lemma 1
part (a) (Mathlib's `Nat.fib_succ_eq_succ_sum`), Lemma 1 parts (f) and (h) (garbled
extraction), and the lower bounds of Theorems 3 and 5, which are false as extracted.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Normalised power sums decrease in the exponent.** Let $n \ge 0$ and let $x_1, \dots, x_n$
be positive real numbers. If $\alpha$ and $\beta$ are real numbers with $0 < \beta < \alpha$, then
$(\sum_{k=1}^{n} x_k^\alpha)^{1/\alpha} \le (\sum_{k=1}^{n} x_k^\beta)^{1/\beta}$.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Proposition 1 (`integers-2026-A101-prop-1`). -/
public theorem_wanted power_sum_rpow_one_div_le {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    {α β : ℝ} (hβ : 0 < β) (hβα : β < α) :
    (∑ i, x i ^ α) ^ (1 / α) ≤ (∑ i, x i ^ β) ^ (1 / β)

/-- **Lower bound for a power sum at the mean exponent.** Let $0 < x_1 \le \dots \le x_N$ be
$N \ge 1$ real numbers, and for real $p$ write $S^{[p]} = \sum_{k=1}^{N} x_k^p$. For all real
$r, s > 0$,
$S^{[r]} S^{[s]} / \max(x_N^{r/2} S^{[s/2]}, x_N^{s/2} S^{[r/2]}) \le S^{[(r+s)/2]}$.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 2 (`integers-2026-A101-thm-2`). -/
public theorem_wanted power_sum_mul_div_max_le {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : Monotone x) (h0 : 0 < x 0) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∑ i, x i ^ r) * (∑ i, x i ^ s) /
        max (x (Fin.last n) ^ (r / 2) * ∑ i, x i ^ (s / 2))
          (x (Fin.last n) ^ (s / 2) * ∑ i, x i ^ (r / 2)) ≤
      ∑ i, x i ^ ((r + s) / 2)

/-- **Power sums under a larger exponent.** Let $x_1, \dots, x_N$ be $N \ge 1$ positive real
numbers, and for real $p$ write $S^{[p]} = \sum_{k=1}^{N} x_k^p$. If $\alpha$ and $\beta$ are
real numbers with $0 < \beta \le \alpha$, then $S^{[\alpha]} \le (S^{[\beta]})^{\alpha/\beta}$.

In the paper $\alpha = (r + s)/2$ with $r, s > 0$ and the sequence is monotone; neither
assumption is needed here.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 2(i) (`integers-2026-A101-thm-2`). -/
public theorem_wanted power_sum_le_rpow_of_le {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) :
    ∑ i, x i ^ α ≤ (∑ i, x i ^ β) ^ (α / β)

/-- **Power mean bound for power sums with a smaller exponent.** Let $x_1, \dots, x_N$ be
$N \ge 1$ positive real numbers, and for real $p$ write $S^{[p]} = \sum_{k=1}^{N} x_k^p$. If
$\alpha$ and $\beta$ are real numbers with $0 < \alpha < \beta$, then
$S^{[\alpha]} \le N (S^{[\beta]} / N)^{\alpha/\beta}$. If moreover $x_k \ge 1$ for every $k$,
then also $N (S^{[\beta]} / N)^{\alpha/\beta} \le S^{[\beta]}$.

In the paper $\alpha = (r + s)/2$ and the sequence is monotone, so the condition $x_k \ge 1$
for every $k$ is the paper's $x_1 \ge 1$.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 2(ii), including (4) (`integers-2026-A101-thm-2`). -/
public theorem_wanted power_sum_le_card_mul_rpow_of_lt {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∑ i, x i ^ α ≤ ((n : ℝ) + 1) * ((∑ i, x i ^ β) / ((n : ℝ) + 1)) ^ (α / β) ∧
      ((∀ i, 1 ≤ x i) →
        ((n : ℝ) + 1) * ((∑ i, x i ^ β) / ((n : ℝ) + 1)) ^ (α / β) ≤ ∑ i, x i ^ β)

/-- **Upper bound for Fibonacci power sums with exponent at least 2.** Let $F_k$ denote the
$k$-th Fibonacci number. For every natural number $n \ge 1$ and every real $\alpha \ge 2$,
$\sum_{k=1}^{n} F_k^\alpha \le (F_n F_{n+1})^{\alpha/2}$.

In the paper $\alpha = (r + s)/2$.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 3(i) (`integers-2026-A101-thm-3`). -/
public theorem_wanted sum_fib_rpow_le_of_two_le {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 2 ≤ α) :
    ∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ α ≤
      ((Nat.fib n : ℝ) * Nat.fib (n + 1)) ^ (α / 2)

/-- **Upper bounds for Fibonacci power sums with exponent below 2.** Let $F_k$ denote the $k$-th
Fibonacci number. For every natural number $n \ge 1$ and every real $\alpha$ with
$0 < \alpha < 2$,
$\sum_{k=1}^{n} F_k^\alpha \le n (F_n F_{n+1} / n)^{\alpha/2} \le F_n F_{n+1}$.

In the paper $\alpha = (r + s)/2$.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 3(ii) (`integers-2026-A101-thm-3`). -/
public theorem_wanted sum_fib_rpow_le_card_mul_rpow {n : ℕ} (hn : 1 ≤ n) {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) :
    ∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ α ≤
        (n : ℝ) * ((Nat.fib n : ℝ) * Nat.fib (n + 1) / n) ^ (α / 2) ∧
      (n : ℝ) * ((Nat.fib n : ℝ) * Nat.fib (n + 1) / n) ^ (α / 2) ≤
        (Nat.fib n : ℝ) * Nat.fib (n + 1)

/-- **Lower bound for a weighted power sum at the mean exponent.** Let
$0 < x_1 \le \dots \le x_N$ be $N \ge 1$ real numbers and $w_1, \dots, w_N$ positive real
weights, and for real $p$ write $S^{[p]} = \sum_{k=1}^{N} w_k x_k^p$. For all real $r, s > 0$,
$S^{[r]} S^{[s]} / \max(x_N^{r/2} S^{[s/2]}, x_N^{s/2} S^{[r/2]}) \le S^{[(r+s)/2]}$.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 4 (`integers-2026-A101-thm-4`). -/
public theorem_wanted weighted_power_sum_mul_div_max_le {n : ℕ} (x w : Fin (n + 1) → ℝ)
    (hx : Monotone x) (h0 : 0 < x 0) (hw : ∀ i, 0 < w i) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) :
    (∑ i, w i * x i ^ r) * (∑ i, w i * x i ^ s) /
        max (x (Fin.last n) ^ (r / 2) * ∑ i, w i * x i ^ (s / 2))
          (x (Fin.last n) ^ (s / 2) * ∑ i, w i * x i ^ (r / 2)) ≤
      ∑ i, w i * x i ^ ((r + s) / 2)

/-- **Weighted power mean bound for power sums with a smaller exponent.** Let
$x_1, \dots, x_N$ be $N \ge 1$ positive real numbers and $w_1, \dots, w_N$ positive real
weights, write $W = \sum_{k=1}^{N} w_k$, and for real $p$ write
$S^{[p]} = \sum_{k=1}^{N} w_k x_k^p$. If $\alpha$ and $\beta$ are real numbers with
$0 < \alpha < \beta$, then $S^{[\alpha]} \le W (S^{[\beta]} / W)^{\alpha/\beta}$. If moreover
$x_k \ge 1$ for every $k$, then also $W (S^{[\beta]} / W)^{\alpha/\beta} \le S^{[\beta]}$.

In the paper $\alpha = (r + s)/2$ and the sequence is monotone.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 4(ii) (`integers-2026-A101-thm-4`). -/
public theorem_wanted weighted_power_sum_le_mul_rpow_of_lt {n : ℕ} (x w : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (hw : ∀ i, 0 < w i) {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∑ i, w i * x i ^ α ≤ (∑ i, w i) * ((∑ i, w i * x i ^ β) / ∑ i, w i) ^ (α / β) ∧
      ((∀ i, 1 ≤ x i) →
        (∑ i, w i) * ((∑ i, w i * x i ^ β) / ∑ i, w i) ^ (α / β) ≤ ∑ i, w i * x i ^ β)

/-- **Weighted power-mean bounds for Fibonacci numbers.** Let $F_k$ be the $k$-th Fibonacci
number ($F_1 = F_2 = 1$), let $n \ge 1$, let $w_1, \dots, w_n$ be positive reals with sum
$W = \sum_{k=1}^n w_k$, and let $\alpha$ be a real number with $0 < \alpha < 2$. Then
$$
\sum_{k=1}^n w_k F_k^{\alpha} \le
W \left( \frac{\sum_{k=1}^n w_k F_k^2}{W} \right)^{\alpha/2} \le \sum_{k=1}^n w_k F_k^2.
$$

In the source the exponent is $\alpha = (r + s)/2$.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 5(ii) (`integers-2026-A101-thm-5`). -/
public theorem_wanted weighted_sum_fib_rpow_le_mul_rpow {n : ℕ} (hn : 1 ≤ n) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Finset.Icc 1 n, 0 < w k) {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    ∑ k ∈ Finset.Icc 1 n, w k * (Nat.fib k : ℝ) ^ α ≤
        (∑ k ∈ Finset.Icc 1 n, w k) *
          ((∑ k ∈ Finset.Icc 1 n, w k * (Nat.fib k : ℝ) ^ (2 : ℝ)) /
            ∑ k ∈ Finset.Icc 1 n, w k) ^ (α / 2) ∧
      (∑ k ∈ Finset.Icc 1 n, w k) *
          ((∑ k ∈ Finset.Icc 1 n, w k * (Nat.fib k : ℝ) ^ (2 : ℝ)) /
            ∑ k ∈ Finset.Icc 1 n, w k) ^ (α / 2) ≤
        ∑ k ∈ Finset.Icc 1 n, w k * (Nat.fib k : ℝ) ^ (2 : ℝ)

/-- **Classical Fibonacci sum identities.** Let $F_k$ denote the $k$-th Fibonacci number, with
$F_0 = 0$ and $F_1 = 1$. For every natural number $n \ge 1$, the following identities hold in
the integers: $\sum_{i=1}^{n} F_{2i-1} = F_{2n}$; $\sum_{i=1}^{n} F_{2i} = F_{2n+1} - 1$;
$\sum_{i=1}^{n} i F_i = n F_{n+2} - F_{n+3} + 2$;
$\sum_{i=1}^{n} F_i F_{3i} = F_n F_{n+1} F_{2n+1}$; and
$\sum_{i=1}^{n} \binom{n}{i} F_i = F_{2n}$.

These are parts (b), (c), (d), (e) and (g) of Lemma 1 of the paper, quoted there from Koshy.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Lemma 1 (`integers-2026-A101-lem-1`). -/
public theorem_wanted fib_power_sum_identities {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n, (Nat.fib (2 * i - 1) : ℤ)) = Nat.fib (2 * n) ∧
    (∑ i ∈ Finset.Icc 1 n, (Nat.fib (2 * i) : ℤ)) = Nat.fib (2 * n + 1) - 1 ∧
    (∑ i ∈ Finset.Icc 1 n, (i : ℤ) * Nat.fib i) =
      n * Nat.fib (n + 2) - Nat.fib (n + 3) + 2 ∧
    (∑ i ∈ Finset.Icc 1 n, (Nat.fib i : ℤ) * Nat.fib (3 * i)) =
      Nat.fib n * Nat.fib (n + 1) * Nat.fib (2 * n + 1) ∧
    (∑ i ∈ Finset.Icc 1 n, (n.choose i : ℤ) * Nat.fib i) = Nat.fib (2 * n)

/-- **Product of two Fibonacci power sums.** Let $F_k$ denote the $k$-th Fibonacci number. For
every natural number $n \ge 1$ and all real $r, s$ with $r + s \ge 4$,
$(F_n F_{n+1})^2 \le (\sum_{k=1}^{n} F_k^r)(\sum_{k=1}^{n} F_k^s)$, where $F_k^r$ and $F_k^s$ are
real powers, with equality if and only if $n = 1$, or $n = 2$, or $n \ge 3$ and $r = s = 2$.

The paper quotes this result from its reference [2].

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 1 (`integers-2026-A101-thm-1`). -/
public theorem_wanted sum_fib_rpow_mul_sum_fib_rpow_ge {n : ℕ} (hn : 1 ≤ n) {r s : ℝ}
    (hrs : 4 ≤ r + s) :
    ((Nat.fib n : ℝ) * Nat.fib (n + 1)) ^ 2 ≤
        (∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ r) * ∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ s ∧
      ((∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ r) * ∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ s =
          ((Nat.fib n : ℝ) * Nat.fib (n + 1)) ^ 2 ↔
        n = 1 ∨ n = 2 ∨ (3 ≤ n ∧ r = 2 ∧ s = 2))

end

end MetaMathlibExt
