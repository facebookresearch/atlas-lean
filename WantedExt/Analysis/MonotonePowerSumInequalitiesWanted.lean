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

/-- Power sums of a nonnegative finite sequence are monotone in the exponent after
normalisation: if `α > β > 0` then `(∑ x_k ^ α) ^ (1 / α) ≤ (∑ x_k ^ β) ^ (1 / β)`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Proposition 1 (`integers-2026-A101-prop-1`). -/
public theorem_wanted power_sum_rpow_one_div_le {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    {α β : ℝ} (hβ : 0 < β) (hβα : β < α) :
    (∑ i, x i ^ α) ^ (1 / α) ≤ (∑ i, x i ^ β) ^ (1 / β)

/-- Lower bound of Theorem 2: for `0 < x_1 ≤ ⋯ ≤ x_n`, `r, s > 0` and
`α = (r + s) / 2`,
`S^{[r]} S^{[s]} / max (x_n ^ (r/2) S^{[s/2]}, x_n ^ (s/2) S^{[r/2]}) ≤ S^{[α]}`.
The paper states it in both cases `α ≥ β` and `α < β`; it does not involve `β`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 2 (`integers-2026-A101-thm-2`). -/
public theorem_wanted power_sum_mul_div_max_le {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : Monotone x) (h0 : 0 < x 0) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∑ i, x i ^ r) * (∑ i, x i ^ s) /
        max (x (Fin.last n) ^ (r / 2) * ∑ i, x i ^ (s / 2))
          (x (Fin.last n) ^ (s / 2) * ∑ i, x i ^ (r / 2)) ≤
      ∑ i, x i ^ ((r + s) / 2)

/-- Upper bound of Theorem 2(i): for positive `x_k` and `0 < β ≤ α`,
`S^{[α]} ≤ (S^{[β]}) ^ (α / β)` (in the paper `α = (r + s) / 2` with `r, s > 0`, and
the sequence is monotone; neither is needed here).

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 2(i) (`integers-2026-A101-thm-2`). -/
public theorem_wanted power_sum_le_rpow_of_le {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) {α β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) :
    ∑ i, x i ^ α ≤ (∑ i, x i ^ β) ^ (α / β)

/-- Upper bounds of Theorem 2(ii): for positive `x_k` and `0 < α < β`,
`S^{[α]} ≤ n (S^{[β]} / n) ^ (α / β)`, and if moreover every `x_k ≥ 1` then
`n (S^{[β]} / n) ^ (α / β) ≤ S^{[β]}` (here `n` is the number of terms, `n + 1` in
Lean; in the paper `α = (r + s) / 2` and the sequence is monotone, so `x_k ≥ 1` is the
paper's `x_1 ≥ 1`).

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 2(ii), including (4) (`integers-2026-A101-thm-2`). -/
public theorem_wanted power_sum_le_card_mul_rpow_of_lt {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∑ i, x i ^ α ≤ ((n : ℝ) + 1) * ((∑ i, x i ^ β) / ((n : ℝ) + 1)) ^ (α / β) ∧
      ((∀ i, 1 ≤ x i) →
        ((n : ℝ) + 1) * ((∑ i, x i ^ β) / ((n : ℝ) + 1)) ^ (α / β) ≤ ∑ i, x i ^ β)

/-- Upper bounds of Theorem 3 for Fibonacci numbers, with `α = (r + s) / 2`: if
`α ≥ 2` then `∑_{k=1}^n F_k ^ α ≤ (F_n F_{n+1}) ^ (α / 2)`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 3(i) (`integers-2026-A101-thm-3`). -/
public theorem_wanted sum_fib_rpow_le_of_two_le {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 2 ≤ α) :
    ∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ α ≤
      ((Nat.fib n : ℝ) * Nat.fib (n + 1)) ^ (α / 2)

/-- Upper bounds of Theorem 3(ii) for Fibonacci numbers, with `α = (r + s) / 2`: if
`0 < α < 2` then
`∑_{k=1}^n F_k ^ α ≤ n (F_n F_{n+1} / n) ^ (α / 2) ≤ F_n F_{n+1}`.

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 3(ii) (`integers-2026-A101-thm-3`). -/
public theorem_wanted sum_fib_rpow_le_card_mul_rpow {n : ℕ} (hn : 1 ≤ n) {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) :
    ∑ k ∈ Finset.Icc 1 n, (Nat.fib k : ℝ) ^ α ≤
        (n : ℝ) * ((Nat.fib n : ℝ) * Nat.fib (n + 1) / n) ^ (α / 2) ∧
      (n : ℝ) * ((Nat.fib n : ℝ) * Nat.fib (n + 1) / n) ^ (α / 2) ≤
        (Nat.fib n : ℝ) * Nat.fib (n + 1)

/-- Lower bound (6), (7) of Theorem 4 (weighted): for `0 < x_1 ≤ ⋯ ≤ x_n`, weights
`w_k > 0`, `r, s > 0` and `α = (r + s) / 2`,
`S^{[r]}(x;w) S^{[s]}(x;w) / max (x_n ^ (r/2) S^{[s/2]}(x;w), x_n ^ (s/2) S^{[r/2]}(x;w))
≤ S^{[α]}(x;w)`, where `S^{[p]}(x;w) = ∑ w_k x_k ^ p`.

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

/-- Upper bounds (7), (8) of Theorem 4(ii) (weighted): for positive `x_k`, weights
`w_k > 0` with `W = ∑ w_k` and `0 < α < β`,
`S^{[α]}(x;w) ≤ W (S^{[β]}(x;w) / W) ^ (α / β)`, and if moreover every `x_k ≥ 1` then
`W (S^{[β]}(x;w) / W) ^ (α / β) ≤ S^{[β]}(x;w)` (in the paper `α = (r + s) / 2` and
the sequence is monotone).

Source: Sanja Kovač and Josip Pečarić, *Power Sum Inequalities for Monotone
Sequences with Applications to Fibonacci Numbers*, INTEGERS 26 (2026), Article A101,
Theorem 4(ii) (`integers-2026-A101-thm-4`). -/
public theorem_wanted weighted_power_sum_le_mul_rpow_of_lt {n : ℕ} (x w : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (hw : ∀ i, 0 < w i) {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∑ i, w i * x i ^ α ≤ (∑ i, w i) * ((∑ i, w i * x i ^ β) / ∑ i, w i) ^ (α / β) ∧
      ((∀ i, 1 ≤ x i) →
        (∑ i, w i) * ((∑ i, w i * x i ^ β) / ∑ i, w i) ^ (α / β) ≤ ∑ i, w i * x i ^ β)

/-- Upper bounds of Theorem 5(ii) (weighted Fibonacci), with `α = (r + s) / 2`: for
weights `w_k > 0`, `W = ∑_{k=1}^n w_k` and `0 < α < 2`,
`∑ w_k F_k ^ α ≤ W (∑ w_k F_k ^ 2 / W) ^ (α / 2) ≤ ∑ w_k F_k ^ 2`.

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

/-- Classical Fibonacci sums quoted in Lemma 1 (from Koshy): for `n ≥ 1`,
(b) `∑_{i=1}^n F_{2i-1} = F_{2n}`, (c) `∑_{i=1}^n F_{2i} = F_{2n+1} - 1`,
(d) `∑_{i=1}^n i F_i = n F_{n+2} - F_{n+3} + 2`, (e) `∑_{i=1}^n F_i F_{3i} = F_n F_{n+1} F_{2n+1}`,
(g) `∑_{i=1}^n binom(n,i) F_i = F_{2n}`, over `ℤ`. Part (a), `∑ F_i = F_{n+2} - 1`, is Mathlib's
`Nat.fib_succ_eq_succ_sum` and is not restated; parts (f) and (h) are omitted because their
extracted text is garbled.

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

/-- For real `r, s` with `r + s ≥ 4` and `n ≥ 1`,
`(∑_{k=1}^n F_k^r)(∑_{k=1}^n F_k^s) ≥ (F_n F_{n+1})²`, with equality if and only if `n = 1`,
`n = 2`, or `n ≥ 3` and `r = s = 2`. Quoted in the paper from its reference [2]; powers are
real powers `rpow`.

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
