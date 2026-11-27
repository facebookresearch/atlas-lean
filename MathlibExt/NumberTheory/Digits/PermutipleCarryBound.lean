/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.Permutiple

/-!
# Carry bound for permutiples

The column-by-column recurrence bounds each carry by one less than the multiplier, with
truncated subtraction giving the bound zero for multiplier zero.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Carry bound for permutiples.** Let $n$ and $b \ge 2$ be natural numbers, let $\sigma$
be a permutation of $\{0, \dots, k\}$, and let $(d_k, \dots, d_0)_b$ be an
$(n, b, \sigma)$-permutiple, where $(e_k, \dots, e_0)_b$ denotes the base-$b$ numeral
$\sum_{j=0}^{k} e_j b^j$. Let $c_0, c_1, \dots$ be the carries of the multiplication
$n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$. Then for every $0 \le j \le k$ we have
$c_j \le n - 1$ if $n \ge 1$, and $c_j = 0$ if $n = 0$.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Theorem 2
(`integers-2024-A88-thm-2`), quoting Holt's earlier paper; restated as Theorem 2
of Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025),
Article A13 (`integers-2025-A13-thm-2`). -/
public theorem permutipleCarry_le (n b : ℕ) (hb : 2 ≤ b) {k : ℕ} (d : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) (j : Fin (k + 1)) :
    permutipleCarry n b d σ j ≤ n - 1 := by
  suffices hc : ∀ i : ℕ, permutipleCarry n b d σ i ≤ n - 1 from hc j
  by_cases hn : n = 0
  · subst n
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      by_cases hi : i < k + 1 <;> simp [permutipleCarry, hi, Nat.le_zero.mp ih]
  intro i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    by_cases hi : i < k + 1
    · rw [permutipleCarry, dite_eq_left hi]
      apply Nat.le_sub_one_of_lt
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).2
      have hd := hp.1 (σ ⟨i, hi⟩)
      -- Even after adding the incoming carry, the numerator is less than n * b.
      have hmul := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hd)
      rw [Nat.mul_succ] at hmul
      omega
    · rw [permutipleCarry, dite_eq_right hi]
      exact Nat.zero_le _

end

end MetaMathlibExt
