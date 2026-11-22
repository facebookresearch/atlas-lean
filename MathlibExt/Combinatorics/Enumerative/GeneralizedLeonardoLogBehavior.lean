/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Log-balancedness of reciprocals

For a positive sequence with successive ratios `x n = z (n + 1) / z n`, the reciprocals
are log-balanced exactly when `x n` decreases and `(n + 1) * x n` increases.
-/

namespace MetaMathlibExt

private theorem balanced_iff_ratios (n : ℕ) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) :
    ((1 / b) ^ 2 ≤ (1 / a) * (1 / c) ∧
      (1 / a / n.factorial) * (1 / c / (n + 2).factorial) ≤ (1 / b / (n + 1).factorial) ^ 2) ↔
      c / b ≤ b / a ∧ ↑(n + 1) * (b / a) ≤ ↑(n + 2) * (c / b) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  push_cast
  apply and_congr
  · field_simp
  · field_simp
    ring_nf

/-- **Log-balancedness of reciprocals along a three-term recurrence.** Let $c_1$ and $c_2$ be
real numbers with $c_2 \ge 0$, and let $(z_n)_{n \ge 0}$ be a sequence of positive real numbers
with $z_{n+1} = c_1 z_n - c_2 z_{n-2}$ for every $n \ge 2$. Write $w_n = 1/z_n$ and
$x_n = z_{n+1}/z_n$, and let $n_0 \ge 0$ be an integer. Suppose that for $n = n_0 + 1$ and
$n = n_0 + 2$
$$w_n^2 \le w_{n-1} w_{n+1} \quad \text{and} \quad
\frac{w_{n-1}}{(n-1)!} \cdot \frac{w_{n+1}}{(n+1)!} \le \left(\frac{w_n}{n!}\right)^2,$$
and that $c_1 x_n x_{n+1} \ge 3 c_2$ for every $n \ge n_0$. Then both inequalities hold for
every $n \ge n_0 + 1$; that is, the sequence $(1/z_n)_{n \ge n_0}$ is log-balanced (Došlić).

The paper also assumes $c_1 > 0$; this follows from positivity, the recurrence and $c_2 \ge 0$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Lemma 2
(`integers-2024-A82-lem-2`). -/
public theorem inv_logBalanced_of_recurrence_of_initial (c₁ c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (z : ℕ → ℝ) (hpos : ∀ n, 0 < z n)
    (hrec : ∀ n, 2 ≤ n → z (n + 1) = c₁ * z n - c₂ * z (n - 2)) (n₀ : ℕ)
    (hinit : ∀ n, n₀ + 1 ≤ n → n ≤ n₀ + 2 →
      (1 / z n) ^ 2 ≤ (1 / z (n - 1)) * (1 / z (n + 1)) ∧
        (1 / z (n - 1) / (n - 1).factorial) * (1 / z (n + 1) / (n + 1).factorial) ≤
          (1 / z n / n.factorial) ^ 2)
    (hx : ∀ n, n₀ ≤ n → 3 * c₂ ≤ c₁ * (z (n + 1) / z n) * (z (n + 2) / z (n + 1))) :
    ∀ n, n₀ + 1 ≤ n →
      (1 / z n) ^ 2 ≤ (1 / z (n - 1)) * (1 / z (n + 1)) ∧
        (1 / z (n - 1) / (n - 1).factorial) * (1 / z (n + 1) / (n + 1).factorial) ≤
          (1 / z n / n.factorial) ^ 2 := by
  let x (n : ℕ) := z (n + 1) / z n
  have xpos (n : ℕ) : 0 < x n := div_pos (hpos _) (hpos _)
  have xrec (n : ℕ) : x (n + 2) = c₁ - c₂ / (x n * x (n + 1)) := by
    dsimp [x]
    rw [hrec (n + 2) (by omega), Nat.add_sub_cancel]
    field_simp [ne_of_gt (hpos _)]
  let P (n : ℕ) := x (n + 1) ≤ x n ∧
    ↑(n + 1) * x n ≤ ↑(n + 2) * x (n + 1)
  have init (i : ℕ) (hi : n₀ ≤ i) (hi' : i ≤ n₀ + 1) : P i := by
    exact (balanced_iff_ratios i (hpos i) (hpos (i + 1)) (hpos (i + 2))).mp
      (hinit (i + 1) (by omega) (by omega))
  have step (i : ℕ) (hi : n₀ ≤ i) (h₀ : P i) (h₁ : P (i + 1)) : P (i + 2) := by
    have hca := h₁.1.trans h₀.1
    have hweight := h₀.2.trans h₁.2
    have ha := xpos i
    have hb := xpos (i + 1)
    have hc := xpos (i + 2)
    have hbound := hx (i + 1) (by omega)
    change 3 * c₂ ≤ c₁ * x (i + 1) * x (i + 2) at hbound
    constructor
    · conv_lhs => rw [xrec (i + 1)]
      conv_rhs => rw [xrec i]
      apply sub_le_sub_left
      apply div_le_div_of_nonneg_left hc₂ (mul_pos hb hc)
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hca hb.le
    · -- After clearing denominators, the difference splits into two nonnegative terms.
      change ↑(i + 3) * x (i + 2) ≤ ↑(i + 4) * x (i + 3)
      conv_lhs => rw [xrec i]
      conv_rhs => rw [xrec (i + 1)]
      push_cast at hweight ⊢
      field_simp
      nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hbound),
        mul_nonneg hc₂ (sub_nonneg.mpr hweight)]
  have tail (k : ℕ) : P (n₀ + k) ∧ P (n₀ + k + 1) := by
    induction k with
    | zero => exact ⟨init _ (by omega) (by omega), init _ (by omega) (by omega)⟩
    | succ k ih => exact ⟨ih.2, step (n₀ + k) (by omega) ih.1 ih.2⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_right_comm n₀ 1 k]
  exact (balanced_iff_ratios (n₀ + k) (hpos _) (hpos _) (hpos _)).mpr (tail k).1

end MetaMathlibExt
