/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.NumberTheory.GenLeonardo
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Log-convexity, log-concavity and log-balancedness along recurrences

Log-convexity and log-concavity of a positive sequence propagate along a linear recurrence
that subtracts nonnegative multiples of the earlier terms.

For a positive sequence with successive ratios `x n = z (n + 1) / z n`, the reciprocals
are log-balanced exactly when `x n` decreases and `(n + 1) * x n` increases.
For positive integer parameters, the generalized Leonardo partial sums are log-concave from
index two on.
-/

namespace MetaMathlibExt

namespace logConvex_of_linearRecurrence_of_initial_logConvex

-- Scaling the successive ratios by 1 or -1 gives the two directions of propagation.
private theorem propagate (a : ℝ) (k : ℕ) (hk : 2 ≤ k) (c : ℕ → ℝ)
    (hc : ∀ j, 2 ≤ j → j ≤ k → 0 ≤ c j) (z : ℕ → ℝ) (hpos : ∀ n, 0 < z n)
    (hrec : ∀ n, k ≤ n →
      z n = c 1 * z (n - 1) - ∑ j ∈ Finset.Icc 2 k, c j * z (n - j))
    (hinit : ∀ i, 1 ≤ i → i < k → a * z i ^ 2 ≤ a * (z (i - 1) * z (i + 1))) :
    ∀ n, 1 ≤ n → a * z n ^ 2 ≤ a * (z (n - 1) * z (n + 1)) := by
  let x (i : ℕ) := a * z (i + 1) / z i
  have step_iff (i : ℕ) :
      x i ≤ x (i + 1) ↔ a * z (i + 1) ^ 2 ≤ a * (z i * z (i + 2)) := by
    simp [x, div_le_div_iff₀ (hpos _) (hpos _), pow_two, mul_comm, mul_left_comm]
  have ratio_rec (i : ℕ) (hi : k ≤ i) :
      x (i - 1) = a * c 1 - ∑ j ∈ Finset.Icc 2 k, c j * (a * z (i - j) / z (i - 1)) := by
    dsimp [x]
    rw [Nat.sub_add_cancel (Nat.le_of_succ_le (hk.trans hi)), hrec i hi, mul_sub, sub_div,
      ← mul_assoc, mul_div_cancel_right₀ _ (hpos _).ne', Finset.mul_sum, Finset.sum_div]
    simp only [mul_left_comm a, mul_div_assoc]
  -- Compare the current ratio to every earlier one, including each lag in the recurrence.
  have ratios (n : ℕ) : ∀ m ≤ n, x m ≤ x n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have step : x n ≤ x (n + 1) := by
        by_cases hn : n + 1 < k
        · exact (step_iff n).2 (by simpa using hinit (n + 1) (by omega) hn)
        · have h₀ := ratio_rec (n + 1) (by omega)
          have h₁ := ratio_rec (n + 1 + 1) (by omega)
          simp only [Nat.add_sub_cancel] at h₀ h₁
          rw [h₀, h₁]
          apply sub_le_sub_left
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hj₂, hjk⟩ := Finset.mem_Icc.mp hj
          apply mul_le_mul_of_nonneg_left _ (hc j hj₂ hjk)
          apply (div_le_div_iff₀ (hpos (n + 1)) (hpos n)).2
          have h := (div_le_div_iff₀ (hpos (n + 1 - j)) (hpos n)).1
            (ih (n + 1 - j) (by omega))
          rw [show n + 1 + 1 - j = n + 1 - j + 1 by omega]
          simpa only [mul_assoc, mul_comm, mul_left_comm] using h
      intro m hm
      rcases hm.eq_or_lt with rfl | hm
      · exact le_rfl
      · exact (ih m (by omega)).trans step
  rintro (_ | n) hn
  · omega
  · exact (step_iff n).1 (ratios (n + 1) n (by omega))

end logConvex_of_linearRecurrence_of_initial_logConvex

/-- **Log-concavity propagates along a linear recurrence.** Let $k \ge 2$ be an integer, let
$c_1, \dots, c_k$ be real numbers with $c_j \ge 0$ for $2 \le j \le k$, and let
$(z_n)_{n \ge 0}$ be a sequence of positive real numbers with
$$z_n = c_1 z_{n-1} - \sum_{j=2}^{k} c_j z_{n-j} \quad (n \ge k).$$
If $z_{i-1} z_{i+1} \le z_i^2$ for $1 \le i < k$, then $z_{n-1} z_{n+1} \le z_n^2$ for every
$n \ge 1$; that is, the whole sequence is log-concave.

The paper assumes that the block $z_0, \dots, z_{k+1}$ is log-concave, which adds the
inequality for $i = k$, and that $c_1 > 0$. Both follow from the other hypotheses: the
recurrence at $n = k + 1$ propagates the inequality for $i = k$ from those for $i < k$, and
the recurrence at $n = k$ forces $c_1 > 0$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Lemma 1
(quoted from the paper's reference [17]) (`integers-2024-A82-lem-1`). -/
public theorem logConcave_of_linearRecurrence_of_initial_logConcave
    (k : ℕ) (hk : 2 ≤ k) (c : ℕ → ℝ) (hc : ∀ j, 2 ≤ j → j ≤ k → 0 ≤ c j)
    (z : ℕ → ℝ) (hpos : ∀ n, 0 < z n)
    (hrec : ∀ n, k ≤ n →
      z n = c 1 * z (n - 1) - ∑ j ∈ Finset.Icc 2 k, c j * z (n - j))
    (hinit : ∀ i, 1 ≤ i → i < k → z (i - 1) * z (i + 1) ≤ z i ^ 2) :
    ∀ n, 1 ≤ n → z (n - 1) * z (n + 1) ≤ z n ^ 2 := by
  simpa using logConvex_of_linearRecurrence_of_initial_logConvex.propagate (-1) k hk c hc z hpos
    hrec (by simpa using hinit)

/-- **Log-convexity propagates along a linear recurrence.** Let $k \ge 2$ be an integer, let
$c_1, \dots, c_k$ be real numbers with $c_j \ge 0$ for $2 \le j \le k$, and let
$(z_n)_{n \ge 0}$ be a sequence of positive real numbers with
$$z_n = c_1 z_{n-1} - \sum_{j=2}^{k} c_j z_{n-j} \quad (n \ge k).$$
If $z_i^2 \le z_{i-1} z_{i+1}$ for $1 \le i < k$, then $z_n^2 \le z_{n-1} z_{n+1}$ for every
$n \ge 1$; that is, the whole sequence is log-convex.

The paper assumes that the block $z_0, \dots, z_{k+1}$ is log-convex, which adds the
inequality for $i = k$, and that $c_1 > 0$. Both follow from the other hypotheses: the
recurrence propagates the inequality for $i = k$, and the recurrence at $n = k$ forces
$c_1 > 0$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Lemma 1,
log-convex reading (quoted from the paper's reference [17])
(`integers-2024-A82-lem-1`). -/
public theorem logConvex_of_linearRecurrence_of_initial_logConvex
    (k : ℕ) (hk : 2 ≤ k) (c : ℕ → ℝ) (hc : ∀ j, 2 ≤ j → j ≤ k → 0 ≤ c j)
    (z : ℕ → ℝ) (hpos : ∀ n, 0 < z n)
    (hrec : ∀ n, k ≤ n →
      z n = c 1 * z (n - 1) - ∑ j ∈ Finset.Icc 2 k, c j * z (n - j))
    (hinit : ∀ i, 1 ≤ i → i < k → z i ^ 2 ≤ z (i - 1) * z (i + 1)) :
    ∀ n, 1 ≤ n → z n ^ 2 ≤ z (n - 1) * z (n + 1) := by
  simpa using logConvex_of_linearRecurrence_of_initial_logConvex.propagate 1 k hk c hc z hpos
    hrec (by simpa using hinit)

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

/-- **Log-concavity of partial sums of generalized Leonardo numbers.** Let $k \ge 1$ be an
integer, let $L_{k,n}$ be the generalized Leonardo numbers, and let
$R_n = \sum_{i=0}^{n} L_{k,i}$. Then $R_{n-1} R_{n+1} \le R_n^2$ for every integer $n \ge 2$.

The inequality fails at $n = 1$: there $R_0 = 1$, $R_1 = 2$ and $R_2 = k + 4$, so
$R_1^2 - R_0 R_2 = -k < 0$. The paper states it for every $n \ge 1$, although its identity
$R_n^2 - R_{n-1} R_{n+1} = (k+1)^2 (F_n + (-1)^n) + k(k+1)(n F_n - 2 F_{n+1}) + k^2$, with
$F_n$ the Fibonacci numbers, gives the same value $-k$ at $n = 1$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 2
(`integers-2024-A82-thm-2`). -/
public theorem genLeonardo_partialSum_logConcave (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 2 ≤ n) :
    (∑ i ∈ Finset.range n, genLeonardo k i) * (∑ i ∈ Finset.range (n + 2), genLeonardo k i) ≤
      (∑ i ∈ Finset.range (n + 1), genLeonardo k i) ^ 2 := by
  let L := genLeonardo (k : ℤ)
  let S (i : ℕ) := ∑ j ∈ Finset.range i, L j
  have recurrence (i : ℕ) : L (i + 2) = L (i + 1) + L i + k := rfl
  have add_term (i : ℕ) : S (i + 1) = S i + L i := Finset.sum_range_succ ..
  have hk' : 0 < (k : ℤ) := by exact_mod_cast hk
  have nonneg (i : ℕ) : 0 ≤ L i := by
    induction i using Nat.twoStepInduction with
    | zero | one => exact zero_le_one
    | more i h₀ h₁ => rw [recurrence]; omega
  have bound (i : ℕ) : S i ≤ L (i + 1) := by
    induction i with
    | zero => simp [S, L, genLeonardo]
    | succ i ih => rw [add_term, recurrence]; omega
  -- Expand S (i + 1) ^ 2 - S i * S (i + 2) and cancel the square of S i.
  let D (i : ℕ) := L i ^ 2 - S i * (L (i + 1) - L i)
  have step (i : ℕ) : D (i + 2) = D i + (L i + k) * (L (i + 1) + k - S i) := by
    dsimp only [D]
    rw [add_term (i + 1), add_term i, recurrence (i + 1), recurrence i]
    ring
  have gap (i : ℕ) : 0 ≤ D (i + 2) := by
    induction i using Nat.twoStepInduction with
    | zero | one =>
      norm_num [D, S, L, Finset.sum_range_succ, genLeonardo]
      nlinarith [sq_nonneg (k : ℤ)]
    | more i h₀ _ =>
      rw [step (i + 2)]
      have h := bound (i + 2)
      exact add_nonneg h₀ (mul_nonneg (add_nonneg (nonneg _) hk'.le) (by omega))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  change S (m + 2) * S (m + 2 + 2) ≤ S (m + 2 + 1) ^ 2
  rw [add_term (m + 2 + 1), add_term (m + 2)]
  have h := gap m
  dsimp only [D] at h
  nlinarith only [h]

end MetaMathlibExt
