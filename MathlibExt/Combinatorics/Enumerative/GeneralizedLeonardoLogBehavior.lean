/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
For positive integer parameters, the reciprocals of generalized Leonardo numbers are log-balanced
from index three on, and the partial sums are log-concave from index two on. The n-th roots of the
generalized Leonardo numbers are log-balanced starting at any index at least both 9 and
$(1 + \sqrt{64k - 7})/4$.

## References

* Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the Generalized Leonardo
  Numbers*, INTEGERS 24 (2024), Article A82, pp. 1–9, Lemma 2 and Theorem 1. The proof for
  reciprocals uses Zhao's recurrence and propagation lemma, but bounds the product of the
  successive ratios directly from monotonicity rather than using their limit.
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

namespace GenLeonardoLogBehavior

private noncomputable def L (k i : ℕ) : ℝ := genLeonardo k i

private theorem rec (k i : ℕ) : L k (i + 2) = L k (i + 1) + L k i + k := by
  simp only [L, genLeonardo, Int.cast_add, Int.cast_natCast]

private theorem pos (k i : ℕ) : 0 < L k i := by
  induction i using Nat.twoStepInduction with
  | zero | one => norm_num [L, genLeonardo]
  | more i ha hb => rw [rec]; positivity

private theorem increasing (k i : ℕ) : L k i ≤ L k (i + 1) := by
  cases i with
  | zero => rfl
  | succ i => rw [rec]; linarith [pos k i, Nat.cast_nonneg (α := ℝ) k]

private noncomputable def gap (k i : ℕ) := L k (i + 1) ^ 2 - L k i * L k (i + 2)

private theorem gap_step (k i : ℕ) :
    gap k (i + 2) = gap k i + k * (L k (i + 1) - L k i) := by
  simp only [gap, rec k (i + 2), rec k (i + 1), rec k i]
  ring

-- Two steps increase both the gap and twice the gap minus its successor.
private theorem gaps (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : 9 ≤ i) :
    0 ≤ gap k i ∧ gap k (i + 1) ≤ 2 * gap k i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 9 := ⟨i - 9, by omega⟩
  clear hi
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  induction j using Nat.twoStepInduction with
  | zero | one =>
    constructor <;> norm_num [gap, L, genLeonardo] <;> nlinarith [sq_nonneg (k : ℝ)]
  | more j ha _ =>
    have h := increasing k (j + 7)
    have hgain : L k (j + 9 + 2) - L k (j + 9 + 1) ≤
        2 * (L k (j + 9 + 1) - L k (j + 9)) := by
      linarith only [rec k (j + 9), rec k (j + 8), rec k (j + 7), h]
    rw [show j + 2 + 9 = j + 9 + 2 by omega, gap_step, gap_step k (j + 9 + 1)]
    constructor
    · exact add_nonneg ha.1 (mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr (increasing _ _)))
    · linarith [mul_le_mul_of_nonneg_left hgain (Nat.cast_nonneg (α := ℝ) k), ha.2]

private noncomputable def t (k i : ℕ) := Real.log (L k i)

-- The logarithms have nonpositive second difference and nonnegative third difference.
private theorem log_differences (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : 9 ≤ i) :
    t k i + t k (i + 2) ≤ 2 * t k (i + 1) ∧
      t k i + 3 * t k (i + 2) ≤ 3 * t k (i + 1) + t k (i + 3) := by
  obtain ⟨hg, hgg⟩ := gaps k hk i hi
  have hratio : 3 * L k (i + 1) ≤ 2 * L k (i + 2) := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    linarith [rec k j, rec k (j + 1), increasing k j, Nat.cast_nonneg (α := ℝ) k]
  have hs : 2 * L k (i + 1) ^ 2 ≤ L k (i + 2) ^ 2 := by
    nlinarith only [sq_nonneg (L k (i + 1)), mul_nonneg (sub_nonneg.mpr hratio)
      (show 0 ≤ 2 * L k (i + 2) + 3 * L k (i + 1) by linarith [pos k (i + 1), pos k (i + 2)])]
  have hp : L k i * L k (i + 2) ^ 3 ≤ L k (i + 1) ^ 3 * L k (i + 3) := by
    have h₁ := mul_le_mul_of_nonneg_right hgg (sq_nonneg (L k (i + 1)))
    have h₂ := mul_le_mul_of_nonneg_left hs hg
    dsimp only [gap] at h₁ h₂
    linarith only [h₁, h₂]
  have hlog₂ := Real.log_le_log (mul_pos (pos k i) (pos k (i + 2))) (sub_nonneg.mp hg)
  have hlog₃ := Real.log_le_log (mul_pos (pos k i) (pow_pos (pos k _) 3)) hp
  simp only [Real.log_mul (pos k _).ne' (pos k _).ne', Real.log_mul (pos k _).ne'
    (pow_pos (pos k _) 3).ne', Real.log_mul (pow_pos (pos k _) 3).ne' (pos k _).ne',
    Real.log_pow, Nat.cast_ofNat] at hlog₂ hlog₃
  exact ⟨hlog₂, hlog₃⟩

-- Clear the three denominators in the second difference of log(Lᵢ)/i.
private noncomputable def curvature (k i : ℕ) : ℝ :=
  (i + 1 : ℝ) * (i + 2) * t k i - 2 * i * (i + 2) * t k (i + 1) +
    i * (i + 1) * t k (i + 2)

private theorem initial (k : ℕ) (hk : 1 ≤ k) : 0 ≤ curvature k 9 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h₉ : L k 9 = 54 * k + 55 := by norm_num [L, genLeonardo]; ring
  have h₁₀ : L k 10 = 88 * k + 89 := by norm_num [L, genLeonardo]; ring
  have h₁₁ : L k 11 = 143 * k + 144 := by norm_num [L, genLeonardo]; ring
  -- Bound the two successive ratios so that the base case reduces to rational arithmetic.
  have ha : Real.log 109 ≤ t k 9 := Real.log_le_log (by norm_num) (by rw [h₉]; linarith)
  have hb : t k 10 - t k 9 ≤ Real.log (44 / 27) := by
    rw [t, t, ← Real.log_div (pos k _).ne' (pos k _).ne']
    apply Real.log_le_log (div_pos (pos _ _) (pos _ _))
    rw [div_le_div_iff₀ (pos k 9) (by norm_num), h₉, h₁₀]
    linarith
  have hc : Real.log (81 / 50) ≤ t k 11 - t k 10 := by
    rw [t, t, ← Real.log_div (pos k _).ne' (pos k _).ne']
    apply Real.log_le_log (by norm_num)
    rw [div_le_div_iff₀ (by norm_num) (pos k 10), h₁₀, h₁₁]
    linarith
  have h := Real.log_le_log (show 0 < (44 / 27 : ℝ) ^ 108 by positivity)
    (show (44 / 27 : ℝ) ^ 108 ≤ 109 ^ 2 * (81 / 50) ^ 90 by norm_num)
  rw [Real.log_mul (by positivity) (by positivity)] at h
  simp only [Real.log_pow, Nat.cast_ofNat] at h
  norm_num [curvature]
  linarith only [ha, hb, hc, h]

-- Each increment of the cleared second difference is (i + 1)(i + 2) times the third
-- difference of log L.
private theorem curvature_nonneg (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : 9 ≤ i) :
    0 ≤ curvature k i := by
  induction i, hi using Nat.le_induction with
  | base => exact initial k hk
  | succ i hi ih =>
    have h := (log_differences k hk i hi).2
    dsimp only [curvature] at ih ⊢
    push_cast
    linarith only [ih, mul_nonneg (show 0 ≤ ((i : ℝ) + 1) * (i + 2) by positivity)
      (sub_nonneg.mpr h)]

private theorem log_upper (k i : ℕ) : t k i ≤ k + (i : ℝ) := by
  have double (j : ℕ) : L k (j + 1) + k ≤ 2 * (L k j + k) := by
    cases j with
    | zero => norm_num [L, genLeonardo]; linarith [Nat.cast_nonneg (α := ℝ) k]
    | succ j => linarith only [rec k j, increasing k j]
  have bound (j : ℕ) : L k j + k ≤ (1 + k) * 2 ^ j := by
    induction j with
    | zero => norm_num [L, genLeonardo]
    | succ j ih => rw [pow_succ]; linarith only [double j, ih]
  have h := Real.log_le_log (pos k i)
    (show L k i ≤ (1 + k) * 2 ^ i by linarith [bound i, Nat.cast_nonneg (α := ℝ) k])
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
  have h₂ : Real.log 2 ≤ 1 := by
    convert! Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ)) using 1
    norm_num
  change Real.log (L k i) ≤ _
  linarith only [h, Real.log_le_sub_one_of_pos (show 0 < 1 + (k : ℝ) by positivity),
    mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α := ℝ) i)]

private theorem curvature_le (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : 9 ≤ i)
    (hsqrt : (1 + Real.sqrt (64 * k - 7)) / 4 ≤ i) :
    curvature k i ≤ i * (i + 1 : ℝ) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hi' : (9 : ℝ) ≤ i := by exact_mod_cast hi
  have hs := mul_self_le_mul_self (Real.sqrt_nonneg (64 * k - 7))
    (show Real.sqrt (64 * k - 7) ≤ 4 * i - 1 by linarith)
  rw [← sq, Real.sq_sqrt (by linarith)] at hs
  have hbound : 2 * ((k : ℝ) + i) ≤ i * (i + 1 : ℝ) := by
    nlinarith only [hs, sq_nonneg ((i : ℝ) - 2), hi']
  have hinc := Real.log_le_log (pos k i) (increasing k i)
  change t k i ≤ t k (i + 1) at hinc
  -- Monotonicity and log-concavity bound the cleared second difference above by 2 log Lᵢ.
  have hconc := (log_differences k hk i hi).1
  dsimp only [curvature]
  linarith only [hbound, log_upper k i,
    mul_nonneg (show 0 ≤ (i : ℝ) * (i + 1) by positivity) (sub_nonneg.mpr hconc),
    mul_nonneg (Nat.cast_nonneg (α := ℝ) i) (sub_nonneg.mpr hinc)]

private noncomputable def root (k i : ℕ) : ℝ := L k i ^ ((1 : ℝ) / i)

private theorem root_pos (k i : ℕ) : 0 < root k i := Real.rpow_pos_of_pos (pos k i) _

private theorem root_bounds (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : 9 ≤ i)
    (hsqrt : (1 + Real.sqrt (64 * k - 7)) / 4 ≤ i) :
    let d := Real.log (root k i) + Real.log (root k (i + 2)) - 2 * Real.log (root k (i + 1))
    0 ≤ d ∧ d ≤ Real.log (i + 2 : ℝ) - Real.log (i + 1 : ℝ) := by
  intro d
  have hi' : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hr (j : ℕ) : Real.log (root k j) = t k j / j := by
    rw [root, Real.log_rpow (pos k j), t]; ring
  let denom := (i : ℝ) * (i + 1) * (i + 2)
  have hd : 0 < denom := by dsimp [denom]; positivity
  have heq : d * denom = curvature k i := by
    dsimp only [d, denom, curvature]
    rw [hr, hr, hr]
    push_cast
    field_simp
    ring
  constructor
  · exact nonneg_of_mul_nonneg_left (heq ▸ curvature_nonneg k hk i hi) hd
  · calc
      d ≤ 1 / (i + 2 : ℝ) := by
        apply (mul_le_mul_iff_left₀ hd).mp
        rw [heq]
        convert! curvature_le k hk i hi hsqrt using 1
        dsimp [denom]
        field_simp
      _ = 1 - ((i + 2 : ℝ) / (i + 1))⁻¹ := by
        rw [inv_div]
        field_simp
        ring
      _ ≤ Real.log ((i + 2 : ℝ) / (i + 1)) := Real.one_sub_inv_le_log_of_pos (by positivity)
      _ = _ := Real.log_div (by positivity) (by positivity)

end GenLeonardoLogBehavior

open GenLeonardoLogBehavior in
/-- **Log-balancedness of the reciprocals of generalized Leonardo numbers.** Let $k \ge 1$ be an
integer and let $L_{k,n}$ be the generalized Leonardo numbers. Then the sequence
$(1/L_{k,n})_{n \ge 3}$ is log-balanced (Došlić): for every integer $n \ge 4$,
$$\left(\frac{1}{L_{k,n}}\right)^2 \le \frac{1}{L_{k,n-1}} \cdot \frac{1}{L_{k,n+1}}$$
and
$$\frac{1}{L_{k,n-1} \, (n-1)!} \cdot \frac{1}{L_{k,n+1} \, (n+1)!} \le
\left(\frac{1}{L_{k,n} \, n!}\right)^2.$$

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 1
(`integers-2024-A82-thm-1`). -/
public theorem inv_genLeonardo_logBalanced (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 4 ≤ n) :
    (1 / (genLeonardo k n : ℝ)) ^ 2 ≤
        (1 / (genLeonardo k (n - 1) : ℝ)) * (1 / (genLeonardo k (n + 1) : ℝ)) ∧
      (1 / (genLeonardo k (n - 1) : ℝ) / (n - 1).factorial) *
          (1 / (genLeonardo k (n + 1) : ℝ) / (n + 1).factorial) ≤
        (1 / (genLeonardo k n : ℝ) / n.factorial) ^ 2 := by
  apply inv_logBalanced_of_recurrence_of_initial 2 1 (by norm_num) (L k) (pos k) _ 3 _ _ n hn
  · intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    rw [Nat.add_sub_cancel, one_mul]
    linarith only [rec k j, rec k (j + 1)]
  · intro i hlo hhi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    apply (balanced_iff_ratios j (pos k j) (pos k (j + 1)) (pos k (j + 2))).2
    -- In both initial cases the cleared differences have nonnegative coefficients in k - 1.
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rcases (show j = 3 ∨ j = 4 by omega) with rfl | rfl <;>
      constructor <;> norm_num [L, genLeonardo, Int.cast_add, Int.cast_natCast, Nat.cast_add] <;>
      field_simp <;> apply sub_nonneg.mp <;> ring_nf <;> positivity
  · intro i _
    -- The two ratios telescope, and monotonicity gives L (i + 2) ≥ 2 * L i.
    calc
      3 * (1 : ℝ) ≤ 2 * L k (i + 2) / L k i := by
        rw [le_div_iff₀ (pos k i)]
        linarith only [rec k i, increasing k i, (pos k i).le, Nat.cast_nonneg (α := ℝ) k]
      _ = 2 * (L k (i + 1) / L k i) * (L k (i + 2) / L k (i + 1)) := by
        field_simp [(pos k (i + 1)).ne']

open GenLeonardoLogBehavior in
/-- **Log-balancedness of the n-th roots of generalized Leonardo numbers.** Let $k \ge 1$ be an
integer, let $L_{k,n}$ be the generalized Leonardo numbers, and let $n_k$ be an integer with
$n_k \ge 9$ and $n_k \ge (1 + \sqrt{64k - 7})/4$. Then for every integer $n \ge n_k + 1$,
$$\left(L_{k,n}^{1/n}\right)^2 \le L_{k,n-1}^{1/(n-1)} L_{k,n+1}^{1/(n+1)}$$
and
$$\frac{L_{k,n-1}^{1/(n-1)}}{(n-1)!} \cdot \frac{L_{k,n+1}^{1/(n+1)}}{(n+1)!} \le
\left(\frac{L_{k,n}^{1/n}}{n!}\right)^2;$$
that is, the sequence $(L_{k,n}^{1/n})_{n \ge n_k}$ is log-balanced (Došlić): it is log-convex
and its quotient by $n!$ is log-concave.

The paper asserts only that some $n_k \ge \max\{9, (1 + \sqrt{64k - 7})/4\}$ with this property
exists; the statement above gives the threshold its proof establishes (log-concavity of
$L_{k,n}^{1/n}/n!$ once $n \ge (1 + \sqrt{64k - 7})/4$, log-convexity of $L_{k,n}^{1/n}$ from
$n = 9$ on).

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 4
(`integers-2024-A82-thm-4`). -/
public theorem genLeonardo_rpow_inv_logBalanced (k : ℕ) (hk : 1 ≤ k) (nk : ℕ)
    (h9 : 9 ≤ nk) (hsqrt : (1 + Real.sqrt (64 * k - 7)) / 4 ≤ nk) :
    ∀ n : ℕ, nk + 1 ≤ n →
      ((genLeonardo k n : ℝ) ^ ((1 : ℝ) / n)) ^ 2 ≤
          (genLeonardo k (n - 1) : ℝ) ^ ((1 : ℝ) / (n - 1 : ℕ)) *
            (genLeonardo k (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1 : ℕ)) ∧
        (genLeonardo k (n - 1) : ℝ) ^ ((1 : ℝ) / (n - 1 : ℕ)) / (n - 1).factorial *
            ((genLeonardo k (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1 : ℕ)) / (n + 1).factorial) ≤
          ((genLeonardo k n : ℝ) ^ ((1 : ℝ) / n) / n.factorial) ^ 2 := by
  intro n hn
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have hnk : nk ≤ i := by omega
  obtain ⟨hlo, hhi⟩ := root_bounds k hk i (h9.trans hnk) (hsqrt.trans (by exact_mod_cast hnk))
  change root k (i + 1) ^ 2 ≤ root k i * root k (i + 2) ∧
    root k i / i.factorial * (root k (i + 2) / (i + 2).factorial) ≤
      (root k (i + 1) / (i + 1).factorial) ^ 2
  have hf (j : ℕ) : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  have hfac (j : ℕ) : Real.log ((j + 1).factorial : ℝ) =
      Real.log (j + 1 : ℝ) + Real.log (j.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, Real.log_mul (by positivity) (hf j).ne']
  constructor
  · apply (Real.log_le_log_iff (pow_pos (root_pos _ _) _)
      (mul_pos (root_pos _ _) (root_pos _ _))).mp
    rw [Real.log_pow, Real.log_mul (root_pos _ _).ne' (root_pos _ _).ne']
    push_cast
    linarith only [hlo]
  · have hpos (j : ℕ) := div_pos (root_pos k j) (hf j)
    apply (Real.log_le_log_iff (mul_pos (hpos _) (hpos _)) (pow_pos (hpos _) _)).mp
    simp only [Real.log_mul (hpos _).ne' (hpos _).ne', Real.log_pow,
      Real.log_div (root_pos k _).ne' (hf _).ne', Nat.cast_ofNat]
    rw [hfac (i + 1), hfac i]
    push_cast
    rw [show (i : ℝ) + 1 + 1 = i + 2 by ring]
    linarith only [hhi]

end MetaMathlibExt
