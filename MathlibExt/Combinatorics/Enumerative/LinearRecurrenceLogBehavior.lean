/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ratio bounds for the A005773 recurrence

Let `A : ℕ → ℝ` satisfy `A 0 = A 1 = 1` and
`(n + 1) A (n + 1) = 2 (n + 1) A n + 3 (n - 1) A (n - 1)` for `n ≥ 1` (OEIS A005773,
`1, 1, 2, 5, 13, 35, …`). With `x n = A (n + 1) / A n` and `φ n = 3 (2n + 1) / (2 (n + 1))`,
Lemma 1 of Zhao's paper states that, for every `n ≥ 0`, `x n ≤ φ n` and
`x (n + 1) / x n ≥ 2 (3n² + 6n + 2) / ((n + 2)(2n + 1) φ n)`. Both inequalities are equalities
at `n = 2`, where `x 2 = 5 / 2 = φ 2` and `x 3 / x 2 = 26 / 25`.

## Proof

Every `A n` is positive, by induction along the recurrence. Divided by `(n + 2) A (n + 1)`, the
recurrence `(n + 2) A (n + 2) = 2 (n + 2) A (n + 1) + 3n A n` at `n + 1` reads
`x (n + 1) = 2 + 3n / ((n + 2) x n)`. An induction proves `x n ≤ φ n` together with the lower
bound `6n / (2n + 1) ≤ x n`: the lower bound for `x n` gives the upper bound for `x (n + 1)`, and
the upper bound for `x n`, with `φ n ≤ φ (n + 1)`, gives the lower bound for `x (n + 1)`. For the
second inequality, clear the positive denominators and use the recurrence at `n + 1`: the
right-hand side minus the left-hand side becomes
`(3 (2n + 1) A n - 2 (n + 1) A (n + 1)) (3n (2n + 1) A n + 2 (3n² + 6n + 2) A (n + 1))`,
whose first factor is nonnegative by `x n ≤ φ n` and whose second factor is positive.

## Main results

* `MetaMathlibExt.a005773Recurrence_ratio_bounds`: both bounds, for every `n`.

## References

* Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
  Sequence*, INTEGERS 25 (2025), Article A100, Lemma 1.
-/

namespace MetaMathlibExt

@[expose] public section

variable {A : ℕ → ℝ}

/-- The recurrence at index `n + 1`, with the casts pushed through. -/
private lemma a005773Recurrence_succ
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) :
    ((n : ℝ) + 2) * A (n + 2) = 2 * ((n : ℝ) + 2) * A (n + 1) + 3 * n * A n := by
  have h := hrec (n + 1) (by omega)
  rw [Nat.add_sub_cancel] at h
  push_cast at h
  linear_combination h

/-- Two consecutive terms of the sequence are positive. -/
private lemma a005773Recurrence_pos (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) : 0 < A n ∧ 0 < A (n + 1) := by
  induction n with
  | zero => simp [h0, h1]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h := a005773Recurrence_succ hrec n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith [mul_pos (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 2)) ih.2,
      mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * (n : ℝ)) ih.1.le]

/-- The two-sided bound `6n / (2n + 1) ≤ A (n + 1) / A n ≤ 3 (2n + 1) / (2 (n + 1))`, with the
denominators cleared. -/
private lemma a005773Recurrence_ratio_mem (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) :
    6 * (n : ℝ) * A n ≤ (2 * n + 1) * A (n + 1) ∧
      2 * ((n : ℝ) + 1) * A (n + 1) ≤ 3 * (2 * n + 1) * A n := by
  induction n with
  | zero => norm_num [h0, h1]
  | succ n ih =>
    obtain ⟨hlo, hhi⟩ := ih
    have h := a005773Recurrence_succ hrec n
    have ha := (a005773Recurrence_pos h0 h1 hrec n).1
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    -- The upper bound at `n`, weakened to `A (n + 1) / A n ≤ φ (n + 1)`.
    have hhi' : 2 * ((n : ℝ) + 2) * A (n + 1) ≤ 3 * (2 * n + 3) * A n := by
      nlinarith [mul_le_mul_of_nonneg_left hhi (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2)]
    push_cast
    rw [show n + 1 + 1 = n + 2 from rfl]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hhi' hn]
    · linarith

/-- **Ratio bounds for the A005773 recurrence.**
Let $(A_n)_{n \ge 0}$ be a sequence of real numbers with $A_0 = A_1 = 1$ and
$(n+1) A_{n+1} = 2(n+1) A_n + 3(n-1) A_{n-1}$ for every $n \ge 1$. Write
$x_n = A_{n+1}/A_n$ and $\varphi_n = 3(2n+1)/(2(n+1))$. Then for every $n \ge 0$ we have
$x_n \le \varphi_n$ and
$$\frac{x_{n+1}}{x_n} \ge \frac{2(3n^2+6n+2)}{(n+2)(2n+1)\,\varphi_n}.$$

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Lemma 1. -/
public theorem a005773Recurrence_ratio_bounds (A : ℕ → ℝ) (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) :
    A (n + 1) / A n ≤ 3 * (2 * n + 1) / (2 * (n + 1)) ∧
      2 * (3 * (n : ℝ) ^ 2 + 6 * n + 2) /
          ((n + 2) * (2 * n + 1) * (3 * (2 * n + 1) / (2 * (n + 1))))
        ≤ (A (n + 2) / A (n + 1)) / (A (n + 1) / A n) := by
  obtain ⟨ha, hb⟩ := a005773Recurrence_pos h0 h1 hrec n
  have hc : 0 < A (n + 2) := (a005773Recurrence_pos h0 h1 hrec (n + 1)).2
  have hhi := (a005773Recurrence_ratio_mem h0 h1 hrec n).2
  have h := a005773Recurrence_succ hrec n
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  constructor
  · rw [div_le_div_iff₀ ha (by positivity)]
    linarith
  · have hφ : 2 * (3 * (n : ℝ) ^ 2 + 6 * n + 2) /
        ((n + 2) * (2 * n + 1) * (3 * (2 * n + 1) / (2 * (n + 1)))) =
        4 * ((n : ℝ) + 1) * (3 * n ^ 2 + 6 * n + 2) / (3 * (n + 2) * (2 * n + 1) ^ 2) := by
      field_simp
      ring
    -- Cleared of denominators, the difference of the two sides factors.
    have hfactor : A (n + 2) * A n * (3 * ((n : ℝ) + 2) * (2 * n + 1) ^ 2) -
        4 * ((n : ℝ) + 1) * (3 * n ^ 2 + 6 * n + 2) * (A (n + 1) * A (n + 1)) =
        (3 * (2 * n + 1) * A n - 2 * ((n : ℝ) + 1) * A (n + 1)) *
          (3 * n * (2 * n + 1) * A n + 2 * (3 * n ^ 2 + 6 * n + 2) * A (n + 1)) := by
      linear_combination (3 * (2 * (n : ℝ) + 1) ^ 2 * A n) * h
    have hnonneg : 0 ≤ (3 * (2 * n + 1) * A n - 2 * ((n : ℝ) + 1) * A (n + 1)) *
        (3 * n * (2 * n + 1) * A n + 2 * (3 * n ^ 2 + 6 * n + 2) * A (n + 1)) :=
      mul_nonneg (by linarith) (by positivity)
    rw [hφ, div_div_div_eq, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith

end

end MetaMathlibExt
