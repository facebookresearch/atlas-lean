/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tribonacci sequence with initial values 0, 0, 1

This module records the JIS concept `jis_sem_1b39589c4b5afc1c43ad6e8e`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Tribonacci sequence.** The Tribonacci sequence $(T_n)_{n \ge 0}$ is defined by $T_0 = 0$,
$T_1 = 0$, $T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for $n \ge 0$; it begins
$0, 0, 1, 1, 2, 4, \dots$ (OEIS A000073).

Source: JIS source statements `jis_16c3a95646fb4f21e9695b73`,
`jis_6d169983fc890fcb1432ab1e`, and `jis_91386fd90045523def73af3f`.

Source: Jiaqiang Pan, *Multiple Binomial Transforms and Families of Integer Sequences*,
Journal of Integer Sequences 13 (2010),
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Pan/pan8.tex>.
-/
def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n

/-- **Tribonacci differences do not keep one strict sign for three steps.** Let $T_n$ be the
Tribonacci numbers ($T_0 = T_1 = 0$, $T_2 = 1$, $T_{n+3} = T_{n+2} + T_{n+1} + T_n$) and let
$\alpha$ be a real number with $\alpha^3 = \alpha^2 + \alpha + 1$. Then for every $n \ge 0$ the
three numbers $T_{k+1} - \alpha T_k$ for $k = n, n + 1, n + 2$ are neither all positive nor all
negative.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 3 (`jis-2025-25.5.4-prop-3`). -/
public theorem tribonacci_succ_sub_mul_sign_changes (α : ℝ)
    (hα : α ^ 3 = α ^ 2 + α + 1) (n : ℕ) :
    ¬ (∀ i < 3, 0 < (tribonacci (n + i + 1) : ℝ) - α * tribonacci (n + i)) ∧
      ¬ (∀ i < 3, (tribonacci (n + i + 1) : ℝ) - α * tribonacci (n + i) < 0) := by
  have hα₀ : 0 < α := by
    by_contra! h
    have hc : α ^ 3 ≤ 0 := by
      rw [pow_succ]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg α) h
    nlinarith [sq_nonneg (α + 1)]
  have hα₁ : 1 < α := by
    by_contra! h
    have hc : α ^ 3 ≤ α ^ 2 := by
      calc
        α ^ 3 = α ^ 2 * α := by ring
        _ ≤ α ^ 2 * 1 := mul_le_mul_of_nonneg_left h (sq_nonneg α)
        _ = α ^ 2 := mul_one _
    linarith
  have h₁ : 0 < α - 1 := sub_pos.mpr hα₁
  have hprod : α * (α ^ 2 - α - 1) = 1 := by linarith
  have h₂ : 0 < α ^ 2 - α - 1 := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hα₀.le h
    linarith
  let T (k : ℕ) : ℝ := tribonacci k
  let D (i : ℕ) : ℝ := T (n + i + 1) - α * T (n + i)
  have hrec : T (n + 3) = T (n + 2) + T (n + 1) + T n := by
    change (tribonacci (n + 3) : ℝ) = _
    have h : tribonacci (n + 3) = tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := rfl
    rw [h, Nat.cast_add, Nat.cast_add]
  -- The cubic and the Tribonacci recurrence give a vanishing positive combination.
  have hD : D 2 + (α - 1) * D 1 + (α ^ 2 - α - 1) * D 0 = 0 := by
    change T (n + 3) - α * T (n + 2) + (α - 1) * (T (n + 2) - α * T (n + 1)) +
      (α ^ 2 - α - 1) * (T (n + 1) - α * T n) = 0
    calc
      _ = (1 + α + α ^ 2 - α ^ 3) * T n := by rw [hrec]; ring
      _ = 0 := by rw [show 1 + α + α ^ 2 - α ^ 3 = 0 by linarith, zero_mul]
  constructor
  · intro h
    have hD₁ : 0 < (α - 1) * D 1 := mul_pos h₁ (h 1 (by decide))
    have hD₀ : 0 < (α ^ 2 - α - 1) * D 0 := mul_pos h₂ (h 0 (by decide))
    exact (ne_of_gt (add_pos (add_pos (h 2 (by decide)) hD₁) hD₀)) hD
  · intro h
    have hD₁ : (α - 1) * D 1 < 0 := mul_neg_of_pos_of_neg h₁ (h 1 (by decide))
    have hD₀ : (α ^ 2 - α - 1) * D 0 < 0 := mul_neg_of_pos_of_neg h₂ (h 0 (by decide))
    exact (ne_of_lt (add_neg (add_neg (h 2 (by decide)) hD₁) hD₀)) hD

end

end MetaMathlibExt
