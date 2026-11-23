/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Sanford's coupled recurrence -/

namespace MetaMathlibExt

/-- **Sanford's coupled recurrence.** Let $a, b$ be real numbers in $(0, 1)$ with $a \ne b$, and
for every natural number $m$ put
$$
x_m = \frac{a(a - b)(1 - b)^m}{a(1 - b)^{m+1} - b(1 - a)^{m+1}}, \qquad
y_m = \frac{b(a - b)(1 - a)^m}{a(1 - b)^{m+1} - b(1 - a)^{m+1}}.
$$
Then for every natural number $n$,
$$
x_{n+1} = \frac{x_n(1 - y_n)}{1 - x_n y_n} \quad\text{and}\quad
y_{n+1} = \frac{y_n(1 - x_n)}{1 - x_n y_n}.
$$

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Lemma 1 (`integers-2025-A52-lem-1`). -/
public theorem sanford_coupled_recurrence {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (hab : a ≠ b) (n : ℕ) :
    let x : ℕ → ℝ := fun m =>
      a * (a - b) * (1 - b) ^ m / (a * (1 - b) ^ (m + 1) - b * (1 - a) ^ (m + 1))
    let y : ℕ → ℝ := fun m =>
      b * (a - b) * (1 - a) ^ m / (a * (1 - b) ^ (m + 1) - b * (1 - a) ^ (m + 1))
    x (n + 1) = x n * (1 - y n) / (1 - x n * y n) ∧
      y (n + 1) = y n * (1 - x n) / (1 - x n * y n) := by
  intro x y
  let d (k : ℕ) := a * (1 - b) ^ k - b * (1 - a) ^ k
  have ordered {u v : ℝ} (hu : 0 < u) (hv : v < 1) (huv : u < v) (k : ℕ) :
      u * (1 - v) ^ k < v * (1 - u) ^ k :=
    mul_lt_mul huv (pow_le_pow_left₀ (sub_nonneg.mpr hv.le) (sub_le_sub_left huv.le 1) k)
      (pow_pos (sub_pos.mpr hv) k) (hu.trans huv).le
  have hd (k : ℕ) : d k ≠ 0 := by
    apply sub_ne_zero.mpr
    rcases hab.lt_or_gt with h | h
    · exact (ordered ha₀ hb₁ h k).ne
    · exact (ordered hb₀ ha₁ h k).ne'
  have hx (k : ℕ) : x k = a * (a - b) * (1 - b) ^ k / d (k + 1) := rfl
  have hy (k : ℕ) : y k = b * (a - b) * (1 - a) ^ k / d (k + 1) := rfl
  -- Factor the denominator shared by the two updates.
  have hxy : 1 - x n * y n = d n * d (n + 2) / d (n + 1) ^ 2 := by
    rw [hx, hy]
    field_simp [hd]
    simp only [d, pow_succ]
    ring
  rw [hxy]
  constructor <;> simp only [hx, hy] <;> field_simp [hd] <;> simp only [d, pow_succ] <;> ring

end MetaMathlibExt
