/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Simple roots of the Padovan–Perrin polynomial

The `([k]; p; s)`-generalized Padovan–Perrin recurrence `v n = k₁ v (n - s) + k₂ v (n - s - p)`
has the characteristic polynomial `P(z) = z^{s+p} - k₁ z^p - k₂`. This file shows that `P` has
only simple roots, stated as separability over `ℂ`, in two cases:

* `padovanPerrin_charPoly_separable_of_p_eq_one`: `p = 1`, and `k₁, k₂, s` are positive integers
  with `(-k₂ (s + 1) / (k₁ s))^s ≠ k₁ / (s + 1)`;
* `padovanPerrin_charPoly_separable`: `k₁, k₂, p, s` are natural numbers with `k₁ > 0`, `p ≥ 2`,
  `p < s` and `k₁ ^ 2 < k₂`.

## Proof outline

A multiple root `a` of `P` is a common root of `P` and `P'`. Since `ℂ` is algebraically closed,
`P` and `P'` are coprime once they have no common root
(`Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`).

For `p = 1`, `P' = (s + 1) z^s - k₁`. Eliminating the leading power,
`(s + 1) P - z P' = -(s k₁ z + (s + 1) k₂)`, so `a = -k₂ (s + 1) / (k₁ s)` is rational, and
`P'(a) = 0` says `a^s = k₁ / (s + 1)`: this is the case the hypothesis excludes.

For `p ≥ 1`, `z P'(z) = z^p ((s + p) z^s - p k₁)` and `P(0) = -k₂ ≠ 0`, so a common root `a`
satisfies `(s + p) a^s = p k₁`, and then `(s + p) P(a) = 0` gives `s k₁ a^p = -(s + p) k₂`.
Taking absolute values, `|a|^s < k₁` and, as `k₁ ^ 2 < k₂`, `|a|^p > k₁ ≥ 1`. This is impossible
for `p ≤ s`: if `|a| ≥ 1` then `|a|^p ≤ |a|^s`, and if `|a| < 1` then `|a|^p < 1`.

The conditions cannot be dropped. For `k₁ = 3`, `k₂ = 2`, `s = 2` both sides of the condition for
`p = 1` equal `1`, and `z³ - 3 z - 2 = (z + 1)² (z - 2)` has the double root `-1`. Substituting
`z²` for `z` gives `p = 2`, `s = 4`, where `k₁ ^ 2 < k₂` fails and
`z⁶ - 3 z² - 2 = (z² + 1)² (z² - 2)` has the double roots `±i`. For `k₁ = 60`, `k₂ = 5184`,
`p = 3`, `s = 2`, where only `p < s` fails, `-6` is a double root of `z⁵ - 60 z³ - 5184`.

## Implementation notes

Both theorems keep the full names and statements they had as wanted theorems in
`WantedExt.NumberTheory.GeneralizedPadovanPerrinModelWanted`.
`padovanPerrin_charPoly_separable_of_p_eq_one` keeps the source's hypothesis `0 < k₂`, which its
proof does not use; the unused-variables linter is turned off for this declaration only. The proof
of `padovanPerrin_charPoly_separable` uses `p ≥ 2` only through `p ≠ 0`, and `p < s` only through
`p ≤ s`.

## References

* Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
  *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*,
  INTEGERS 24 (2024), Article A49.
-/

@[expose] public section

namespace MetaMathlibExt

open Polynomial

-- `hk₂` is a hypothesis of the source statement, kept for fidelity; the proof does not need it.
set_option linter.unusedVariables false in
/-- **Simple roots of the Padovan–Perrin polynomial for $p = 1$.** Let $k_1, k_2, s$ be positive
integers with $\left(-\frac{k_2 (s + 1)}{k_1 s}\right)^s \neq \frac{k_1}{s + 1}$. Then the
polynomial $P(z) = z^{s+1} - k_1 z - k_2$ is separable over $\mathbb{C}$, that is, it has only
simple roots.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 2 (`integers-2024-A49-lem-2`). -/
theorem padovanPerrin_charPoly_separable_of_p_eq_one (k₁ k₂ s : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hs : 0 < s)
    (h : (-(k₂ : ℚ) * (s + 1) / (k₁ * s)) ^ s ≠ k₁ / (s + 1)) :
    (X ^ (s + 1) - C (k₁ : ℂ) * X - C (k₂ : ℂ)).Separable := by
  rw [separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  intro a
  rw [← not_and_or]
  rintro ⟨hP, hP'⟩
  -- `hP : a ^ (s + 1) - k₁ * a - k₂ = 0` and `hP' : (s + 1) * a ^ s - k₁ = 0`.
  simp only [map_natCast, aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, eval_mul, eval_natCast,
    derivative_sub, derivative_X_pow_succ, map_add, map_one, derivative_mul, derivative_natCast,
    zero_mul, derivative_X, mul_one, zero_add, sub_zero, eval_add, eval_one] at hP hP'
  have hk₁' : (k₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk₁.ne'
  have hs' : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
  have hs1 : (s : ℂ) + 1 ≠ 0 := by exact_mod_cast s.succ_ne_zero
  -- The common root is the rational number `-k₂ (s + 1) / (k₁ s)`, since
  -- `(s + 1) P - X P' = -(s k₁ X + (s + 1) k₂)`.
  have ha : a = ((-(k₂ : ℚ) * (s + 1) / (k₁ * s) : ℚ) : ℂ) := by
    push_cast
    rw [eq_div_iff (mul_ne_zero hk₁' hs')]
    linear_combination -((s : ℂ) + 1) * hP + a * hP'
  -- `P'(a) = 0` now says that this rational number satisfies the excluded equation.
  apply h
  have key : (((-(k₂ : ℚ) * (s + 1) / (k₁ * s)) ^ s : ℚ) : ℂ) = ((k₁ / (s + 1) : ℚ) : ℂ) := by
    rw [Rat.cast_pow, ← ha]
    push_cast
    rw [eq_div_iff hs1]
    linear_combination hP'
  exact_mod_cast key

/-- **Simple roots of the Padovan–Perrin characteristic polynomial.** Let $k_1, k_2, p, s$ be
natural numbers with $k_1 > 0$, $p \ge 2$, $p < s$ and $k_1^2 < k_2$. Then the characteristic
polynomial $P(z) = z^{s+p} - k_1 z^p - k_2$ of the $([k]; p; s)$-generalized Padovan–Perrin
recurrence is separable over $\mathbb{C}$, that is, it has only simple roots.

The hypotheses force $k_2 > 0$ and $s > 0$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 4 (`integers-2024-A49-lem-4`). -/
theorem padovanPerrin_charPoly_separable (k₁ k₂ p s : ℕ) (hk₁ : 0 < k₁)
    (hp : 2 ≤ p) (hps : p < s) (hk : k₁ ^ 2 < k₂) :
    (X ^ (s + p) - C (k₁ : ℂ) * X ^ p - C (k₂ : ℂ)).Separable := by
  rw [separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  intro a
  rw [← not_and_or]
  rintro ⟨hP, hP'⟩
  -- `hP : a ^ (s + p) - k₁ * a ^ p - k₂ = 0` and
  -- `hP' : (s + p) * a ^ (s + p - 1) - k₁ * (p * a ^ (p - 1)) = 0`.
  simp only [map_natCast, aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, eval_mul, eval_natCast,
    derivative_sub, derivative_X_pow, derivative_mul, derivative_natCast, zero_mul, zero_add,
    sub_zero] at hP hP'
  -- `0` is not a root, since `P(0) = -k₂ ≠ 0`.
  have ha : a ≠ 0 := by
    rintro rfl
    simp [zero_pow (show s + p ≠ 0 by omega), zero_pow (show p ≠ 0 by omega)] at hP
    omega
  -- `a P'(a) = a^p ((s + p) a^s - p k₁)`, so `(s + p) a^s = p k₁`.
  have h₁ : ((s + p : ℕ) : ℂ) * a ^ s = (p * k₁ : ℕ) := by
    have h : a ^ p * (((s + p : ℕ) : ℂ) * a ^ s - (p * k₁ : ℕ)) = 0 := by
      push_cast at hP' ⊢
      linear_combination a * hP' - ((s : ℂ) + p) * mul_pow_sub_one (show s + p ≠ 0 by omega) a +
        (p : ℂ) * k₁ * mul_pow_sub_one (show p ≠ 0 by omega) a
    rw [mul_eq_zero, sub_eq_zero] at h
    exact h.resolve_left (pow_ne_zero _ ha)
  -- Then `(s + p) P(a) = 0` gives `s k₁ a^p = -(s + p) k₂`.
  have h₂ : ((s * k₁ : ℕ) : ℂ) * a ^ p = -((s + p) * k₂ : ℕ) := by
    push_cast at h₁ hP ⊢
    linear_combination (-((s : ℂ) + p)) * hP + a ^ p * h₁
  -- Taking norms: `(s + p) ‖a‖^s = p k₁` and `s k₁ ‖a‖^p = (s + p) k₂`.
  have hn₁ := congrArg norm h₁
  have hn₂ := congrArg norm h₂
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_natCast] at hn₁ hn₂
  push_cast at hn₁ hn₂
  have hs : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hk₁' : (1 : ℝ) ≤ k₁ := by exact_mod_cast hk₁
  have hk' : (k₁ : ℝ) ^ 2 < k₂ := by exact_mod_cast hk
  -- `‖a‖^s < k₁`, since `(s + p) ‖a‖^s = p k₁ < (s + p) k₁`.
  have hlt₁ : ‖a‖ ^ s < k₁ := by
    refine lt_of_mul_lt_mul_left (a := (s + p : ℝ)) ?_ (by positivity)
    rw [hn₁]
    nlinarith
  -- `k₁ < ‖a‖^p`, since `s k₁ ‖a‖^p = (s + p) k₂ ≥ s k₂ > s k₁ ^ 2`.
  have hlt₂ : (k₁ : ℝ) < ‖a‖ ^ p := by
    refine lt_of_mul_lt_mul_left (a := (s * k₁ : ℝ)) ?_ (by positivity)
    rw [hn₂]
    nlinarith
  -- These two bounds contradict each other when `p ≤ s`: compare `‖a‖` with `1`.
  rcases le_or_gt 1 ‖a‖ with h | h
  · linarith [pow_le_pow_right₀ h hps.le]
  · linarith [pow_le_one₀ (n := p) (norm_nonneg a) h.le]

end MetaMathlibExt
