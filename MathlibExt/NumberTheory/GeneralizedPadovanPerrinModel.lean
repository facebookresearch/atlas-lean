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
# Simple roots of the Padovan–Perrin polynomial for `p = 1`

For positive integers `k₁, k₂, s` with `(-k₂ (s + 1) / (k₁ s))^s ≠ k₁ / (s + 1)`, the
characteristic polynomial `P(z) = z^{s+1} - k₁ z - k₂` of the `([k]; 1; s)`-generalized
Padovan–Perrin recurrence `v n = k₁ v (n - s) + k₂ v (n - s - 1)` has only simple roots
(`padovanPerrin_charPoly_separable_of_p_eq_one`, stated as separability over `ℂ`).

## Proof outline

A multiple root `a` of `P` is a common root of `P` and `P' = (s + 1) z^s - k₁`. Eliminating the
leading power, `(s + 1) P - z P' = -(s k₁ z + (s + 1) k₂)`, so `a = -k₂ (s + 1) / (k₁ s)` is
rational, and `P'(a) = 0` says `a^s = k₁ / (s + 1)`: this is the case the hypothesis excludes.
Since `ℂ` is algebraically closed, `P` and `P'` are coprime once they have no common root
(`Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`).

The condition cannot be dropped: for `k₁ = 3`, `k₂ = 2`, `s = 2` both of its sides equal `1`, and
`z³ - 3 z - 2 = (z + 1)² (z - 2)` has the double root `-1`. The positivity of `k₂` is not used.

## Implementation notes

`padovanPerrin_charPoly_separable_of_p_eq_one` keeps the full name and the statement it had as a
wanted theorem in `WantedExt.NumberTheory.GeneralizedPadovanPerrinModelWanted`, including the
source's hypothesis `0 < k₂`, which the proof does not use; the unused-variables linter is turned
off for this declaration only.

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

end MetaMathlibExt
