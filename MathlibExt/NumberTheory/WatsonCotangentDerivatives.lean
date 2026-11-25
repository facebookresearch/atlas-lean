/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DowkerHalfSum
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Signs of Watson's cotangent derivatives

We prove that the odd cotangent derivatives in Watson's expansion are strictly negative.
-/

namespace MetaMathlibExt

namespace watson_odd_cotangent_deriv_neg

open Polynomial
open scoped Topology

/-- The polynomial giving the signed cotangent derivative at each order. -/
private noncomputable def derivPoly : ℕ → ℝ[X]
  | 0 => X
  | k + 1 => (derivPoly k).derivative * (1 + X ^ 2)

private theorem coeff_succ (k j : ℕ) :
    (derivPoly (k + 1)).coeff j =
      (derivPoly k).coeff (j + 1) * (j + 1) +
        if 2 ≤ j then (derivPoly k).derivative.coeff (j - 2) else 0 := by
  rw [derivPoly, mul_add, mul_one, coeff_add, coeff_mul_X_pow', coeff_derivative]

private theorem coeff_nonneg (k j : ℕ) : 0 ≤ (derivPoly k).coeff j := by
  induction k generalizing j with
  | zero =>
    rw [derivPoly, coeff_X]
    split_ifs <;> positivity
  | succ k ih =>
    rw [coeff_succ]
    refine add_nonneg (mul_nonneg (ih _) (by positivity)) ?_
    split_ifs
    · rw [coeff_derivative]
      exact mul_nonneg (ih _) (by positivity)
    · exact le_rfl

-- Only degrees of parity opposite to the derivative order can occur.
private theorem coeff_eq_zero_of_even_add (k j : ℕ) (h : Even (k + j)) :
    (derivPoly k).coeff j = 0 := by
  induction k generalizing j with
  | zero =>
    rw [derivPoly, coeff_X, ite_eq_right]
    rw [Nat.even_iff] at h
    omega
  | succ k ih =>
    rw [Nat.even_iff] at h
    have h₁ : Even (k + (j + 1)) := by rw [Nat.even_iff]; omega
    rw [coeff_succ, ih _ h₁, zero_mul, zero_add]
    split_ifs with hj
    · have h₂ : Even (k + (j - 2 + 1)) := by rw [Nat.even_iff]; omega
      rw [coeff_derivative, ih _ h₂, zero_mul]
    · rfl

-- Differentiation and multiplication by X² carry the linear coefficient
-- through degree two, from which one more differentiation returns it to degree one.
private theorem coeff_one_pos (k : ℕ) : 0 < (derivPoly (2 * k)).coeff 1 := by
  induction k with
  | zero => norm_num [derivPoly]
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
    have h₂ : 0 < (derivPoly (2 * k + 1)).coeff 2 := by
      norm_num [coeff_succ, coeff_derivative]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (coeff_nonneg _ _) (by norm_num)) ih
    rw [coeff_succ, ite_eq_right (by decide : ¬ 2 ≤ (1 : ℕ)), add_zero]
    exact mul_pos h₂ (by positivity : 0 < ((1 : ℕ) : ℝ) + 1)

private theorem eval_odd_pos (k : ℕ) (y : ℝ) : 0 < (derivPoly (2 * k + 1)).eval y := by
  rw [eval_eq_sum_range]
  apply Finset.sum_pos'
  · intro j _
    by_cases hj : Even j
    · exact mul_nonneg (coeff_nonneg _ _) (hj.pow_nonneg y)
    · have h : Even (2 * k + 1 + j) := by
        rw [Nat.even_iff] at hj ⊢
        omega
      simp [coeff_eq_zero_of_even_add _ _ h]
  · refine ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), ?_⟩
    simpa [coeff_succ] using coeff_one_pos k

private theorem hasDerivAt_cot {x : ℝ} (hx : Real.sin x ≠ 0) :
    HasDerivAt Real.cot (-(1 + Real.cot x ^ 2)) x := by
  rw [show Real.cot = fun y => Real.cos y / Real.sin y from
    funext Real.cot_eq_cos_div_sin]
  convert (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx using 1
  field_simp
  ring

private theorem iteratedDeriv_cot (k : ℕ) (x : ℝ) (hx : Real.sin x ≠ 0) :
    iteratedDeriv k Real.cot x = (-1 : ℝ) ^ k * (derivPoly k).eval (Real.cot x) := by
  induction k generalizing x with
  | zero => simp [derivPoly]
  | succ k ih =>
    have heq : iteratedDeriv k Real.cot =ᶠ[𝓝 x]
        fun y => (-1 : ℝ) ^ k * (derivPoly k).eval (Real.cot y) := by
      filter_upwards [Real.continuous_sin.continuousAt.eventually_ne hx] with y hy
      exact ih y hy
    have h := (((derivPoly k).hasDerivAt (Real.cot x)).comp x (hasDerivAt_cot hx)).const_mul
      ((-1 : ℝ) ^ k)
    simp only [Function.comp_apply] at h
    rw [iteratedDeriv_succ, heq.deriv_eq, h.deriv, derivPoly, eval_mul, eval_add, eval_one,
      eval_pow, eval_X, pow_succ]
    ring

end watson_odd_cotangent_deriv_neg

open watson_odd_cotangent_deriv_neg

/--
**The odd cotangent derivatives in Watson's expansion are negative.** Let $r$, $n$ and $\nu$ be
natural numbers with $r \ge 1$ and $1 \le \nu \le n - 1$. Then
$\mathcal{H}_{2r-1}(\nu/n) = \cot^{(2r-1)}(\pi\nu/n)$, the $(2r-1)$st derivative of the cotangent
evaluated at $\pi\nu/n$, is strictly negative.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 3 (printed as Theorem 4).
-/
public theorem watson_odd_cotangent_deriv_neg
    (r n ν : ℕ) (hr : 1 ≤ r) (hνpos : 1 ≤ ν) (hνmax : ν ≤ n - 1) :
    watsonOddCotangentDeriv r n ν < 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hν : (0 : ℝ) < ν := by exact_mod_cast (show 0 < ν by omega)
  have hνn : (ν : ℝ) < n := by exact_mod_cast (show ν < n by omega)
  have hpos : 0 < Real.pi * (ν : ℝ) / (n : ℝ) :=
    div_pos (mul_pos Real.pi_pos hν) hn
  have hlt : Real.pi * (ν : ℝ) / (n : ℝ) < Real.pi :=
    (div_lt_iff₀ hn).mpr (mul_lt_mul_of_pos_left hνn Real.pi_pos)
  have hsin := (Real.sin_pos_of_pos_of_lt_pi hpos hlt).ne'
  rw [watsonOddCotangentDeriv, show 2 * r - 1 = 2 * (r - 1) + 1 by omega,
    iteratedDeriv_cot _ _ hsin]
  rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul, neg_lt_zero]
  exact eval_odd_pos _ _

end MetaMathlibExt
