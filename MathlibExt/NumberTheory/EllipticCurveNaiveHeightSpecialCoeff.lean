/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField

/-!
# Naive height lower bounds for elliptic curves with special coefficients

We bound the height of a rational point on `y² = x³ + ax + b` when `b = ±a`, `b = 0`
or `a = 0`, identifying the exceptional points below the bound.
-/

namespace MetaMathlibExt

namespace naiveHeight_lower_bound_of_special_coeff

private theorem coord_bounds (u v : ℚ) (i : Fin 3) :
    let q := ![u, v, 1] i
    let H := Height.mulHeight ![u, v, 1]
    |(q : ℝ)| ≤ H ∧ |(q.num : ℝ)| ≤ H ∧ (q.den : ℝ) ≤ H := by
  let q := ![u, v, 1] i
  have h : Height.mulHeight₁ q ≤ Height.mulHeight ![u, v, 1] := by
    rw [Height.mulHeight₁_eq_mulHeight]
    calc
      Height.mulHeight ![q, 1] = Height.mulHeight (![u, v, 1] ∘ ![i, 2]) :=
        congrArg Height.mulHeight (List.ofFn_inj.mp rfl)
      _ ≤ _ := Height.mulHeight_comp_le _ _
  rw [Rat.mulHeight₁_eq_max, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs, max_le_iff] at h
  refine ⟨le_trans ?_ h.1, h⟩
  change |(q : ℝ)| ≤ |(q.num : ℝ)|
  rw [Rat.cast_def, abs_div, abs_of_nonneg (Nat.cast_nonneg q.den : (0 : ℝ) ≤ q.den)]
  exact div_le_self (abs_nonneg _) (by exact_mod_cast q.den_pos)

/-- Clearing the denominator of `u` makes the linear form integral. If it is nonzero,
its absolute value is at least one, whereas the curve equation bounds its product with
the coefficient by twice the cube of the height. -/
private theorem linear_form_eq_zero (c m n : ℤ) {u v : ℚ} {k : ℝ} (hk : 2 ≤ k)
    (hP : v ^ 2 = u ^ 3 + c * (m * u + n))
    (hs : Height.mulHeight ![u, v, 1] < (|(c : ℝ)| / k) ^ ((1 : ℝ) / 3)) :
    (m : ℚ) * u + n = 0 := by
  let H := Height.mulHeight ![u, v, 1]
  have hH : 0 ≤ H := (Height.mulHeight_pos _).le
  change H < _ at hs
  have hk₀ : 0 < k := by linarith
  rw [one_div, Real.lt_rpow_inv_iff_of_pos hH (by positivity) (by norm_num),
    Real.rpow_ofNat, lt_div_iff₀ hk₀] at hs
  let z : ℤ := m * u.num + n * u.den
  have hzq : (z : ℚ) = (m * u + n) * u.den := by
    simp [z, add_mul, mul_assoc]
  by_contra hne
  have hz : z ≠ 0 := by
    intro he
    have : ((m : ℚ) * u + n) * u.den = 0 := by rw [← hzq, he, Int.cast_zero]
    exact (mul_ne_zero hne (by exact_mod_cast u.den_ne_zero)) this
  have hz₁ : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast (Int.add_one_le_of_lt (abs_pos.mpr hz))
  obtain ⟨hu, hnum, hden⟩ := coord_bounds u v 0
  have hv := (coord_bounds u v 1).1
  change |(u : ℝ)| ≤ H at hu
  change |(v : ℝ)| ≤ H at hv
  change |(u.num : ℝ)| ≤ H at hnum
  change (u.den : ℝ) ≤ H at hden
  have heq : (c : ℝ) * z = (v : ℝ) ^ 2 * u.den - (u : ℝ) ^ 2 * u.num := by
    exact_mod_cast (show (c : ℚ) * z = v ^ 2 * u.den - u ^ 2 * u.num by
      rw [hzq, ← u.mul_den_eq_num]
      linear_combination -(u.den : ℚ) * hP)
  have hbound : |(c : ℝ)| ≤ H ^ 3 * k := calc
    |(c : ℝ)| ≤ |(c : ℝ)| * |(z : ℝ)| := le_mul_of_one_le_right (abs_nonneg _) hz₁
    _ = |(v : ℝ) ^ 2 * u.den - (u : ℝ) ^ 2 * u.num| := by rw [← abs_mul, heq]
    _ ≤ |(v : ℝ) ^ 2 * u.den| + |(u : ℝ) ^ 2 * u.num| := abs_sub _ _
    _ ≤ H ^ 2 * H + H ^ 2 * H := by
      simp only [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg u.den : (0 : ℝ) ≤ u.den)]
      gcongr
    _ = H ^ 3 * 2 := by ring
    _ ≤ H ^ 3 * k := by gcongr
  exact hs.not_ge hbound

end naiveHeight_lower_bound_of_special_coeff

open naiveHeight_lower_bound_of_special_coeff in
set_option linter.unusedVariables false in
/-- **Height lower bounds on $y^2 = x^3 + ax + b$ when $b = \pm a$, $b = 0$ or $a = 0$.** Let
$a, b \in \mathbb{Z}$ with $4a^3 + 27b^2 \ne 0$, and for $u, v \in \mathbb{Q}$ let
$H(u, v) = \max(|U|, |V|, |W|)$, where $U, V, W$ are coprime integers with
$(U : V : W) = (u : v : 1)$. Consider the rational solutions $(u, v)$ of $v^2 = u^3 + au + b$.
(a) If $b = a$, every solution has $H(u, v) \ge (|a|/4)^{1/3}$.
(b) If $b = -a$, every solution with $H(u, v) < (|a|/4)^{1/3}$ is $(1, 1)$ or $(1, -1)$.
(c) If $b = 0$, every solution with $H(u, v) < (|a|/4)^{1/3}$ is $(0, 0)$.
(d) If $a = 0$, every solution has $H(u, v) \ge (|b|/3)^{1/3}$.

In (b) the points $(1, \pm 1)$ and the point at infinity need not form a subgroup of order
three: for $a = 5$, doubling $(1, 1)$ gives $(14, -53)$.

Source: Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66, Theorem 3 (`integers-2025-A66-thm-3`). -/
public theorem naiveHeight_lower_bound_of_special_coeff (a b : ℤ)
    (hE : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    (b = a → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        ¬ Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 4) ^ ((1 : ℝ) / 3)) ∧
      (b = -a → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 4) ^ ((1 : ℝ) / 3) →
          u = 1 ∧ (v = 1 ∨ v = -1)) ∧
      (b = 0 → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 4) ^ ((1 : ℝ) / 3) → u = 0 ∧ v = 0) ∧
      (a = 0 → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        ¬ Height.mulHeight ![u, v, 1] < (|(b : ℝ)| / 3) ^ ((1 : ℝ) / 3)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hb
    subst b
    intro u v hP hs
    have h := linear_form_eq_zero a 1 1 (by norm_num) (v := v) (u := u)
      (by push_cast; linarith only [hP]) hs
    norm_num at h
    have hu : u = -1 := by linarith only [h]
    rw [hu] at hP
    nlinarith only [hP, sq_nonneg v]
  · rintro rfl u v hP hs
    have h := linear_form_eq_zero a 1 (-1) (by norm_num) (v := v) (u := u)
      (by push_cast at *; linarith only [hP]) hs
    norm_num at h
    have hu : u = 1 := by linarith only [h]
    refine ⟨hu, sq_eq_one_iff.mp ?_⟩
    rw [hP, hu]
    push_cast
    ring
  · rintro rfl u v hP hs
    have h := linear_form_eq_zero a 1 0 (by norm_num) (v := v) (u := u)
      (by simpa using hP) hs
    have hu : u = 0 := by simpa using h
    exact ⟨hu, by simpa [hu] using hP⟩
  · rintro rfl u v hP hs
    have h := linear_form_eq_zero b 0 1 (by norm_num) (v := v) (u := u)
      (by simpa using hP) hs
    norm_num at h

end MetaMathlibExt
