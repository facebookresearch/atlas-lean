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
# Naive height lower bounds for elliptic curves with a unit coefficient

We prove lower bounds for the multiplicative height of a rational point on
`y² = x³ + ax + b` when `a = ±1` or `b = ±1`, with exceptions at `(0, ±1)` when `b = 1`.
-/

namespace MetaMathlibExt

namespace naiveHeight_lower_bound_of_unit_coeff

private theorem abs_le_mulHeight₁ (q : ℚ) : |(q : ℝ)| ≤ Height.mulHeight₁ q := by
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  calc
    |(q : ℝ)| ≤ |(q.num : ℝ)| := by
      rw [Rat.cast_def, abs_div, abs_of_nonneg (Nat.cast_nonneg q.den : (0 : ℝ) ≤ q.den)]
      exact div_le_self (abs_nonneg _) hden
    _ ≤ Height.mulHeight₁ q := by
      rw [Rat.mulHeight₁_eq_max, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
      exact le_max_left _ _

private theorem mulHeight₁_coord_le (u v : ℚ) (i : Fin 3) :
    Height.mulHeight₁ (![u, v, 1] i) ≤ Height.mulHeight ![u, v, 1] := by
  rw [Height.mulHeight₁_eq_mulHeight]
  calc
    Height.mulHeight ![![u, v, 1] i, 1] = Height.mulHeight (![u, v, 1] ∘ ![i, 2]) :=
      congrArg Height.mulHeight (List.ofFn_inj.mp rfl)
    _ ≤ Height.mulHeight ![u, v, 1] := Height.mulHeight_comp_le _ _

private theorem not_lt_rpow_of_le_cube {c H : ℝ} (hH : 1 ≤ H)
    (hc : |c| ≤ 3 * H ^ 3) : ¬ H < (|c| / 5) ^ ((1 : ℝ) / 3) := by
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have h : |c| / 5 ≤ H ^ 3 := by linarith only [hc, pow_nonneg hH₀ 3]
  apply not_lt_of_ge
  calc
    (|c| / 5) ^ ((1 : ℝ) / 3) ≤ (H ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) h (by norm_num)
    _ = H := by
      rw [← Real.rpow_natCast_mul hH₀, show (↑(3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num,
        Real.rpow_one]

private theorem constCoeff_le_cube {a b u v H : ℝ} (hH : 1 ≤ H) (hu : |u| ≤ H) (hv : |v| ≤ H)
    (ha : |a| = 1) (hP : v ^ 2 = u ^ 3 + a * u + b) : |b| ≤ 3 * H ^ 3 := by
  have h₁ : H ≤ H ^ 3 := le_self_pow₀ hH (by decide)
  have h₂ : H ^ 2 ≤ H ^ 3 := pow_le_pow_right₀ hH (by decide : 2 ≤ 3)
  calc
    |b| = |v ^ 2 - u ^ 3 - a * u| := congrArg abs (by linarith only [hP])
    _ ≤ |v ^ 2| + |u ^ 3| + |a * u| :=
      (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ H ^ 2 + H ^ 3 + 1 * H := by
      simp only [abs_pow, abs_mul, ha]
      gcongr
    _ ≤ 3 * H ^ 3 := by linarith only [h₁, h₂]

private theorem linearCoeff_not_lt_rpow {a b : ℤ} {u v : ℚ} (hu : u ≠ 0)
    (hb : |(b : ℝ)| = 1) (hP : v ^ 2 = u ^ 3 + a * u + b) :
    ¬ Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 5) ^ ((1 : ℝ) / 3) := by
  let H := Height.mulHeight ![u, v, 1]
  have hH : 1 ≤ H := Height.one_le_mulHeight _
  have h₁ : H ≤ H ^ 3 := le_self_pow₀ hH (by decide)
  have h₂ : H ^ 2 ≤ H ^ 3 := pow_le_pow_right₀ hH (by decide : 2 ≤ 3)
  have huH : |(u : ℝ)| ≤ H := (abs_le_mulHeight₁ u).trans (mulHeight₁_coord_le u v 0)
  have hvH : |(v : ℝ)| ≤ H := (abs_le_mulHeight₁ v).trans (mulHeight₁_coord_le u v 1)
  have hinv : |(u : ℝ)⁻¹| ≤ H := by
    rw [← Rat.cast_inv]
    exact (abs_le_mulHeight₁ u⁻¹).trans (Height.mulHeight₁_inv u ▸ mulHeight₁_coord_le u v 0)
  have hu₀ : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  have hP' : (v : ℝ) ^ 2 = (u : ℝ) ^ 3 + (a : ℝ) * (u : ℝ) + (b : ℝ) := by
    exact_mod_cast hP
  apply not_lt_rpow_of_le_cube hH
  calc
    |(a : ℝ)| = |((v : ℝ) ^ 2 - b) * (u : ℝ)⁻¹ - (u : ℝ) ^ 2| := by
      congr 1
      field_simp
      linarith only [hP']
    _ ≤ (|(v : ℝ)| ^ 2 + 1) * |(u : ℝ)⁻¹| + |(u : ℝ)| ^ 2 := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_pow]
      gcongr
      have h := abs_sub ((v : ℝ) ^ 2) (b : ℝ)
      rwa [abs_pow, hb] at h
    _ ≤ (H ^ 2 + 1) * H + H ^ 2 := by gcongr
    _ = H ^ 3 + H + H ^ 2 := by ring
    _ ≤ 3 * H ^ 3 := by linarith only [h₁, h₂]

end naiveHeight_lower_bound_of_unit_coeff

open naiveHeight_lower_bound_of_unit_coeff in
set_option linter.unusedVariables false in
/-- **Height lower bounds on $y^2 = x^3 + ax + b$ when $a = \pm 1$ or $b = \pm 1$.** Let
$a, b \in \mathbb{Z}$ with $4a^3 + 27b^2 \ne 0$, and for $u, v \in \mathbb{Q}$ let
$H(u, v) = \max(|U|, |V|, |W|)$, where $U, V, W$ are coprime integers with
$(U : V : W) = (u : v : 1)$. Consider the rational solutions $(u, v)$ of $v^2 = u^3 + au + b$.
(a) If $a = \pm 1$ and $b \notin \{0, 1, -1\}$, every solution has $H(u, v) \ge (|b|/5)^{1/3}$.
(b) If $a \notin \{0, 1, -1\}$ and $b = -1$, every solution has $H(u, v) \ge (|a|/5)^{1/3}$.
(c) If $a \notin \{0, 1, -1\}$ and $b = 1$, every solution with $H(u, v) < (|a|/5)^{1/3}$ is
$(0, 1)$ or $(0, -1)$.

Source: Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66, Theorem 2 (`integers-2025-A66-thm-2`). -/
public theorem naiveHeight_lower_bound_of_unit_coeff (a b : ℤ)
    (hE : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    ((a = 1 ∨ a = -1) → b ≠ 0 → b ≠ 1 → b ≠ -1 → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        ¬ Height.mulHeight ![u, v, 1] < (|(b : ℝ)| / 5) ^ ((1 : ℝ) / 3)) ∧
      (a ≠ 0 → a ≠ 1 → a ≠ -1 → b = -1 → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        ¬ Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 5) ^ ((1 : ℝ) / 3)) ∧
      (a ≠ 0 → a ≠ 1 → a ≠ -1 → b = 1 → ∀ u v : ℚ, v ^ 2 = u ^ 3 + a * u + b →
        Height.mulHeight ![u, v, 1] < (|(a : ℝ)| / 5) ^ ((1 : ℝ) / 3) →
          u = 0 ∧ (v = 1 ∨ v = -1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ha _ _ _ u v hP
    have ha' : |(a : ℝ)| = 1 := by rcases ha with rfl | rfl <;> norm_num
    refine not_lt_rpow_of_le_cube (Height.one_le_mulHeight _) <|
      constCoeff_le_cube (Height.one_le_mulHeight _)
        ((abs_le_mulHeight₁ u).trans (mulHeight₁_coord_le u v 0))
        ((abs_le_mulHeight₁ v).trans (mulHeight₁_coord_le u v 1)) ha' ?_
    exact_mod_cast hP
  · rintro _ _ _ rfl u v hP
    by_cases hu : u = 0
    · simp [hu] at hP
      nlinarith only [hP, sq_nonneg v]
    · exact linearCoeff_not_lt_rpow hu (by norm_num) hP
  · rintro _ _ _ rfl u v hP hlt
    have hu : u = 0 := by
      by_contra hu
      exact linearCoeff_not_lt_rpow hu (by norm_num) hP hlt
    have hv : v ^ 2 = 1 := by simpa [hu] using hP
    exact ⟨hu, sq_eq_one_iff.mp hv⟩

end MetaMathlibExt
