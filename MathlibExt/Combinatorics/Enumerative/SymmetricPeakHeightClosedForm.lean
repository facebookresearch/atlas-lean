/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightGeneratingFunction
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination

/-!
# Closed form for the total symmetric peak height over compositions

This file proves `MetaMathlibExt.symmetricPeakHeightSum_compositions_closed_form`: the sum
`hsp(n)` of the heights of the symmetric peaks over all compositions of `n` is given by the
closed form of Corollary 1, (6) in Walaa Asakly and Noor Kezil's paper (INTEGERS 26 (2026),
Article A65), cited in the theorem's docstring; in the preprint arXiv:2408.09166v1 the formula is
equation (7) of Corollary 3.

The proof reads off the coefficients of the generating function
`∑ₙ hsp(n) xⁿ = x⁴ / ((1 - 2x)² (1 - x³))`, proved in
`MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightGeneratingFunction`. In `ℤ⟦X⟧`, partial
fractions give `98 · hsp(n) = (7n - 24) · 2ⁿ + c(n)`, where `c(n)` is `24`, `34` or `40` according
as `n` is `0`, `1` or `2` modulo `3`. Since `-2 / (1 ± i√3)` are the primitive cube roots of
unity, the two conjugate terms of the closed form have period three; together with the constant
`1/3` they equal `c(n) / 98`, as one checks for `n = 0, 1, 2`.
-/

open PowerSeries

namespace MetaMathlibExt
namespace symmetricPeakHeightSum_compositions_closed_form

/-- The series `∑ₙ (a n + b) rⁿ xⁿ`. -/
private noncomputable def affineGeom (a b r : ℤ) : ℤ⟦X⟧ :=
  mk fun n => (a * n + b) * r ^ n

/-- Clearing a double geometric denominator leaves only a linear numerator. -/
private theorem affineGeom_mul (a b r : ℤ) :
    affineGeom a b r * (1 - C r * X) ^ 2 = C b + C ((a - b) * r) * X := by
  let f := affineGeom a b r
  change f * _ = _
  rw [show f * (1 - C r * X) ^ 2 =
    f - (f * C r * X + f * C r * X) + f * C r * X * C r * X by ring]
  ext (_ | _ | n)
  all_goals
    simp only [map_sub, map_add, coeff_zero_mul_X, coeff_succ_mul_X, coeff_zero_C,
      coeff_succ_C, coeff_mul_C, f, affineGeom, coeff_mk, Nat.cast_succ, Nat.cast_zero,
      pow_succ, pow_zero]
    ring

/-- The part of `98 · hsp(n)` of period three. -/
private def correction (n : ℕ) : ℤ :=
  if n % 3 = 0 then 24 else if n % 3 = 1 then 34 else 40

private theorem correction_mul :
    mk correction * (1 - X ^ 3) = 24 + 34 * X + 40 * X ^ 2 := by
  rw [mul_sub, mul_one]
  change _ = C (24 : ℤ) + C 34 * X + C 40 * X ^ 2
  ext (_ | _ | _ | n)
  all_goals
    simp only [map_sub, map_add, coeff_mk, coeff_mul_X_pow', coeff_C,
      coeff_zero_mul_X, coeff_succ_mul_X]
    simp [correction, Nat.add_assoc]

/-- Partial fractions: `98 · hsp(n) = (7n - 24) · 2ⁿ + c(n)`. -/
private theorem scaled_height (n : ℕ) :
    98 * ((∑ c : Composition n, symmetricPeakHeightSum c.blocks : ℕ) : ℤ) =
      (7 * n - 24) * 2 ^ n + correction n := by
  let H := mk fun m => ((∑ c : Composition m, symmetricPeakHeightSum c.blocks : ℕ) : ℤ)
  let Q : ℤ⟦X⟧ := (1 - 2 * X) ^ 2 * (1 - X ^ 3)
  have hH : H * Q = X ^ 4 := symmetricPeakHeightSum_compositions_genFun
  have htwo := affineGeom_mul 7 (-24) 2
  norm_num at htwo
  have hQ : IsUnit Q := isUnit_iff_constantCoeff.mpr (by simp [Q])
  have h : 98 * H = affineGeom 7 (-24) 2 + mk correction := by
    apply hQ.mul_left_inj.mp
    dsimp only [Q] at hH ⊢
    linear_combination 98 * hH - (1 - X ^ 3) * htwo - (1 - 2 * X) ^ 2 * correction_mul
  simpa [H, affineGeom, coeff_ofNat_mul, sub_eq_add_neg] using congrArg (coeff n) h

/-- The term `(-33 - 15 z) (-2)ⁿ / (441 (1 + z)ⁿ⁺¹)` of the closed form, for `z = ± i√3`. -/
private noncomputable def wave (z : ℂ) (n : ℕ) : ℂ :=
  (-33 - 15 * z) * (-2) ^ n / (441 * (1 + z) ^ (n + 1))

private theorem wave_period (z : ℂ) (hz : z ^ 2 = -3) (n : ℕ) :
    wave z (n + 3) = wave z n := by
  have hcube : (1 + z) ^ 3 = -8 := by linear_combination (z + 3) * hz
  rw [wave, wave, show n + 3 + 1 = n + 1 + 3 by omega, pow_add (1 + z), hcube, pow_add,
    ← mul_assoc, ← mul_assoc (441 : ℂ), show (-2 : ℂ) ^ 3 = -8 by norm_num]
  exact mul_div_mul_right _ _ (by norm_num)

/-- The two conjugate terms and the constant give the part of period three. -/
private theorem correction_eq (z : ℂ) (hz : z ^ 2 = -3) (n : ℕ) :
    (correction n : ℂ) = 98 * (wave z n + wave (-z) n + 1 / 3) := by
  have hz' : (-z) ^ 2 = -3 := by simpa only [neg_sq] using hz
  have h₁ : 1 + z ≠ 0 := by grind
  have h₂ : 1 + -z ≠ 0 := by grind
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 | 2 =>
      norm_num [correction, wave]
      field_simp
      grind
    | n + 3 =>
      rw [wave_period z hz, wave_period (-z) hz']
      simpa only [correction, Nat.add_mod_right] using ih n (by omega)

end symmetricPeakHeightSum_compositions_closed_form

open symmetricPeakHeightSum_compositions_closed_form in
/-- **Closed form for the total symmetric peak height over compositions.** For $n \ge 0$ let
$\mathrm{hsp}(n)$ be the sum, over all compositions $c$ of $n$, of the symmetric peak height
sum of the sequence of parts of $c$, and let $\omega_\pm = 1 \pm i\sqrt{3}$. Then for every
$n \ge 0$, as complex numbers,
$$
\mathrm{hsp}(n) = \frac{2^n}{2} \cdot \frac{7n - 24}{49} +
\frac{(-33 - 15 i \sqrt{3})(-2)^n}{441\, \omega_+^{n+1}} +
\frac{(-33 + 15 i \sqrt{3})(-2)^n}{441\, \omega_-^{n+1}} + \frac{1}{3}.
$$

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Corollary 1, (6) (`integers-2026-A65-cor-1`). -/
public theorem symmetricPeakHeightSum_compositions_closed_form (n : ℕ) :
    ((∑ c : Composition n, symmetricPeakHeightSum c.blocks : ℕ) : ℂ) =
      (2 : ℂ) ^ n / 2 * (7 * n - 24) / 49 +
        (-33 - 15 * Complex.I * (Real.sqrt 3 : ℂ)) * (-2) ^ n /
          (441 * (1 + Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) +
        (-33 + 15 * Complex.I * (Real.sqrt 3 : ℂ)) * (-2) ^ n /
          (441 * (1 - Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) + 1 / 3 := by
  let z := Complex.I * (Real.sqrt 3 : ℂ)
  have hz : z ^ 2 = -3 := by
    dsimp only [z]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h := congrArg (Int.cast : ℤ → ℂ) (scaled_height n)
  push_cast at h ⊢
  rw [correction_eq z hz] at h
  simp only [wave, z, mul_neg, sub_neg_eq_add, ← sub_eq_add_neg] at h
  linear_combination h / 98

end MetaMathlibExt
