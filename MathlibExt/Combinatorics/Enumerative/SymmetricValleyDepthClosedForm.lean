/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import MathlibExt.Combinatorics.Enumerative.SymmetricValleyDepthGeneratingFunction
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination

/-!
# Closed form for the total depth of symmetric valleys over compositions

`MetaMathlibExt.symmetricValleyDepthSum_compositions_closed_form` extracts the coefficients
of the valley depth generating function. After cancellation, the denominator factors as
`(1 - 2 * X) ^ 2 * (1 + X) ^ 2 * (1 - X ^ 3)`. The last factor gives a correction of period three.
-/

open PowerSeries

namespace MetaMathlibExt
namespace symmetricValleyDepthSum_compositions_closed_form

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

-- The common denominator of all the rational coefficients is 5292.
private def correction (n : ℕ) : ℤ :=
  if n % 3 = 0 then -27 else if n % 3 = 1 then 513 else 837

private theorem correction_mul :
    mk correction * (1 - X ^ 3) = -27 + 513 * X + 837 * X ^ 2 := by
  rw [mul_sub, mul_one]
  change _ = -C (27 : ℤ) + C 513 * X + C 837 * X ^ 2
  ext (_ | _ | _ | n)
  all_goals
    simp only [map_sub, map_add, map_neg, coeff_mk, coeff_mul_X_pow', coeff_C,
      coeff_zero_mul_X, coeff_succ_mul_X]
    simp [correction, Nat.add_assoc]

private theorem scaled_depth (n : ℕ) :
    5292 * ((∑ c : Composition n, symmetricValleyDepthSum c.blocks : ℕ) : ℤ) =
      (-294 * n + 343) * (-1) ^ n + (84 * n - 316) * 2 ^ n + correction n := by
  let D := mk fun m => ((∑ c : Composition m, symmetricValleyDepthSum c.blocks : ℕ) : ℤ)
  let Q : ℤ⟦X⟧ := (1 - 2 * X) ^ 2 * (1 - X ^ 3) * (1 - X ^ 2) ^ 2
  have hD : D * Q = X ^ 5 - 2 * X ^ 6 + X ^ 7 := symmetricValleyDepthSum_compositions_genFun
  have hneg := affineGeom_mul (-294) 343 (-1)
  have htwo := affineGeom_mul 84 (-316) 2
  norm_num at hneg htwo
  have hQ : IsUnit Q := isUnit_iff_constantCoeff.mpr (by simp [Q])
  have h : 5292 * D = affineGeom (-294) 343 (-1) + affineGeom 84 (-316) 2 +
      mk correction := by
    apply hQ.mul_left_inj.mp
    dsimp only [Q] at hD ⊢
    linear_combination 5292 * hD -
      (1 - 2 * X) ^ 2 * (1 - X ^ 3) * (1 - X) ^ 2 * hneg -
      (1 - X ^ 3) * (1 - X ^ 2) ^ 2 * htwo -
      (1 - 2 * X) ^ 2 * (1 - X ^ 2) ^ 2 * correction_mul
  simpa [D, affineGeom, coeff_ofNat_mul, sub_eq_add_neg] using congrArg (coeff n) h

private noncomputable def wave (z : ℂ) (n : ℕ) : ℂ :=
  (-33 - 15 * z) * (-2) ^ n / (441 * (1 + z) ^ (n + 1))

private theorem wave_period (z : ℂ) (hz : z ^ 2 = -3) (n : ℕ) :
    wave z (n + 3) = wave z n := by
  have hcube : (1 + z) ^ 3 = -8 := by linear_combination (z + 3) * hz
  rw [wave, wave, show n + 3 + 1 = n + 1 + 3 by omega, pow_add (1 + z), hcube, pow_add,
    ← mul_assoc, ← mul_assoc (441 : ℂ), show (-2 : ℂ) ^ 3 = -8 by norm_num]
  exact mul_div_mul_right _ _ (by norm_num)

/-- The two conjugate terms and the constant give a rational correction of period three. -/
private theorem correction_eq (z : ℂ) (hz : z ^ 2 = -3) (n : ℕ) :
    (correction n : ℂ) = 5292 * (wave z n + wave (-z) n + 1 / 12) := by
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

end symmetricValleyDepthSum_compositions_closed_form

open symmetricValleyDepthSum_compositions_closed_form in
/-- **Closed form for the total depth of symmetric valleys over compositions.** For $n \ge 0$,
let $\operatorname{dsv}(n)$ be the sum, over all compositions $c$ of $n$, of the total depth of
the symmetric valleys of the sequence of parts of $c$, and write $\omega_\pm = 1 \pm i\sqrt{3}$.
Then, as complex numbers,
$$\operatorname{dsv}(n) = \frac{(-6n+7)(-1)^n}{108} + \frac{2^n(21n-79)}{1323} +
\frac{(-33-15\sqrt{3}\,i)(-2)^n}{441\,\omega_+^{n+1}} +
\frac{(-33+15\sqrt{3}\,i)(-2)^n}{441\,\omega_-^{n+1}} + \frac{1}{12}.$$

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Corollary 2, (12) (`integers-2026-A65-cor-2`). -/
public theorem symmetricValleyDepthSum_compositions_closed_form (n : ℕ) :
    ((∑ c : Composition n, symmetricValleyDepthSum c.blocks : ℕ) : ℂ) =
      (-6 * n + 7) / 108 * (-1) ^ n + (2 : ℂ) ^ n * (21 * n - 79) / 1323 +
        (-33 - 15 * (Real.sqrt 3 : ℂ) * Complex.I) * (-2) ^ n /
          (441 * (1 + Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) +
        (-33 + 15 * (Real.sqrt 3 : ℂ) * Complex.I) * (-2) ^ n /
          (441 * (1 - Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) + 1 / 12 := by
  let z := Complex.I * (Real.sqrt 3 : ℂ)
  have hz : z ^ 2 = -3 := by
    dsimp only [z]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h := congrArg (Int.cast : ℤ → ℂ) (scaled_depth n)
  push_cast at h ⊢
  rw [correction_eq z hz] at h
  simp only [wave, z, mul_neg, sub_neg_eq_add, ← sub_eq_add_neg] at h
  linear_combination h / 5292

end MetaMathlibExt
