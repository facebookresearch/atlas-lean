/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

The theorem statement in `benchmark/level2/ma_proofbench_l2_79.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029).
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors: L. Pu et al.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# A sixth-power bound for normalized test functions on the real line

Integrating the derivative of the square on a half-line and applying Cauchy–Schwarz
bounds the fourth power pointwise by four times the Dirichlet energy.
-/

namespace MathlibExt.Analysis.Calculus.SixthPowerIntegralLeDerivSqWanted

open MeasureTheory Set

private theorem pow_four_le_energy {u : ℝ → ℝ} (hu₁ : ContDiff ℝ 1 u)
    (hcomp : HasCompactSupport u) (hnorm : (∫ t, u t ^ 2) = 1) (x : ℝ) :
    u x ^ 4 ≤ 4 * ∫ t, (deriv u t) ^ 2 := by
  have hdu := hu₁.continuous_deriv_one
  have hs : HasCompactSupport (fun t ↦ u t ^ 2) :=
    hcomp.comp_left (g := fun z ↦ z ^ 2) (by norm_num)
  let E := ∫ t, (deriv u t) ^ 2
  have hE : 0 ≤ E := integral_nonneg fun _ ↦ sq_nonneg _
  have hCS : (∫ t, |u t| * |deriv u t|) ≤ √E := by
    have h := integral_mul_norm_le_Lp_mul_Lq (μ := volume) Real.HolderConjugate.two_two
      (hu₁.continuous.memLp_of_hasCompactSupport hcomp)
      (hdu.memLp_of_hasCompactSupport hcomp.deriv)
    simpa [E, Real.norm_eq_abs, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow, hnorm] using h
  have hFTC := HasCompactSupport.integral_Iic_deriv_eq (hu₁.pow 2) hs x
  have hprod : ∫ t in Iic x, 2 * (u t * deriv u t) = u x ^ 2 := by
    simpa [deriv_fun_pow (hu₁.differentiable_one _), mul_assoc] using hFTC
  have hint : Integrable (fun t ↦ |u t| * |deriv u t|) :=
    (hu₁.continuous.abs.mul hdu.abs).integrable_of_hasCompactSupport hcomp.abs.mul_right
  have hsq : u x ^ 2 ≤ 2 * √E := calc
    u x ^ 2 = 2 * ∫ t in Iic x, u t * deriv u t := by
      rw [← integral_const_mul, hprod]
    _ ≤ 2 * ∫ t in Iic x, |u t| * |deriv u t| := by
      gcongr 1
      simpa only [abs_mul] using
        (le_abs_self _).trans (abs_integral_le_integral_abs (f := fun t ↦ u t * deriv u t))
    _ ≤ 2 * ∫ t, |u t| * |deriv u t| := by
      gcongr 1
      exact setIntegral_le_integral hint (.of_forall fun t ↦
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ 2 * √E := by gcongr
  calc
    u x ^ 4 = (u x ^ 2) ^ 2 := by ring
    _ ≤ (2 * √E) ^ 2 := by gcongr
    _ = 4 * E := by rw [mul_pow, Real.sq_sqrt hE]; ring

/-- **Sixth-power integral bounded by the Dirichlet energy under $L^2$ normalization.** There is
a constant $C_2 > 0$ such that every infinitely differentiable, compactly supported function
$u : \mathbb{R} \to \mathbb{R}$ with $\int_{\mathbb{R}} u(t)^2 \, dt = 1$ satisfies
$$\int_{\mathbb{R}} u(t)^6 \, dt \le C_2 \int_{\mathbb{R}} u'(t)^2 \, dt.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities
in real analysis), `benchmark/level2/ma_proofbench_l2_79.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_integral_pow_six_le_integral_deriv_sq_of_integral_sq_eq_one :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ u : ℝ → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) u →
        HasCompactSupport u →
        (∫ t, (u t) ^ 2) = 1 →
          ∫ t, (u t) ^ 6 ≤ C2 * ∫ t, (deriv u t) ^ 2 := by
  refine ⟨4, by norm_num, fun u hu hcomp hnorm ↦ ?_⟩
  have hu₁ : ContDiff ℝ 1 u := hu.of_le (by simp)
  let E := ∫ t, (deriv u t) ^ 2
  have hint (n : ℕ) (hn : n ≠ 0) : Integrable (fun t ↦ u t ^ n) := by
    apply Continuous.integrable_of_hasCompactSupport (hu.continuous.pow n)
    exact hcomp.comp_left (g := fun z : ℝ ↦ z ^ n) (zero_pow hn)
  calc
    ∫ t, u t ^ 6 ≤ ∫ t, (4 * E) * u t ^ 2 := by
      apply integral_mono (hint 6 (by decide)) ((hint 2 (by decide)).const_mul _)
      intro t
      calc
        u t ^ 6 = u t ^ 4 * u t ^ 2 := by ring
        _ ≤ (4 * E) * u t ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_four_le_energy hu₁ hcomp hnorm t) (sq_nonneg _)
    _ = 4 * E := by rw [integral_const_mul, hnorm, mul_one]

end MathlibExt.Analysis.Calculus.SixthPowerIntegralLeDerivSqWanted
