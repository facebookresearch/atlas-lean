/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_94.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029):
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors: L. Pu et al. (MA-ProofBench, arXiv:2606.13782).

This attribution applies to the theorem statement.

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

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Agmon's inequality on the line

We prove Agmon's inequality for real-valued Schwartz functions on the real line.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace MathlibExt.Analysis.FunctionalAnalysis.AgmonInequalitySchwartzLineWanted

/-- **Agmon's inequality on the line.** There is a constant $C > 0$ such that every real-valued
Schwartz function $f \colon \mathbb{R} \to \mathbb{R}$ satisfies
$$\|f\|_{L^\infty} \le C \, \|f\|_{L^2}^{1/2} \, \|f'\|_{L^2}^{1/2},$$
where $f'$ is the derivative of $f$ and the $L^\infty$ and $L^2$ norms are taken with respect to
Lebesgue measure on $\mathbb{R}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities
in real analysis), `benchmark/level2/ma_proofbench_l2_94.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exists_norm_toLp_top_le_mul_sqrt_norm_toLp_two_mul_sqrt_deriv :
    ∃ C > 0, ∀ f : SchwartzMap ℝ ℝ,
      ‖f.toLp (⊤ : ENNReal) (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖ ≤
        C * Real.sqrt ‖f.toLp (2 : ENNReal) (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖ *
          Real.sqrt
            ‖(SchwartzMap.derivCLM ℝ ℝ f).toLp
                (2 : ENNReal) (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖ := by
  refine ⟨Real.sqrt 2, Real.sqrt_pos.2 (by norm_num), fun f ↦ ?_⟩
  let g := SchwartzMap.derivCLM ℝ ℝ f
  have hf := f.memLp 2 volume
  have hg := g.memLp 2 volume
  have hprod : Integrable (fun t ↦ f t * g t) volume := hf.integrable_mul hg
  have hcs : (∫ t, ‖f t‖ * ‖g t‖) ≤ ‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖ := by
    rw [SchwartzMap.norm_toLp' (by norm_num) (by simp),
      SchwartzMap.norm_toLp' (by norm_num) (by simp)]
    simpa only [one_div, ENNReal.toReal_ofNat] using
      (integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        (by simpa using hf) (by simpa using hg))
  have hzero : Tendsto (fun t ↦ f t ^ 2) atBot (𝓝 0) := by
    simpa using (f.tendsto_cocompact.mono_left atBot_le_cocompact).pow 2
  rw [SchwartzMap.norm_toLp, eLpNorm_exponent_top f.continuous.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity)
    (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x ↦ ?_))
  -- Integrate the derivative of the square from minus infinity.
  have hderiv (t : ℝ) : HasDerivAt (fun y ↦ f y ^ 2) (2 * (f t * g t)) t := by
    have h : HasDerivAt f (g t) t := f.hasDerivAt t
    rw [show 2 * (f t * g t) = g t * f t + f t * g t by ring]
    simp only [pow_two]
    exact h.fun_mul h
  have hftc : (∫ t in Iic x, 2 * (f t * g t)) = f x ^ 2 := by
    simpa only [sub_zero] using integral_Iic_of_hasDerivAt_of_tendsto'
      (fun t _ ↦ hderiv t) (hprod.const_mul 2).integrableOn hzero
  have hsquare : ‖f x‖ ^ 2 ≤ 2 * (‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖) := calc
    ‖f x‖ ^ 2 = ‖∫ t in Iic x, 2 * (f t * g t)‖ := by
      rw [hftc, norm_pow]
    _ ≤ ∫ t in Iic x, ‖2 * (f t * g t)‖ := norm_integral_le_integral_norm _
    _ = 2 * (∫ t in Iic x, ‖f t‖ * ‖g t‖) := by
      simp only [norm_mul, Real.norm_ofNat, integral_const_mul]
    _ ≤ 2 * (∫ t, ‖f t‖ * ‖g t‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact setIntegral_le_integral (by simpa only [norm_mul] using hprod.norm)
        (Eventually.of_forall fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ 2 * (‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖) :=
      mul_le_mul_of_nonneg_left hcs (by norm_num)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num),
    Real.sqrt_mul (norm_nonneg (f.toLp 2 volume)), mul_assoc] using Real.sqrt_le_sqrt hsquare

end MathlibExt.Analysis.FunctionalAnalysis.AgmonInequalitySchwartzLineWanted
