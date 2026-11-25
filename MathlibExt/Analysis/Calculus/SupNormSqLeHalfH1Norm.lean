/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

The theorem statement in `benchmark/level1/ma_proofbench_l1_54.lean` (openbmb/ma-proofbench,
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

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# Sup-norm bound by the H¹ energy on an interval

The square of the sup norm of a function vanishing at both endpoints is bounded by half
its H¹ energy. We bound the change in its square from each endpoint to a maximum.
-/

namespace MathlibExt.Analysis.Calculus.SupNormSqLeHalfH1NormWanted

open Set MeasureTheory

private theorem norm_sq_sub_sq_le_integral {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Icc a b))
    (hint : IntervalIntegrable (fun t => f t ^ 2 + deriv f t ^ 2) volume a b) :
    ‖f b ^ 2 - f a ^ 2‖ ≤ ∫ t in a..b, (f t ^ 2 + deriv f t ^ 2) := by
  apply norm_sub_le_integral_of_norm_deriv_le_of_le (f := fun t => f t ^ 2) hab
    (hf.continuousOn.pow 2) ((hf.mono Ioo_subset_Icc_self).pow 2) _ hint
  refine Filter.Eventually.of_forall fun t ht => ?_
  have hd := (hf t (Ioo_subset_Icc_self ht)).differentiableAt (Icc_mem_nhds ht.1 ht.2)
  rw [deriv_fun_pow hd]
  simpa [Real.norm_eq_abs, abs_mul] using two_mul_le_add_sq |f t| |deriv f t|

/-- **Sup-norm bound by the $H^1$ energy for functions vanishing at both ends.** Let
$\alpha \le \beta$ be real numbers and let $f : \mathbb{R} \to \mathbb{R}$ be continuously
differentiable on $[\alpha, \beta]$ with $f(\alpha) = f(\beta) = 0$. Then
$$\Bigl(\sup_{x \in [\alpha, \beta]} |f(x)|\Bigr)^2 \le
\frac{1}{2} \int_\alpha^\beta \bigl(f(x)^2 + f'(x)^2\bigr)\,dx.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Inequalities in
real analysis), `benchmark/level1/ma_proofbench_l1_54.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem sSup_norm_sq_le_half_integral_sq_add_deriv_sq
    {α β : ℝ} (hαβ : α ≤ β) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc α β))
    (hfa : f α = 0) (hfb : f β = 0) :
    (sSup (Set.image (fun x => ‖f x‖) (Set.Icc α β))) ^ 2
      ≤ (1 / 2 : ℝ) *
          ∫ x in α..β, ((f x) ^ 2 + (deriv f x) ^ 2) := by
  rcases hαβ.eq_or_lt with rfl | hlt
  · simp [hfa]
  -- On the interior the ordinary derivative agrees with the continuous derivative within.
  have hcont := hf.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
  have hint : IntervalIntegrable (fun t => f t ^ 2 + deriv f t ^ 2) volume α β := by
    apply (((hf.continuousOn.pow 2).add (hcont.pow 2)).intervalIntegrable_of_Icc hαβ).congr_uIoo
    rw [uIoo_of_le hαβ]
    intro t ht
    simp [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  obtain ⟨x, hx, hmax⟩ := (isCompact_Icc.image_of_continuousOn hf.continuousOn.norm).sSup_mem
    ((nonempty_Icc.mpr hαβ).image _)
  obtain ⟨hleft, hright⟩ := (IntervalIntegrable.trans_iff (Icc_subset_uIcc hx)).mp hint
  have hdiff := hf.differentiableOn one_ne_zero
  have h₁ := norm_sq_sub_sq_le_integral hx.1 (hdiff.mono (Icc_subset_Icc_right hx.2)) hleft
  have h₂ := norm_sq_sub_sq_le_integral hx.2 (hdiff.mono (Icc_subset_Icc_left hx.1)) hright
  rw [← hmax, ← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  simp only [Real.norm_eq_abs, sq_abs]
  simp [hfa, hfb, Real.norm_eq_abs] at h₁ h₂
  linarith

end MathlibExt.Analysis.Calculus.SupNormSqLeHalfH1NormWanted
