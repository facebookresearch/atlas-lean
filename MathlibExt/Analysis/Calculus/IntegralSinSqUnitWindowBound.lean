/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_29.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029):
Copyright (c) 2026 OpenBMB. Licensed under the MIT License.
Authors: L. Pu et al.
The theorem statement and its informal description are adapted from this source.

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

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A unit-window bound for the integral of `sin (t ^ 2)`

The integral of `sin (t ^ 2)` over `[x, x + 1]` has absolute value strictly less than
`1 / x` for every positive `x`.
-/

namespace MathlibExt.Analysis.Calculus.IntegralSinSqUnitWindowBoundWanted

open Set intervalIntegral

/-- Estimate either sign of the integral by differentiating `-(1 + s * cos (t ^ 2)) / t`. -/
private theorem signed_integral_lt {x b s : ℝ} (hx : 0 < x) (hb : x < b) (hs : |s| ≤ 1) :
    s * (∫ t in x..b, Real.sin (t ^ 2)) < 1 / x := by
  let g (t : ℝ) := 1 + s * Real.cos (t ^ 2)
  have hg (t : ℝ) : 0 ≤ g t ∧ g t ≤ 2 := by
    have h : |s * Real.cos (t ^ 2)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (Real.abs_cos_le_one _)
    obtain ⟨hl, hu⟩ := abs_le.mp h
    dsimp [g]
    constructor <;> linarith
  let r (t : ℝ) := g t / t ^ 2
  have hr : ContinuousOn r (Icc x b) := by
    refine ContinuousOn.div (by dsimp [g]; fun_prop) (by fun_prop) ?_
    exact fun t ht ↦ pow_ne_zero _ (hx.trans_le ht.1).ne'
  have hr₀ (t : ℝ) : 0 ≤ r t := div_nonneg (hg t).1 (sq_nonneg _)
  have hsin : Continuous (fun t : ℝ ↦ (2 * s) * Real.sin (t ^ 2)) := by fun_prop
  have hderiv (t : ℝ) (ht : t ∈ uIcc x b) :
      HasDerivAt (fun u ↦ -(g u / u)) ((2 * s) * Real.sin (t ^ 2) + r t) t := by
    rw [uIcc_of_le hb.le] at ht
    have ht₀ := (hx.trans_le ht.1).ne'
    have hd := (((hasDerivAt_pow 2 t).cos.const_mul s).const_add 1).div (hasDerivAt_id t) ht₀
    apply hd.neg.congr_deriv
    dsimp [g, r]
    field_simp
    ring
  have hparts := integral_eq_sub_of_hasDerivAt hderiv
    ((hsin.continuousOn.add hr).intervalIntegrable_of_Icc hb.le)
  rw [integral_add (hsin.intervalIntegrable x b) (hr.intervalIntegrable_of_Icc hb.le),
    integral_const_mul] at hparts
  have hright : 0 ≤ g b / b := div_nonneg (hg b).1 (hx.trans hb).le
  -- If the numerator vanishes at the left endpoint, the signed integral is nonpositive.
  -- Otherwise the continuous remainder is strictly positive there.
  rcases (hg x).1.eq_or_lt with hzero | hpos
  · rw [← hzero, zero_div] at hparts
    have := integral_nonneg_of_forall (μ := MeasureTheory.volume) hb.le hr₀
    linarith [one_div_pos.mpr hx]
  · have hstrict := integral_pos hb hr (fun t _ ↦ hr₀ t)
        ⟨x, left_mem_Icc.mpr hb.le, div_pos hpos (sq_pos_of_pos hx)⟩
    have hleft := div_le_div_of_nonneg_right (hg x).2 hx.le
    rw [show 2 / x = 2 * (1 / x) by ring] at hleft
    linarith

/-- **Unit-window bound for the integral of $\sin(t^2)$.** Let $f : \mathbb{R} \to \mathbb{R}$ be
given by $f(x) = \int_x^{x+1} \sin(t^2)\,dt$. Then $|f(x)| < 1/x$ for every real $x > 0$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_29.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem abs_integral_sin_sq_lt_inv (f : ℝ → ℝ)
    (hf : f = fun x : ℝ => ∫ t in x..(x + 1), Real.sin (t ^ 2))
    (x : ℝ) (hx : 0 < x) :
    |f x| < 1 / x := by
  subst f
  rw [abs_lt]
  constructor
  · have h := signed_integral_lt (s := -1) hx (lt_add_one x) (by norm_num)
    linarith
  · simpa using signed_integral_lt (s := 1) hx (lt_add_one x) (by norm_num)

end MathlibExt.Analysis.Calculus.IntegralSinSqUnitWindowBoundWanted
