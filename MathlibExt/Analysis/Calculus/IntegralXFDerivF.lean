/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_16.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029). The theorem statement and problem description
are adapted from MA-ProofBench by L. Pu et al.
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.

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

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The integral of a weighted product with a derivative

Integration by parts gives $\int_a^b x f(x) f'(x)\,dx = -1/2$ for a $C^1$ function
vanishing at the endpoints with $\int_a^b f(x)^2\,dx = 1$.
-/

namespace MathlibExt.Analysis.Calculus.IntegralXFDerivFWanted

/-- **The integral of $x f(x) f'(x)$ equals $-1/2$.** Let $a<b$ and let
$f : \mathbb{R} \to \mathbb{R}$ be continuously differentiable on $[a,b]$ with $f(a)=f(b)=0$ and
$$
\int_a^b f(x)^2\,dx=1.
$$
Then
$$
\int_a^b x\,f(x)\,f'(x)\,dx=-\frac12.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_16.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem integral_mul_mul_deriv_eq_neg_half {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc a b))
    (hfa : f a = 0) (hfb : f b = 0)
    (hnorm : (∫ x in a..b, (f x) ^ 2) = 1) :
    (∫ x in a..b, x * f x * deriv f x) = (-(1 / 2 : ℝ)) := by
  have hsq : ContDiffOn ℝ 1 (fun x ↦ f x ^ 2) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact hf.pow 2
  have hid : AbsolutelyContinuousOnInterval (fun x : ℝ ↦ x) a b :=
    contDiffOn_id.absolutelyContinuousOnInterval
  have hparts := hid.integral_mul_deriv_eq_deriv_mul hsq.absolutelyContinuousOnInterval
  have htwice : 2 * (∫ x in a..b, x * f x * deriv f x) = -1 := calc
    _ = ∫ x in a..b, x * deriv (fun y ↦ f y ^ 2) x := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le hab.le
      intro x hx
      have hfx := (hf.differentiableOn one_ne_zero x (Set.mem_Icc_of_Ioo hx)).differentiableAt
        (Icc_mem_nhds hx.1 hx.2)
      simp [deriv_fun_pow hfx, mul_comm, mul_left_comm, mul_assoc]
    _ = -1 := by simpa [hfa, hfb, hnorm] using hparts
  linarith

end MathlibExt.Analysis.Calculus.IntegralXFDerivFWanted
