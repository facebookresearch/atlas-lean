/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_06.lean` in openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029 (theorem statement and informal description).
Authors: L. Pu et al. (MA-ProofBench)
Licensed under the MIT License.

Copyright (c) 2026 OpenBMB

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

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# The signed radial function at the origin

The two diagonal restrictions agree by reflection, so their derivatives at zero must agree.
Linearity would then force the horizontal derivative to vanish, but the horizontal
restriction is the identity.
-/

public section

namespace MathlibExt.Analysis.Calculus.SignedRadialNotDifferentiableWanted

/-- **The signed radial function is not differentiable at the origin.** Let
$f : \mathbb{R}^2 \to \mathbb{R}$ be the function

$$
f(x,y)=
\begin{cases}
\sqrt{x^{2}+y^{2}}, & y>0,\\
x, & y=0,\\
-\sqrt{x^{2}+y^{2}}, & y<0.
\end{cases}
$$

Then $f$ is not differentiable at $(0, 0)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
several variables), `benchmark/level1/ma_proofbench_l1_06.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem not_differentiableAt_signed_norm_zero
    {f : ℝ × ℝ → ℝ} (hpos : ∀ x y : ℝ, y > 0 → f (x, y) = Real.sqrt (x ^ 2 + y ^ 2))
    (hzero : ∀ x : ℝ, f (x, 0) = x)
    (hneg : ∀ x y : ℝ, y < 0 → f (x, y) = -Real.sqrt (x ^ 2 + y ^ 2)) :
    ¬ DifferentiableAt ℝ f (0, 0) := by
  rintro ⟨L, hL⟩
  have hline (a b : ℝ) : deriv (fun t : ℝ ↦ f (t * a, t * b)) 0 = L (a, b) := by
    simpa [lineDeriv, ← Prod.zero_eq_mk, Prod.smul_mk, smul_eq_mul] using
      (hL.hasLineDerivAt (a, b)).lineDeriv
  have haxis : L (1, 0) = 1 := by
    simpa [hzero] using (hline 1 0).symm
  have hreflect (t : ℝ) : f (-t, t) = f (t, t) := by
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · simp [hneg _ _ ht]
    · simp
    · simp [hpos _ _ ht]
  have hdiag : L (-1, 1) = L (1, 1) := by
    simp [← hline, hreflect]
  have h : L ((0, 1) - (1, 0)) = L ((0, 1) + (1, 0)) := by
    simpa [Prod.mk_sub_mk, Prod.mk_add_mk] using hdiag
  rw [map_sub, map_add, haxis] at h
  linarith

end MathlibExt.Analysis.Calculus.SignedRadialNotDifferentiableWanted
