/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_01.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029).
Authors: L. Pu et al. (MA-ProofBench).
The theorem statement is adapted from this problem and is covered by the MIT notice below.

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

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact

/-!
# Smooth functions vanishing on the coordinate axes

A smooth real-valued function that vanishes on both coordinate axes is bounded in absolute value
by a constant times the product of the absolute coordinates on the open unit square.

The inner product space import supplies the `NormedSpace ℝ ℝ` instance inferred in the original
wanted statement via `RCLike.toInnerProductSpaceReal`.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace MathlibExt.Analysis.Calculus.SmoothVanishingOnAxesBoundWanted

/-- **Smooth functions vanishing on the axes are $O(|x|\,|y|)$ near the origin.** Let
$f : \mathbb{R}^2 \to \mathbb{R}$ be infinitely differentiable with $f(x,y) = 0$ whenever $xy = 0$.
Then there is a constant $C > 0$ such that $|f(x,y)| \le C\,|x|\,|y|$ for all real $x$ and $y$ with
$|x| < 1$ and $|y| < 1$, that is, on the open unit ball of $\mathbb{R}^2$ for the maximum norm.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Functions of
several variables), `benchmark/level2/ma_proofbench_l2_01.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_abs_le_mul_abs_mul_abs_of_contDiff_of_eq_zero_on_axes
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hzero : ∀ x y : ℝ, x * y = 0 → f (x, y) = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : ℝ, (x, y) ∈ Metric.ball (0 : ℝ × ℝ) 1 →
        |f (x, y)| ≤ C * |x| * |y| := by
  let dx : ℝ × ℝ → ℝ := fun p => fderiv ℝ f p (1, 0)
  let dy_dx : ℝ × ℝ → ℝ := fun p => fderiv ℝ dx p (0, 1)
  have hf₂ : ContDiff ℝ 2 f := contDiff_infty.mp hf 2
  have hdx : ContDiff ℝ 1 dx :=
    (hf₂.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const
  have hdy_dx : Continuous dy_dx :=
    (hdx.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hderivX (x y : ℝ) : HasDerivAt (fun t => f (t, y)) (dx (x, y)) x :=
    (hf.differentiable (by simp) (x, y)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id' x).prodMk (hasDerivAt_const x y))
  have hderivYX (x y : ℝ) : HasDerivAt (fun t => dx (x, t)) (dy_dx (x, y)) y :=
    (hdx.differentiable one_ne_zero (x, y)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id' y))
  have hdx_zero (x : ℝ) : dx (x, 0) = 0 := by
    have haxis : (fun t => f (t, 0)) = fun _ => 0 :=
      funext fun t => hzero t 0 (mul_zero t)
    rw [← (hderivX x 0).deriv, haxis, deriv_const]
  -- Bound the mixed partial on the closed unit square.
  let I := Icc (-1 : ℝ) 1
  have hI : Convex ℝ I := convex_Icc _ _
  have h0 : (0 : ℝ) ∈ I := by simp [I]
  have hcompact : IsCompact (I ×ˢ I) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hdy_dx.norm.continuousOn
  let C := max 1 B
  have hbound (x y : ℝ) (hx : x ∈ I) (hy : y ∈ I) : ‖dy_dx (x, y)‖ ≤ C :=
    (hB (mem_image_of_mem _ (show (x, y) ∈ I ×ˢ I from ⟨hx, hy⟩))).trans (le_max_right _ _)
  -- First bound the horizontal derivative by comparing it to its value on the x-axis.
  have hboundX (x y : ℝ) (hx : x ∈ I) (hy : y ∈ I) : ‖dx (x, y)‖ ≤ C * ‖y‖ := by
    simpa only [hdx_zero x, sub_zero] using
      hI.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ => (hderivYX x t).hasDerivWithinAt) (fun t ht => hbound x t hx ht) h0 hy
  refine ⟨C, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro x y hxy
  simp only [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff] at hxy
  have hx : x ∈ I := abs_le.mp hxy.1.le
  have hy : y ∈ I := abs_le.mp hxy.2.le
  -- Compare the function to its value on the y-axis.
  simpa only [hzero 0 y (zero_mul y), sub_zero, Real.norm_eq_abs, mul_right_comm C |y| |x|] using
    hI.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hderivX t y).hasDerivWithinAt) (fun t ht => hboundX t y ht hy) h0 hx

end MathlibExt.Analysis.Calculus.SmoothVanishingOnAxesBoundWanted
