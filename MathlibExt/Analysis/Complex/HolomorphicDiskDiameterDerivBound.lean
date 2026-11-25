/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_78.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029).
Copyright (c) 2026 OpenBMB.
Licensed under the MIT License below.
Authors: L. Pu et al.
Adapted portions: the theorem statement and its problem description.

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

-- Preserve the complex normed-ring instances used by the original statement.
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Schwarz

/-! # Diameter bounds for holomorphic functions on the unit disc

The norm of the derivative at the center is at most half the extended diameter of the image.
-/

public section

namespace MathlibExt.Analysis.Complex.HolomorphicDiskDiameterDerivBoundWanted

/-- **Diameter bound for the derivative at the center of the disc.** Let $D$ be the open unit disc
in $\mathbb{C}$ and let $f : \mathbb{C} \to \mathbb{C}$ be holomorphic on $D$. Then the diameter
$d = \sup_{z,w \in D} |f(z) - f(w)|$ of the image $f(D)$, which may be $+\infty$, satisfies
$2|f'(0)| \le d$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_78.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem two_mul_norm_deriv_le_ediam_image_ball
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) :
    ENNReal.ofReal (2 * ‖deriv f 0‖) ≤ Metric.ediam (f '' (Metric.ball (0 : ℂ) 1)) := by
  by_cases htop : Metric.ediam (f '' Metric.ball 0 1) = ⊤
  · rw [htop]
    exact le_top
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  -- The difference at antipodal points has twice the derivative of f at zero.
  let g : ℂ → ℂ := fun z => f z - f (-z)
  have hneg : Set.MapsTo (fun z : ℂ => -z) (Metric.ball 0 1) (Metric.ball 0 1) := by
    intro z hz
    simpa [mem_ball_zero_iff] using hz
  have hg : DifferentiableOn ℂ g (Metric.ball 0 1) :=
    hf.sub (hf.comp differentiable_neg.differentiableOn hneg)
  have hmaps : Set.MapsTo g (Metric.ball 0 1)
      (Metric.closedBall (g 0) (Metric.ediam (f '' Metric.ball 0 1)).toReal) := by
    intro z hz
    rw [Metric.mem_closedBall, show g 0 = 0 by simp [g], dist_zero_right]
    change ‖f z - f (-z)‖ ≤ _
    rw [← ENNReal.ofReal_le_iff_le_toReal htop, ← dist_eq_norm_sub, ← edist_dist]
    exact Metric.edist_le_ediam_of_mem (Set.mem_image_of_mem f hz)
      (Set.mem_image_of_mem f (hneg hz))
  have hf₀ : DifferentiableAt ℂ f 0 :=
    hf.differentiableAt (Metric.ball_mem_nhds _ zero_lt_one)
  have hcomp : HasDerivAt (fun z => f (-z)) (-deriv f 0) 0 := by
    have houter : HasDerivAt f (deriv f 0) (-(0 : ℂ)) := by
      simpa only [neg_zero] using hf₀.hasDerivAt
    simpa only [Function.comp_def, mul_neg, mul_one] using
      houter.comp 0 (hasDerivAt_id (0 : ℂ)).neg
  have hsub : HasDerivAt g (deriv f 0 - -deriv f 0) 0 := hf₀.hasDerivAt.sub hcomp
  have hderiv : deriv g 0 = (2 : ℂ) * deriv f 0 := by
    rw [hsub.deriv, sub_neg_eq_add, two_mul]
  have hbound := Complex.norm_deriv_le_div_of_mapsTo_ball hg hmaps zero_lt_one
  simpa [hderiv, norm_mul] using hbound

end MathlibExt.Analysis.Complex.HolomorphicDiskDiameterDerivBoundWanted
