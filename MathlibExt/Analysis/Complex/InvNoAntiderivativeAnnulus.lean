/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_67.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the statement of
`not_exists_hasDerivAt_inv_on_annulus`.
Authors: L. Pu et al.
MIT License

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

-- Preserve the instances for the complex normed ring and continuous scalar multiplication
-- used in the original statement.
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# The reciprocal function has no antiderivative on an annulus

The circle of radius `3 / 2` about the origin lies in the annulus. The integral of the
reciprocal around it is `2 * π * I`, whereas the integral of a derivative would be zero.
-/

namespace MathlibExt.Analysis.Complex.InvNoAntiderivativeAnnulusWanted

/-- **The reciprocal function has no antiderivative on an annulus.** Let
$U = \{z \in \mathbb{C} : 1 < |z| < 2\}$. There is no function $F : \mathbb{C} \to \mathbb{C}$
that is complex differentiable at every $z \in U$ with $F'(z) = 1/z$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_67.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem not_exists_hasDerivAt_inv_on_annulus (U : Set ℂ)
    (hU : U = {z : ℂ | 1 < norm z ∧ norm z < 2}) :
    ¬ ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (1 / z) z := by
  rintro ⟨F, hF⟩
  apply Complex.two_pi_I_ne_zero
  rw [← circleIntegral.integral_sub_center_inv 0 (R := 3 / 2) (by norm_num)]
  apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f := F) (by norm_num)
  intro z hz
  have hzU : z ∈ U := by
    norm_num [hU, mem_sphere_zero_iff_norm.mp hz]
  simpa only [sub_zero, one_div] using (hF z hzU).hasDerivWithinAt

end MathlibExt.Analysis.Complex.InvNoAntiderivativeAnnulusWanted
