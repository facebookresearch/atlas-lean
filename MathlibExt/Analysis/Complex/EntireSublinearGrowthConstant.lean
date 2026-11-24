/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_28.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029). The theorem statement is adapted from this problem.
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

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Entire functions of sublinear growth

The divided difference at zero extends to an entire function and tends to zero at infinity.
Liouville's theorem then makes the divided difference vanish everywhere.
-/

open Topology Filter Bornology

namespace MathlibExt.Analysis.Complex.EntireSublinearGrowthConstantWanted

/-- **An entire function of sublinear growth is constant.** Let $f : \mathbb{C} \to \mathbb{C}$
be an entire function such that $f(z)/z \to 0$ as $|z| \to \infty$. Then $f$ is constant: there
is $c \in \mathbb{C}$ with $f(z) = c$ for all $z \in \mathbb{C}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Entire and meromorphic functions of one complex variable, and related topics),
`benchmark/level2/ma_proofbench_l2_28.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_const_of_differentiable_of_tendsto_div_self_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hlim : Tendsto (fun z : ℂ => f z / z) (comap (fun z : ℂ => ‖z‖) atTop) (𝓝 (0 : ℂ))) :
    ∃ c : ℂ, ∀ z : ℂ, f z = c := by
  have hd : Differentiable ℂ (dslope f 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope univ_mem).2 hf.differentiableOn)
  rw [comap_norm_atTop] at hlim
  have hquot : Tendsto (fun z : ℂ => (f z - f 0) / z) (cobounded ℂ) (𝓝 0) := by
    simpa [div_eq_mul_inv, sub_mul] using hlim.sub (tendsto_inv₀_cobounded.const_mul (f 0))
  have hslope : Tendsto (dslope f 0) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    apply hquot.congr'
    filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
    simp [dslope_of_ne f hz, slope_def_field]
  refine ⟨f 0, fun z => sub_eq_zero.mp ?_⟩
  rw [← sub_smul_dslope f 0 z, hd.apply_eq_of_tendsto_cocompact z hslope, smul_zero]

end MathlibExt.Analysis.Complex.EntireSublinearGrowthConstantWanted
