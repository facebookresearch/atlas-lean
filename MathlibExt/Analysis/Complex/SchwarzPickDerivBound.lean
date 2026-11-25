/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_86.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the statement of the theorem and the informal
problem it describes.
Authors: L. Pu et al. (MA-ProofBench)
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
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import MathlibExt.Analysis.Complex.SchwarzPick

/-!
# Schwarz–Pick derivative bound

The two-point Schwarz–Pick inequality gives a bound on the derivative of a holomorphic
self-map of the unit disc by taking the limit of its difference quotient.
-/

open Filter Metric
open scoped Topology

namespace MathlibExt.Analysis.Complex.SchwarzPickDerivBoundWanted

private lemma one_sub_sq_pos {a : ℂ} (ha : a ∈ ball 0 1) : 0 < 1 - ‖a‖ ^ 2 :=
  sub_pos.mpr (pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp ha) two_ne_zero)

private lemma tendsto_norm_denom {a : ℂ} (ha : a ∈ ball 0 1) :
    Tendsto (fun w : ℂ => ‖1 - star a * w‖) (𝓝 a) (𝓝 (1 - ‖a‖ ^ 2)) := by
  have h : ‖1 - star a * a‖ = 1 - ‖a‖ ^ 2 := by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_sub_sq_pos ha)]
  rw [← h]
  exact ((continuous_const.sub (continuous_const.mul continuous_id)).norm).continuousAt

/-- **Schwarz–Pick lemma, derivative form.** Let $\mathbb{D}=\{z\in\mathbb{C}:|z|<1\}$ be the open
unit disc. If $f:\mathbb{D}\to\mathbb{D}$ is holomorphic, then

\[
\frac{|f'(z)|}{1-|f(z)|^2}\le \frac{1}{1-|z|^2}\qquad\text{for all } z\in\mathbb{D}.
\]

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Geometric function theory), `benchmark/level1/ma_proofbench_l1_86.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem norm_deriv_div_one_sub_sq_le_of_mapsTo_unitBall (f : ℂ → ℂ)
    (hf_holo : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf_maps : Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1)) :
    ∀ z : ℂ, z ∈ Metric.ball 0 1 →
      norm (deriv f z) / (1 - (norm (f z)) ^ 2)
        ≤ 1 / (1 - (norm z) ^ 2) := by
  intro z hz
  have hd := hf_holo.differentiableAt (isOpen_ball.mem_nhds hz)
  have hlim := hd.hasDerivAt.tendsto_slope.norm.div
    ((tendsto_norm_denom (hf_maps hz)).comp (hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
    (one_sub_sq_pos (hf_maps hz)).ne'
  apply le_of_tendsto_of_tendsto hlim
    (tendsto_const_nhds.div ((tendsto_norm_denom hz).mono_left nhdsWithin_le_nhds)
      (one_sub_sq_pos hz).ne')
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz)]
    with w hw hwball
  have hne : ‖w - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw)
  have hpick := SchwarzPick.schwarzPick hf_holo hf_maps w hwball z hz
  change ‖slope f z w‖ / ‖1 - star (f z) * f w‖ ≤ 1 / ‖1 - star z * w‖
  rw [slope_def_field, norm_div, div_right_comm, ← norm_div]
  calc
    _ ≤ ‖(w - z) / (1 - star z * w)‖ / ‖w - z‖ :=
      div_le_div_of_nonneg_right hpick (norm_nonneg _)
    _ = _ := by rw [norm_div, div_right_comm, div_self hne]

end MathlibExt.Analysis.Complex.SchwarzPickDerivBoundWanted
