/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_62.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the theorem statement.
Authors: Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu, Xin Li,
Jie Zhou and Yudong Wang.
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

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.Schwarz

/-!
# A derivative bound at `i` for a holomorphic self-map of the upper half-plane
-/

open Complex Metric
open UpperHalfPlane (upperHalfPlaneSet isOpen_upperHalfPlaneSet)
open scoped ComplexConjugate

namespace MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapDerivBoundWanted

private lemma norm_sub_lt_norm_sub_conj {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖z - w‖ < ‖z - conj w‖ := by
  apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
  simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, conj_re, conj_im]
  nlinarith [mul_pos hz hw]

private lemma norm_deriv_I_le_im {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hm : Set.MapsTo f upperHalfPlaneSet upperHalfPlaneSet) :
    ‖deriv f I‖ ≤ (f I).im := by
  let w := f I
  have hi : I ∈ upperHalfPlaneSet := by simp [upperHalfPlaneSet]
  have hw : 0 < w.im := hm hi
  -- The source Cayley map sends zero to i and has derivative 2i there.
  let φ (z : ℂ) := I * ((1 + z) / (1 - z))
  have hφ0 : φ 0 = I := by simp [φ]
  have hφmaps : Set.MapsTo φ (ball 0 1) upperHalfPlaneSet := by
    intro z hz
    have h := le_re_herglotzRieszKernel (z := (1 : ℂ)) (by simp) hz
    have hpos := div_pos (sub_pos.mpr (mem_ball_zero_iff.mp hz)) (by positivity : 0 < 1 + ‖z‖)
    simpa [φ, upperHalfPlaneSet] using hpos.trans_le (by simpa using h)
  have hφdiff : DifferentiableOn ℂ φ (ball 0 1) := by
    intro z hz
    have hden : 1 - z ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [← h] at hz
    dsimp [φ]
    fun_prop (disch := assumption)
  have hφ' : HasDerivAt φ (2 * I) 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).const_add 1).fun_div
      ((hasDerivAt_id (0 : ℂ)).const_sub 1) (by simp)
    simpa [φ, two_mul, mul_add] using h.const_mul I
  -- The target Cayley map sends w to zero, so the composite fixes zero.
  let ψ (z : ℂ) := (z - w) / (z - conj w)
  have hden {z : ℂ} (hz : 0 < z.im) : z - conj w ≠ 0 :=
    norm_pos_iff.mp ((norm_nonneg _).trans_lt (norm_sub_lt_norm_sub_conj hz hw))
  have hψdiff : DifferentiableOn ℂ ψ upperHalfPlaneSet := by
    intro z hz
    dsimp [ψ]
    fun_prop (disch := exact hden hz)
  have hψ' : HasDerivAt ψ (1 / (w - conj w)) w := by
    have h := ((hasDerivAt_id w).sub_const w).fun_div
      ((hasDerivAt_id w).sub_const (conj w)) (hden hw)
    simpa [ψ, pow_two, ← div_div, hden hw] using h
  let g := ψ ∘ f ∘ φ
  have hgdiff : DifferentiableOn ℂ g (ball 0 1) :=
    hψdiff.comp (hf.comp hφdiff hφmaps) (hm.comp hφmaps)
  have hgmaps : Set.MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
    have hg0 : g 0 = 0 := by simp [g, hφ0, ψ, w]
    rw [hg0]
    intro z hz
    have hz' : 0 < (f (φ z)).im := hm (hφmaps hz)
    rw [mem_closedBall_zero_iff]
    change ‖(f (φ z) - w) / (f (φ z) - conj w)‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hden hz'))]
    exact (norm_sub_lt_norm_sub_conj hz' hw).le
  have hf' := (hf.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hi)).hasDerivAt
  have hg' : HasDerivAt g ((1 / (w - conj w)) * (deriv f I * (2 * I))) 0 := by
    apply HasDerivAt.comp 0 _ (HasDerivAt.comp 0 _ hφ')
    · simpa only [Function.comp_apply, hφ0] using hψ'
    · simpa only [hφ0] using hf'
  have h := Complex.norm_deriv_le_one_of_mapsTo_ball hgdiff hgmaps zero_lt_one
  rw [hg'.deriv] at h
  have hdist : ‖w - conj w‖ = 2 * w.im := by
    rw [← dist_eq_norm, dist_self_conj, abs_of_pos hw]
  simpa [norm_mul, norm_div, hdist, field, hw.ne'] using h

/-- **Derivative bound at $i$ for a self-map of the upper half-plane.** Let
$\mathbb{H}=\{z\in\mathbb{C} : \mathrm{Im}\,z>0\}$ be the upper half-plane, and let $f$ be a
complex function that is holomorphic on $\mathbb{H}$, maps $\mathbb{H}$ into $\mathbb{H}$, and
satisfies $f(i)=e^{2\pi i/3}$. Then $|f'(i)|\le\sqrt{3/2}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_62.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem norm_deriv_I_le_sqrt_three_halves_of_mapsTo_upperHalfPlane
    (f : ℂ → ℂ)
    (hf_holo : DifferentiableOn ℂ f UpperHalfPlane.upperHalfPlaneSet)
    (hf_maps : Set.MapsTo f UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet)
    (hpoint : f Complex.I = Complex.exp ((2 * Real.pi * Complex.I) / 3)) :
    ‖deriv f Complex.I‖ ≤ Real.sqrt (3 / 2 : ℝ) := by
  calc
    ‖deriv f I‖ ≤ (f I).im := norm_deriv_I_le_im hf_holo hf_maps
    _ ≤ ‖f I‖ := im_le_norm _
    _ = 1 := by simp [hpoint, Complex.norm_exp, Complex.mul_im]
    _ ≤ Real.sqrt (3 / 2 : ℝ) := by
      apply (Real.le_sqrt (by norm_num) (by norm_num)).2
      norm_num

end MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapDerivBoundWanted
