/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Log-convexity of sup|f| over circles |z−r|=r: A(1)² ≤ A(2)A(2/3)

The following OpenBMB notice applies to the adapted statement and its documentation.

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

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_99.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. The original ATLAS import converted
`theorem ma_proofbench_l2_99 … := by sorry` into the Batteries `theorem_wanted`
`sq_sSup_norm_circle_one_le_mul`; moved the informal problem statement docstring onto it and
placed the declarations in namespace
`MathlibExt.Analysis.Complex.SupOnTangentCirclesLogConvexWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This change proves the statement and moves it to the proved library.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Three tangent circles

Inversion maps each circle tangent at zero to a vertical line after removing zero.
Hadamard's three-lines theorem applies to the function composed with inversion on the
bounded-width strip, where the inverse images lie in a fixed compact ball. The tangency
point belongs to both boundary circles and can be bounded directly.
-/

open Set Complex HadamardThreeLines

namespace MathlibExt.Analysis.Complex.SupOnTangentCirclesLogConvexWanted

private theorem mem_circle_iff_inv_re {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ≠ 0) :
    ‖z - (r : ℂ)‖ = r ↔ (z⁻¹).re = 1 / (2 * r) := by
  have hsq : ‖z - (r : ℂ)‖ = r ↔ normSq z = 2 * r * z.re := by
    rw [← sq_eq_sq₀ (norm_nonneg _) hr.le, ← normSq_eq_norm_sq]
    simp only [normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
    constructor <;> intro h <;> nlinarith
  rw [hsq, inv_re, div_eq_div_iff (normSq_pos.mpr hz).ne' (by positivity)]
  constructor <;> intro h <;> linarith

private theorem circle_value_le {f : ℂ → ℂ} (hf : Continuous f) {A : ℝ → ℝ}
    (hA : ∀ r : ℝ, 0 < r → A r = sSup {t : ℝ | ∃ z : ℂ, ‖z - (r : ℂ)‖ = r ∧ t = ‖f z‖})
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z - (r : ℂ)‖ = r) : ‖f z‖ ≤ A r := by
  have hset : {t : ℝ | ∃ z : ℂ, ‖z - (r : ℂ)‖ = r ∧ t = ‖f z‖} =
      (fun w => ‖f w‖) '' Metric.sphere (r : ℂ) r := by
    ext t
    simp only [mem_ofPred_eq, mem_image, Metric.mem_sphere, dist_eq_norm]
    constructor
    · rintro ⟨w, hw, ht⟩
      exact ⟨w, hw, ht.symm⟩
    · rintro ⟨w, hw, ht⟩
      exact ⟨w, hw, ht.symm⟩
  rw [hA r hr, hset]
  exact le_csSup ((isCompact_sphere _ _).bddAbove_image hf.norm.continuousOn)
    ⟨z, by simpa [Metric.mem_sphere, dist_eq_norm] using hz, rfl⟩

private theorem inv_norm_le_four {w : ℂ}
    (hw : w ∈ verticalClosedStrip (1 / 4) (3 / 4)) : ‖w⁻¹‖ ≤ 4 := by
  have hr : 1 / 4 ≤ w.re := hw.1
  have h : 1 / 4 ≤ ‖w‖ := hr.trans (re_le_norm w)
  have hpos : 0 < ‖w‖ := (by norm_num : (0 : ℝ) < 1 / 4).trans_le h
  rw [norm_inv, inv_eq_one_div, div_le_iff₀ hpos]
  linarith

private theorem strip_inversion_bdd {f : ℂ → ℂ} (hf : Continuous f) :
    BddAbove ((norm ∘ fun w : ℂ => f w⁻¹) '' verticalClosedStrip (1 / 4) (3 / 4)) := by
  refine ((isCompact_closedBall (0 : ℂ) 4).bddAbove_image hf.norm.continuousOn).mono ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w⁻¹, mem_closedBall_zero_iff.mpr (inv_norm_le_four hw), rfl⟩

private theorem strip_inversion_diffContOnCl {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    DiffContOnCl ℂ (fun w : ℂ => f w⁻¹) (verticalStrip (1 / 4) (3 / 4)) := by
  have hdiff (w : ℂ) (hw : 0 < w.re) : DifferentiableAt ℂ (fun w : ℂ => f w⁻¹) w := by
    have hne : w ≠ 0 := by
      rintro rfl
      simp at hw
    exact (hf w⁻¹).comp w (differentiableAt_inv hne)
  refine ⟨?_, ?_⟩
  · intro w hw
    exact (hdiff w ((by norm_num : (0 : ℝ) < 1 / 4).trans hw.1)).differentiableWithinAt
  · have hcl : closure (verticalStrip (1 / 4) (3 / 4)) ⊆
        verticalClosedStrip (1 / 4) (3 / 4) :=
      closure_minimal (fun _ hw => ⟨hw.1.le, hw.2.le⟩) (isClosed_Icc.preimage continuous_re)
    intro w hw
    have hw' : 0 < w.re := (by norm_num : (0 : ℝ) < 1 / 4).trans_le (hcl hw).1
    exact (hdiff w hw').continuousAt.continuousWithinAt

private theorem on_line_inv_circle {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hw : w.re = 1 / (2 * r)) : ‖w⁻¹ - (r : ℂ)‖ = r := by
  have hne : w ≠ 0 := by
    rintro rfl
    have hpos : (0 : ℝ) < 1 / (2 * r) := by positivity
    exact hpos.ne' (by simpa using hw.symm)
  exact (mem_circle_iff_inv_re hr (inv_ne_zero hne)).mpr (by simpa only [inv_inv] using hw)

/-- **A three-circles inequality for circles tangent at the origin.** Let
$f:\mathbb{C}\to\mathbb{C}$ be an entire function and, for $r>0$, let
\[
A(r)=\sup\{\lvert f(z)\rvert:\lvert z-r\rvert=r\}.
\]
Then
\[
A(1)^{2}\le A(2)\,A\!\left(\frac{2}{3}\right).
\]

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_99.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem sq_sSup_norm_circle_one_le_mul
  (f : ℂ → ℂ) (hentire : Differentiable ℂ f)
  (A : ℝ → ℝ) (hA_def : ∀ r : ℝ, 0 < r → A r = sSup {t : ℝ | ∃ z : ℂ, ‖z - r‖ = r ∧ t = ‖f z‖}) :
  A 1 ^ 2 ≤ A 2 * A (2 / 3 : ℝ) := by
  have hc := hentire.continuous
  have hz (r : ℝ) (hr : 0 < r) : ‖(0 : ℂ) - (r : ℂ)‖ = r := by
    simp [Real.norm_of_nonneg hr.le]
  have hzero (r : ℝ) (hr : 0 < r) : ‖f 0‖ ≤ A r := circle_value_le hc hA_def hr (hz r hr)
  have h2 := hzero 2 (by norm_num)
  have h23 := hzero (2 / 3) (by norm_num)
  have hA2 := (norm_nonneg (f 0)).trans h2
  have hA23 := (norm_nonneg (f 0)).trans h23
  have hzero_sq : ‖f 0‖ ^ 2 ≤ A 2 * A (2 / 3) := by
    rw [pow_two]
    exact mul_le_mul h2 h23 (norm_nonneg _) hA2
  have hbound (z : ℂ) (hcircle : ‖z - (1 : ℂ)‖ = 1) : ‖f z‖ ≤ √(A 2 * A (2 / 3)) := by
    by_cases hne : z = 0
    · rw [hne]
      exact Real.le_sqrt_of_sq_le hzero_sq
    have hre : (z⁻¹).re = 1 / 2 := by
      simpa using (mem_circle_iff_inv_re (r := 1) one_pos hne).mp (by simpa using hcircle)
    have hmem : z⁻¹ ∈ verticalClosedStrip (1 / 4) (3 / 4) := by
      change 1 / 4 ≤ (z⁻¹).re ∧ (z⁻¹).re ≤ 3 / 4
      rw [hre]
      norm_num
    have hbL (w : ℂ) (hw : w ∈ re ⁻¹' ({1 / 4} : Set ℝ)) : ‖f w⁻¹‖ ≤ A 2 := by
      change w.re = 1 / 4 at hw
      apply circle_value_le hc hA_def (by norm_num : (0 : ℝ) < 2)
      apply on_line_inv_circle (by norm_num)
      rw [hw]
      norm_num
    have hbU (w : ℂ) (hw : w ∈ re ⁻¹' ({3 / 4} : Set ℝ)) : ‖f w⁻¹‖ ≤ A (2 / 3) := by
      change w.re = 3 / 4 at hw
      apply circle_value_le hc hA_def (by norm_num : (0 : ℝ) < 2 / 3)
      apply on_line_inv_circle (by norm_num)
      rw [hw]
      norm_num
    have h := norm_le_interp_of_mem_verticalClosedStrip' (f := fun w : ℂ => f w⁻¹)
      (by norm_num) hmem (strip_inversion_diffContOnCl hentire) (strip_inversion_bdd hc) hbL hbU
    rw [inv_inv, hre] at h
    have hr : ((1 / 2 : ℝ) - 1 / 4) / (3 / 4 - 1 / 4) = 1 / 2 := by norm_num
    rw [hr, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hA2] at h
    exact h
  have hsup : A 1 ≤ √(A 2 * A (2 / 3)) := by
    rw [hA_def 1 one_pos]
    refine csSup_le ⟨‖f 0‖, 0, hz 1 one_pos, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hbound z (by simpa using hz)
  exact (Real.le_sqrt ((norm_nonneg (f 0)).trans (hzero 1 one_pos))
    (mul_nonneg hA2 hA23)).mp hsup

end MathlibExt.Analysis.Complex.SupOnTangentCirclesLogConvexWanted
