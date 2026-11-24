/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Continuous and holomorphic off the coordinate axes implies entire

The following OpenBMB notice applies to the adapted statement, axis definitions, and
their documentation.

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_27.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. In the original ATLAS import,
changes included converting
`theorem ma_proofbench_l1_27 … := by sorry` into the Batteries `theorem_wanted`
`differentiable_of_continuous_of_differentiableOn_compl_coordAxes`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.ContinuousHolomorphicOffAxesEntireWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions.
This change proves the theorem, moves the axis definitions, and narrows the imports.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Removability of the coordinate axes for continuous holomorphic functions

Cauchy–Goursat on rectangles with one corner at zero makes the two coordinate path
integrals agree. Continuity controls the error of the primitive along a short path,
so it has the given function as its complex derivative everywhere.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Asymptotics
open scoped Interval Topology

namespace MathlibExt.Analysis.Complex.ContinuousHolomorphicOffAxesEntireWanted

/-- **Real axis.** The real axis is the set $\{z \in \mathbb{C} : \operatorname{Im} z = 0\}$. -/
def realAxis : Set ℂ := {z : ℂ | z.im = 0}

/-- **Imaginary axis.** The imaginary axis is the set
$\{z \in \mathbb{C} : \operatorname{Re} z = 0\}$. -/
def imagAxis : Set ℂ := {z : ℂ | z.re = 0}

/-- **Coordinate axes.** The coordinate axes of $\mathbb{C}$: the union of the real axis and the
imaginary axis. -/
def coordAxes : Set ℂ := realAxis ∪ imagAxis

private def point (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

private theorem point_re (x y : ℝ) : (point x y).re = x := by simp [point, Complex.mul_re]
private theorem point_im (x y : ℝ) : (point x y).im = y := by simp [point, Complex.mul_im]

private noncomputable def horiz (f : ℂ → ℂ) (y a b : ℝ) : ℂ :=
  ∫ t in a..b, f (point t y)

private noncomputable def vert (f : ℂ → ℂ) (x a b : ℝ) : ℂ :=
  ∫ t in a..b, f (point x t)

private theorem continuous_horiz (f : ℂ → ℂ) (hc : Continuous f) (y : ℝ) :
    Continuous (fun t ↦ f (point t y)) := by
  dsimp only [point]
  fun_prop

private theorem continuous_vert (f : ℂ → ℂ) (hc : Continuous f) (x : ℝ) :
    Continuous (fun t ↦ f (point x t)) := by
  dsimp only [point]
  fun_prop

private theorem zero_notMem_Ioo_origin (x : ℝ) : (0 : ℝ) ∉ Ioo (min 0 x) (max 0 x) := by
  intro h
  rcases le_total 0 x with hx | hx
  · exact (lt_irrefl (0 : ℝ)) (by simpa only [min_eq_left hx] using h.1)
  · exact (lt_irrefl (0 : ℝ)) (by simpa only [max_eq_left hx] using h.2)

private theorem origin_rect {f : ℂ → ℂ} (hc : Continuous f)
    (h : DifferentiableOn ℂ f {z : ℂ | z.re ≠ 0 ∧ z.im ≠ 0}) (x y : ℝ) :
    horiz f 0 0 x + I * vert f x 0 y = I * vert f 0 0 y + horiz f y 0 x := by
  -- A rectangle based at zero has no point of either axis in its interior.
  have hD : DifferentiableOn ℂ f
      (Ioo (min (0 : ℂ).re (point x y).re) (max (0 : ℂ).re (point x y).re) ×ℂ
        Ioo (min (0 : ℂ).im (point x y).im) (max (0 : ℂ).im (point x y).im)) := by
    refine h.mono ?_
    intro z hz
    have hx : z.re ∈ Ioo (min 0 x) (max 0 x) := by
      simpa only [zero_re, point_re] using (mem_reProdIm.mp hz).1
    have hy : z.im ∈ Ioo (min 0 y) (max 0 y) := by
      simpa only [zero_im, point_im] using (mem_reProdIm.mp hz).2
    exact ⟨fun he ↦ zero_notMem_Ioo_origin x (he ▸ hx),
      fun he ↦ zero_notMem_Ioo_origin y (he ▸ hy)⟩
  have he := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f 0 (point x y) hc.continuousOn hD
  simp only [zero_re, zero_im, point_re, point_im, smul_eq_mul] at he
  change horiz f 0 0 x - horiz f y 0 x + I * vert f x 0 y - I * vert f 0 0 y = 0 at he
  linear_combination he

private noncomputable def primitive (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  horiz f 0 0 z.re + I * vert f z.re 0 z.im

private theorem primitive_sub {f : ℂ → ℂ} (hc : Continuous f)
    (h : DifferentiableOn ℂ f {z : ℂ | z.re ≠ 0 ∧ z.im ≠ 0}) (z w : ℂ) :
    primitive f w - primitive f z = horiz f z.im z.re w.re + I * vert f w.re z.im w.im := by
  have hv := intervalIntegral.integral_interval_sub_left (μ := volume)
    ((continuous_vert f hc w.re).intervalIntegrable 0 w.im)
    ((continuous_vert f hc w.re).intervalIntegrable 0 z.im)
  have hh := intervalIntegral.integral_interval_sub_left (μ := volume)
    ((continuous_horiz f hc z.im).intervalIntegrable 0 w.re)
    ((continuous_horiz f hc z.im).intervalIntegrable 0 z.re)
  change vert f w.re 0 w.im - vert f w.re 0 z.im = vert f w.re z.im w.im at hv
  change horiz f z.im 0 w.re - horiz f z.im 0 z.re = horiz f z.im z.re w.re at hh
  -- Use the two path orders at the intermediate point `(w.re, z.im)`.
  have hw := origin_rect hc h w.re z.im
  have hz := origin_rect hc h z.re z.im
  dsimp only [primitive]
  rw [← hv, ← hh]
  linear_combination hw - hz

private theorem norm_point_sub_le (x y : ℝ) (z : ℂ) :
    ‖point x y - z‖ ≤ |x - z.re| + |y - z.im| := by
  simpa only [sub_re, sub_im, point_re, point_im] using
    Complex.norm_le_abs_re_add_abs_im (point x y - z)

private theorem abs_sub_le_interval {a b t : ℝ} (ht : t ∈ Ι a b) : |t - a| ≤ |b - a| := by
  rcases mem_uIcc.mp (uIoc_subset_uIcc ht) with ⟨hat, htb⟩ | ⟨hbt, hta⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hat), abs_of_nonneg (sub_nonneg.mpr (hat.trans htb))]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hta), abs_of_nonpos (sub_nonpos.mpr (hbt.trans hta))]
    linarith

private theorem primitive_hasDerivAt {f : ℂ → ℂ} (hc : Continuous f)
    (h : DifferentiableOn ℂ f {z : ℂ | z.re ≠ 0 ∧ z.im ≠ 0}) (z : ℂ) :
    HasDerivAt (primitive f) (f z) z := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hc.continuousAt (ε / 2) (by positivity)
  have hball : Metric.ball z (δ / 3) ∈ 𝓝 z :=
    Metric.ball_mem_nhds z (div_pos hδ (by norm_num))
  filter_upwards [hball] with w hw
  have hw' : ‖w - z‖ < δ / 3 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hr : |w.re - z.re| ≤ ‖w - z‖ := by
    simpa only [sub_re] using abs_re_le_norm (w - z)
  have hi : |w.im - z.im| ≤ ‖w - z‖ := by
    simpa only [sub_im] using abs_im_le_norm (w - z)
  -- Subtract the constant integrand `f z` on both legs to bound the derivative error.
  let g (u : ℂ) := f u - f z
  have hbound (u : ℂ) (hu : ‖u - z‖ < δ) : ‖g u‖ ≤ ε / 2 := by
    have hh := hcont (x := u) (by simpa only [dist_eq_norm] using hu)
    exact (by simpa only [dist_eq_norm, g] using hh.le)
  have hH : ‖horiz g z.im z.re w.re‖ ≤ (ε / 2) * |w.re - z.re| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    refine hbound _ ((norm_point_sub_le t z.im z).trans_lt ?_)
    have ht' := abs_sub_le_interval ht
    rw [sub_self, abs_zero, add_zero]
    linarith
  have hV : ‖vert g w.re z.im w.im‖ ≤ (ε / 2) * |w.im - z.im| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    refine hbound _ ((norm_point_sub_le w.re t z).trans_lt ?_)
    have ht' := abs_sub_le_interval ht
    linarith
  have hHsub : horiz g z.im z.re w.re =
      horiz f z.im z.re w.re - ((w.re - z.re : ℝ) : ℂ) * f z := by
    dsimp only [horiz, g]
    rw [intervalIntegral.integral_sub ((continuous_horiz f hc _).intervalIntegrable _ _)
      (intervalIntegrable_const (c := f z)), intervalIntegral.integral_const]
    rfl
  have hVsub : vert g w.re z.im w.im =
      vert f w.re z.im w.im - ((w.im - z.im : ℝ) : ℂ) * f z := by
    dsimp only [vert, g]
    rw [intervalIntegral.integral_sub ((continuous_vert f hc _).intervalIntegrable _ _)
      (intervalIntegrable_const (c := f z)), intervalIntegral.integral_const]
    rfl
  have hlin : w - z = ((w.re - z.re : ℝ) : ℂ) + ((w.im - z.im : ℝ) : ℂ) * I := by
    simpa only [sub_re, sub_im] using (re_add_im (w - z)).symm
  have heq : primitive f w - primitive f z - (w - z) • f z =
      horiz g z.im z.re w.re + I * vert g w.re z.im w.im := by
    rw [primitive_sub hc h z w, hHsub, hVsub, smul_eq_mul, hlin]
    ring
  change ‖primitive f w - primitive f z - (w - z) • f z‖ ≤ ε * ‖w - z‖
  rw [heq]
  calc
    _ ≤ ‖horiz g z.im z.re w.re‖ + ‖vert g w.re z.im w.im‖ := by
      simpa only [norm_mul, norm_I, one_mul] using
        norm_add_le (horiz g z.im z.re w.re) (I * vert g w.re z.im w.im)
    _ ≤ (ε / 2) * |w.re - z.re| + (ε / 2) * |w.im - z.im| := add_le_add hH hV
    _ ≤ ε * ‖w - z‖ := by
      have hp : 0 ≤ ε / 2 := by positivity
      linarith [mul_le_mul_of_nonneg_left hr hp, mul_le_mul_of_nonneg_left hi hp]

/-- **Continuous functions holomorphic off the coordinate axes are entire.** Let
$f : \mathbb{C} \to \mathbb{C}$ be continuous on all of $\mathbb{C}$ and holomorphic on the
complement of the coordinate axes. Then $f$ is holomorphic on all of $\mathbb{C}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_27.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem differentiable_of_continuous_of_differentiableOn_compl_coordAxes
    (f : ℂ → ℂ) (hc : Continuous f) (hhol : DifferentiableOn ℂ f (coordAxesᶜ)) :
    Differentiable ℂ f := by
  have h : DifferentiableOn ℂ f {z : ℂ | z.re ≠ 0 ∧ z.im ≠ 0} := by
    refine hhol.mono ?_
    intro z hz
    exact not_or_intro hz.2 hz.1
  have hd : Differentiable ℂ (primitive f) := fun z ↦ (primitive_hasDerivAt hc h z).differentiableAt
  have hf : deriv (primitive f) = f := funext fun z ↦ (primitive_hasDerivAt hc h z).deriv
  simpa only [hf] using hd.deriv

end MathlibExt.Analysis.Complex.ContinuousHolomorphicOffAxesEntireWanted
