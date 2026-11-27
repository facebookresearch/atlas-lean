/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
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

Attribution and modification notice: the statement is adapted from openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_86.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; also distributed in the Hugging Face dataset
openbmb/MA-ProofBench), under the MIT license above. The ATLAS import converted the statement to
`theorem_wanted`, named it in the namespace below, and documented the disk abbreviation.
This file preserves the statement, abbreviation and audited docstrings, supplies a proof, and
narrows the imports.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Growth of holomorphic maps into a vertical strip

The exponential and the Cayley map send the strip into the disk. Schwarz's lemma bounds the disk
coordinate, and integration of the difference of the two logarithms along a radius bounds the
inverse map by the exact real logarithmic ratio.
-/

open Complex Set Metric
open scoped Interval

noncomputable section

@[expose] public section

namespace MathlibExt.Analysis.Complex.StripBoundedHolomorphicGrowthWanted

private def stripExponent (w : ℂ) : ℂ := ((Real.pi / 2 : ℝ) : ℂ) * (Complex.I * w)

private def cayley (q : ℂ) : ℂ := (q - 1) / (q + 1)

private theorem stripExponent_im (w : ℂ) : (stripExponent w).im = Real.pi / 2 * w.re := by
  simp [stripExponent, Complex.mul_im, Complex.mul_re]

private theorem stripExponent_abs_im {w : ℂ} (hw : |w.re| < 1) :
    |(stripExponent w).im| < Real.pi / 2 := by
  have hp : 0 < Real.pi / 2 := by positivity
  rw [stripExponent_im, abs_mul, abs_of_pos hp]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hw hp

private theorem exp_strip_re_pos {w : ℂ} (hw : |w.re| < 1) :
    0 < (Complex.exp (stripExponent w)).re := by
  have hi := abs_lt.mp (stripExponent_abs_im hw)
  rw [Complex.exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  exact ⟨by linarith [hi.1], hi.2⟩

private theorem add_one_ne_zero_of_re_pos {q : ℂ} (hq : 0 < q.re) : q + 1 ≠ 0 := by
  intro he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
  linarith

private theorem norm_cayley_lt_one {q : ℂ} (hq : 0 < q.re) : ‖cayley q‖ < 1 := by
  rw [cayley, norm_div, div_lt_iff₀ (norm_pos_iff.mpr (add_one_ne_zero_of_re_pos hq)), one_mul]
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
    Complex.one_re, Complex.one_im, sub_zero, add_zero]
  nlinarith

private theorem cayley_schwarz {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (h0 : g 0 = 0)
    (hRe : ∀ z ∈ ball (0 : ℂ) 1, |(g z).re| < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖cayley (Complex.exp (stripExponent (g z)))‖ ≤ ‖z‖ := by
  let e (y : ℂ) := Complex.exp (stripExponent (g y))
  let f (y : ℂ) := cayley (e y)
  have hi : DifferentiableOn ℂ (fun y => Complex.I * g y) (ball 0 1) :=
    (differentiableOn_const Complex.I).mul hg
  have he : DifferentiableOn ℂ e (ball 0 1) :=
    ((differentiableOn_const ((Real.pi / 2 : ℝ) : ℂ)).mul hi).cexp
  have hone : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) (ball 0 1) := differentiableOn_const _
  have hf : DifferentiableOn ℂ f (ball 0 1) :=
    (he.sub hone).div (he.add hone)
      (fun y hy => add_one_ne_zero_of_re_pos (exp_strip_re_pos (hRe y hy)))
  have hm : MapsTo f (ball 0 1) (closedBall 0 1) := by
    intro y hy
    exact mem_closedBall_zero_iff.mpr (norm_cayley_lt_one (exp_strip_re_pos (hRe y hy))).le
  have hf0 : f 0 = 0 := by simp [f, e, cayley, stripExponent, h0]
  exact Complex.norm_le_norm_of_mapsTo_ball hf hm hf0 (mem_ball_zero_iff.mp hz)

private theorem cayley_inverse {q : ℂ} (hq : 0 < q.re) :
    (1 + cayley q) / (1 - cayley q) = q := by
  have h1 : 1 - cayley q ≠ 0 := by
    intro h
    have hc : cayley q = 1 := sub_eq_zero.mp h |>.symm
    have := norm_cayley_lt_one hq
    rw [hc, norm_one] at this
    exact lt_irrefl _ this
  apply (div_eq_iff h1).mpr
  rw [cayley]
  field_simp [add_one_ne_zero_of_re_pos hq]
  ring

private theorem stripExponent_eq_log_difference {w : ℂ} (hw : |w.re| < 1) :
    stripExponent w =
      Complex.log (1 + cayley (Complex.exp (stripExponent w))) -
        Complex.log (1 - cayley (Complex.exp (stripExponent w))) := by
  let T := stripExponent w
  let q := Complex.exp T
  let a := cayley q
  have hq : 0 < q.re := exp_strip_re_pos hw
  have ha : ‖a‖ < 1 := norm_cayley_lt_one hq
  have har := Complex.abs_re_le_norm a
  have hpa : 0 < (1 + a).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith [neg_abs_le a.re]
  have hma : 0 < (1 - a).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [le_abs_self a.re]
  have hp : |(Complex.log (1 + a)).im| < Real.pi / 2 := by
    rw [Complex.log_im]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpa)
  have hm : |(Complex.log (1 - a)).im| < Real.pi / 2 := by
    rw [Complex.log_im]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hma)
  have h1 : 1 + a ≠ 0 := fun h => hpa.ne' (by rw [h, Complex.zero_re])
  have h2 : 1 - a ≠ 0 := fun h => hma.ne' (by rw [h, Complex.zero_re])
  have hexp : Complex.exp (Complex.log (1 + a) - Complex.log (1 - a)) = q := by
    rw [Complex.exp_sub, Complex.exp_log h1, Complex.exp_log h2]
    exact cayley_inverse hq
  have hTi := abs_lt.mp (stripExponent_abs_im hw)
  have hl := abs_lt.mp hp
  have hr := abs_lt.mp hm
  have hπ := Real.pi_pos
  change T = Complex.log (1 + a) - Complex.log (1 - a)
  calc
    T = Complex.log q := (Complex.log_exp (by change -Real.pi < (stripExponent w).im; linarith)
      (by change (stripExponent w).im ≤ Real.pi; linarith)).symm
    _ = Complex.log (Complex.exp (Complex.log (1 + a) - Complex.log (1 - a))) :=
      congrArg _ hexp.symm
    _ = _ := Complex.log_exp (by rw [Complex.sub_im]; linarith) (by rw [Complex.sub_im]; linarith)

/-- The inverse Cayley logarithm is bounded by its restriction to the positive radius. -/
private theorem norm_log_difference_le {a : ℂ} (ha : ‖a‖ < 1) :
    ‖Complex.log (1 + a) - Complex.log (1 - a)‖ ≤
      Real.log ((1 + ‖a‖) / (1 - ‖a‖)) := by
  let r := ‖a‖
  let f (t : ℝ) := a * ((1 + t • a)⁻¹ + (1 - t • a)⁻¹)
  let m (t : ℝ) := r * ((1 + t * r)⁻¹ + (1 - t * r)⁻¹)
  have hr0 : 0 ≤ r := norm_nonneg a
  have hr1 : r < 1 := ha
  have htr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ t * r ∧ t * r < 1 :=
    ⟨mul_nonneg ht.1 hr0, (mul_le_of_le_one_left hr0 ht.2).trans_lt hr1⟩
  have ha' : ‖-a‖ < 1 := by simpa only [norm_neg] using ha
  have hp := Complex.mem_slitPlane_of_norm_lt_one ha
  have hm : 1 - a ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one ha'
  have hPlus : ContinuousOn (fun t : ℝ => (1 + t • a)⁻¹) (Icc 0 1) :=
    Complex.continuousOn_one_add_mul_inv hp
  have hMinus : ContinuousOn (fun t : ℝ => (1 - t • a)⁻¹) (Icc 0 1) := by
    simpa only [sub_eq_add_neg, smul_neg] using
      Complex.continuousOn_one_add_mul_inv (Complex.mem_slitPlane_of_norm_lt_one ha')
  have hF : ContinuousOn f (Icc 0 1) := continuousOn_const.mul (hPlus.add hMinus)
  have hpC : ContinuousOn (fun t : ℝ => 1 + t * r) (Icc 0 1) := by fun_prop
  have hmC : ContinuousOn (fun t : ℝ => 1 - t * r) (Icc 0 1) := by fun_prop
  have hp0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 1 + t * r ≠ 0 :=
    ne_of_gt (by linarith [(htr t ht).1])
  have hm0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 1 - t * r ≠ 0 :=
    ne_of_gt (by linarith [(htr t ht).2])
  have hM : ContinuousOn m (Icc 0 1) :=
    continuousOn_const.mul ((hpC.inv₀ hp0).add (hmC.inv₀ hm0))
  have hFInt : IntervalIntegrable f MeasureTheory.volume 0 1 :=
    (by rwa [uIcc_of_le zero_le_one] : ContinuousOn f (uIcc 0 1)).intervalIntegrable
  have hMInt : IntervalIntegrable m MeasureTheory.volume 0 1 :=
    (by rwa [uIcc_of_le zero_le_one] : ContinuousOn m (uIcc 0 1)).intervalIntegrable
  have hPlusInt : IntervalIntegrable (fun t : ℝ => (1 + t • a)⁻¹) MeasureTheory.volume 0 1 :=
    (by rwa [uIcc_of_le zero_le_one] : ContinuousOn (fun t : ℝ => (1 + t • a)⁻¹)
      (uIcc 0 1)).intervalIntegrable
  have hMinusInt : IntervalIntegrable (fun t : ℝ => (1 - t • a)⁻¹) MeasureTheory.volume 0 1 :=
    (by rwa [uIcc_of_le zero_le_one] : ContinuousOn (fun t : ℝ => (1 - t • a)⁻¹)
      (uIcc 0 1)).intervalIntegrable
  have hL : Complex.log (1 + a) - Complex.log (1 - a) = ∫ t in (0 : ℝ)..1, f t := by
    have hn : Complex.log (1 - a) = (-a) * ∫ t in (0 : ℝ)..1, (1 - t • a)⁻¹ := by
      simpa only [smul_neg, ← sub_eq_add_neg] using
        Complex.log_eq_integral (z := -a) (Complex.mem_slitPlane_of_norm_lt_one ha')
    rw [Complex.log_eq_integral hp, hn]
    rw [show (∫ t in (0 : ℝ)..1, f t) =
        a * ∫ t in (0 : ℝ)..1, (1 + t • a)⁻¹ + (1 - t • a)⁻¹ from
          intervalIntegral.integral_const_mul a (fun t : ℝ => (1 + t • a)⁻¹ + (1 - t • a)⁻¹)]
    rw [intervalIntegral.integral_add hPlusInt hMinusInt, mul_add]
    ring
  have hFle (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖f t‖ ≤ m t := by
    let z := t • a
    have hz : ‖z‖ = t * r := by rw [norm_smul, Real.norm_of_nonneg ht.1]
    have hz1 : ‖z‖ < 1 := hz.trans_lt (htr t ht).2
    have hzp : 1 + z ≠ 0 := Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hz1)
    have hzm : 1 - z ≠ 0 := by
      have hh : ‖-z‖ < 1 := by simpa only [norm_neg] using hz1
      rw [sub_eq_add_neg]
      exact Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hh)
    have hzsq : (1 : ℂ) - z ^ 2 = (1 + z) * (1 - z) := by ring
    have hsum : (1 + z)⁻¹ + (1 - z)⁻¹ = 2 / (1 - z ^ 2) := by
      rw [hzsq]
      field_simp [hzp, hzm]
      ring
    have hd0 : 0 < 1 - (t * r) ^ 2 := by nlinarith [(htr t ht).1, (htr t ht).2]
    have hd : 1 - (t * r) ^ 2 ≤ ‖(1 : ℂ) - z ^ 2‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (z ^ (2 : ℕ))
      rw [norm_one, pow_two z, norm_mul, hz, ← pow_two (t * r)] at h
      simpa only [pow_two] using h
    have hrp : 0 < 1 + t * r := by linarith [(htr t ht).1]
    have hrm : 0 < 1 - t * r := by linarith [(htr t ht).2]
    have hsumR : (1 + t * r)⁻¹ + (1 - t * r)⁻¹ = 2 / (1 - (t * r) ^ 2) := by
      rw [show 1 - (t * r) ^ 2 = (1 + t * r) * (1 - t * r) by ring]
      field_simp [hrp.ne', hrm.ne']
      ring
    change ‖a * ((1 + z)⁻¹ + (1 - z)⁻¹)‖ ≤ r * ((1 + t * r)⁻¹ + (1 - t * r)⁻¹)
    rw [hsum, hsumR, norm_mul, norm_div, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num) hd0 hd) hr0
  have hEval : (∫ t in (0 : ℝ)..1, m t) = Real.log ((1 + r) / (1 - r)) := by
    let M (t : ℝ) := Real.log (1 + t * r) - Real.log (1 - t * r)
    have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : HasDerivAt M (m t) t := by
      rw [uIcc_of_le zero_le_one] at ht
      have h1 : 0 < 1 + t * r := by linarith [(htr t ht).1]
      have h2 : 0 < 1 - t * r := by linarith [(htr t ht).2]
      have htr' : HasDerivAt (fun s : ℝ => s * r) r t := by
        simpa only [id_eq, one_mul] using (hasDerivAt_id t).mul_const r
      have hd1 := ((hasDerivAt_const t (1 : ℝ)).add htr').log h1.ne'
      have hd2 := ((hasDerivAt_const t (1 : ℝ)).sub htr').log h2.ne'
      have hdsub := hd1.sub hd2
      simp only [Pi.add_apply, Pi.sub_apply, zero_add, zero_sub] at hdsub
      change HasDerivAt M (r / (1 + t * r) - (-r) / (1 - t * r)) t at hdsub
      convert hdsub using 1
      dsimp only [m]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hMInt]
    simp only [M, one_mul, zero_mul, add_zero, sub_zero, Real.log_one, sub_self]
    rw [Real.log_div (by linarith : 1 + r ≠ 0) (by linarith : 1 - r ≠ 0)]
  rw [hL, ← hEval]
  exact (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans
    (intervalIntegral.integral_mono_on zero_le_one hFInt.norm hMInt hFle)

/-- **The open unit disc $D$.** The set $D=\{z\in\mathbb{C}:|z|<1\}$ is the open disc of radius $1$
about $0$. -/
noncomputable abbrev D : Set ℂ := Metric.ball (0 : ℂ) 1

/-- **Growth bound for holomorphic maps from the unit disc into a vertical strip.** Let
$D=\{z:|z|<1\}\subset\mathbb{C}$ be the unit disk and $g:D\to\mathbb{C}$ be a holomorphic
function such that $g(0)=0$ and $|\operatorname{Re} g(z)|<1$ for any $z\in D$. Then for any
$z\in D$,
\[
|g(z)|\le \frac{2}{\pi}\log\frac{1+|z|}{1-|z|}.
\]

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_86.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem norm_le_two_div_pi_mul_log_of_abs_re_lt_one
  (g : ℂ → ℂ)
  (hg_holo : DifferentiableOn ℂ g D)
  (hg0 : g 0 = 0)
  (hRe : ∀ z : ℂ, z ∈ D → |(Complex.re (g z))| < 1) :
  ∀ z : ℂ,
    z ∈ D →
      ‖g z‖ ≤ (2 / Real.pi) * Real.log ((1 + ‖z‖) / (1 - ‖z‖)) := by
  intro z hz
  let a := cayley (Complex.exp (stripExponent (g z)))
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have haz : ‖a‖ ≤ ‖z‖ := cayley_schwarz hg_holo hg0 hRe hz
  have ha1 : ‖a‖ < 1 := haz.trans_lt hz1
  have hratio : (1 + ‖a‖) / (1 - ‖a‖) ≤ (1 + ‖z‖) / (1 - ‖z‖) := by
    apply (div_le_div_iff₀ (sub_pos.mpr ha1) (sub_pos.mpr hz1)).mpr
    nlinarith [haz]
  have hlog := Real.log_le_log (div_pos (by positivity : 0 < 1 + ‖a‖) (sub_pos.mpr ha1)) hratio
  have hb := (norm_log_difference_le ha1).trans hlog
  have hinv : stripExponent (g z) = Complex.log (1 + a) - Complex.log (1 - a) :=
    stripExponent_eq_log_difference (hRe z hz)
  rw [← hinv] at hb
  have hπ : 0 < Real.pi / 2 := by positivity
  have hnorm : ‖stripExponent (g z)‖ = (Real.pi / 2) * ‖g z‖ := by
    rw [stripExponent, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_of_nonneg hπ.le]
  rw [hnorm] at hb
  calc
    ‖g z‖ ≤ Real.log ((1 + ‖z‖) / (1 - ‖z‖)) / (Real.pi / 2) :=
      (le_div_iff₀ hπ).mpr (by simpa only [mul_comm] using hb)
    _ = (2 / Real.pi) * Real.log ((1 + ‖z‖) / (1 - ‖z‖)) := by
      field_simp [Real.pi_pos.ne']

end MathlibExt.Analysis.Complex.StripBoundedHolomorphicGrowthWanted
