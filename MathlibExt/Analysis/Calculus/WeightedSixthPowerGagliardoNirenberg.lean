/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Weighted L^6 bound with a slowly varying weight

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_67.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_67 … := by sorry` into the Batteries `theorem_wanted`
`exists_integral_pow_six_mul_weight_le`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.WeightedSixthPowerGagliardoNirenbergWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A weighted sixth-power Gagliardo–Nirenberg bound

The supremum of `u² √θ` is bounded by integrating its derivative from outside the
support of `u` and applying Cauchy–Schwarz. Squaring this bound and integrating
against `u²` gives the weighted sixth-power inequality.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Interval Topology

namespace MathlibExt.Analysis.Calculus.WeightedSixthPowerGagliardoNirenbergWanted

private theorem integral_norm_rpow_two (f : ℝ → ℝ) :
    (∫ x, ‖f x‖ ^ (2 : ℝ)) = ∫ x, f x ^ (2 : ℕ) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    calc
      ‖f x‖ ^ (2 : ℝ) = ‖f x‖ ^ (2 : ℕ) := by
        simpa only [Nat.cast_ofNat] using Real.rpow_natCast ‖f x‖ 2
      _ = f x ^ (2 : ℕ) := by rw [Real.norm_eq_abs, sq_abs]

private theorem integrable_compact_pow_mul {f h : ℝ → ℝ} (hf : Continuous f)
    (hh : Continuous h) (hK : HasCompactSupport f) {n : ℕ} (hn : n ≠ 0) :
    Integrable (fun x ↦ f x ^ n * h x) volume := by
  have hc : Continuous (fun x ↦ f x ^ n) := by fun_prop
  have hk : HasCompactSupport (fun x ↦ f x ^ n) :=
    hK.comp_left (g := fun y : ℝ ↦ y ^ n) (zero_pow hn)
  have hmul : HasCompactSupport (fun x ↦ f x ^ n * h x) := hk.mul_right
  exact (hc.mul hh).integrable_of_hasCompactSupport hmul

/-- **A weighted $L^6$ bound with a slowly varying weight.** There is a constant $C > 0$ with the
following property. Let $\theta : \mathbb{R} \to \mathbb{R}$ be continuously differentiable, with
$\theta(x) > 0$ for every $x$ and $\|\theta'/\theta\|_{L^\infty(\mathbb{R})} \le 1$, and let
$u : \mathbb{R} \to \mathbb{R}$ be smooth with compact support. Then
$$\int_{\mathbb{R}} u(x)^6\,\theta(x)\,dx \le C\,\|u\|_{L^2(\mathbb{R})}^4
\int_{\mathbb{R}} \left(|u'(x)|^2 + |u(x)|^2\right)\theta(x)\,dx.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities
in real analysis), `benchmark/level2/ma_proofbench_l2_67.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exists_integral_pow_six_mul_weight_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (θ : ℝ → ℝ), (∀ x : ℝ, 0 < θ x) → ContDiff ℝ 1 θ →
        eLpNorm (fun x : ℝ => deriv θ x / θ x) ⊤ volume ≤ 1 →
        ∀ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
          ∫ x : ℝ, (u x) ^ (6 : ℕ) * θ x ≤
            C * (ENNReal.toReal (eLpNorm u 2 volume)) ^ (4 : ℕ) *
              ∫ x : ℝ, (|deriv u x| ^ (2 : ℕ) + |u x| ^ (2 : ℕ)) * θ x := by
  refine ⟨5, by norm_num, ?_⟩
  intro θ hθ hθC hLogBound u hu huK
  have hu₂ : ContDiff ℝ 2 u := hu.of_le (by simp)
  have huC := hu₂.continuous
  have hθc := hθC.continuous
  have hud := hu₂.differentiable (by norm_num)
  have hθd := hθC.differentiable (by norm_num)
  have hudC : Continuous (deriv u) := hu₂.continuous_deriv (by norm_num)
  have hθdC : Continuous (deriv θ) := hθC.continuous_deriv_one
  let s : ℝ → ℝ := Real.sqrt ∘ θ
  have hsC : Continuous s := Real.continuous_sqrt.comp hθc
  have hs0 (x : ℝ) : 0 < s x := Real.sqrt_pos.2 (hθ x)
  have hs2 (x : ℝ) : s x ^ 2 = θ x := Real.sq_sqrt (hθ x).le
  let l (x : ℝ) := deriv θ x / θ x
  have hlC : Continuous l := hθdC.div hθc (fun x ↦ (hθ x).ne')
  have hlb : ∀ᵐ x ∂volume, |l x| ≤ 1 := by
    change eLpNorm l ∞ volume ≤ 1 at hLogBound
    rw [eLpNorm_exponent_top hlC.aestronglyMeasurable] at hLogBound
    filter_upwards [ae_le_eLpNormEssSup (f := l) (μ := volume)] with x hx
    have he := ENNReal.toReal_mono (b := (1 : ℝ≥0∞)) (by simp) (hx.trans hLogBound)
    rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_one,
      Real.norm_eq_abs] at he
    exact he
  -- The square of this auxiliary function accounts for four powers of `u` and the weight.
  let g (x : ℝ) := u x ^ 2 * s x
  let g' (x : ℝ) := 2 * u x * deriv u x * s x + u x ^ 2 * (l x * s x / 2)
  have hgc' : Continuous g' := by
    dsimp [g']
    exact (((continuous_const.mul huC).mul hudC).mul hsC).add
      ((huC.pow 2).mul ((hlC.mul hsC).div_const 2))
  have hg' (x : ℝ) : HasDerivAt g (g' x) x := by
    have he : (1 / (2 * s x)) * deriv θ x = l x * s x / 2 := by
      dsimp only [l]
      rw [← hs2 x]
      field_simp [(hs0 x).ne']
    have hsd : HasDerivAt s (l x * s x / 2) x := by
      rw [← he]
      exact (Real.hasDerivAt_sqrt (hθ x).ne').comp x (hθd x).hasDerivAt
    simpa only [g, g', Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (((hud x).hasDerivAt.fun_pow 2).fun_mul hsd)
  let v (x : ℝ) := (2 * |deriv u x| + |u x| / 2) * s x
  let w (x : ℝ) := (|deriv u x| ^ 2 + |u x| ^ 2) * θ x
  have hv0 (x : ℝ) : 0 ≤ v x := by
    dsimp only [v]
    exact mul_nonneg (by positivity) (hs0 x).le
  have hg0 (x : ℝ) : 0 ≤ g x := mul_nonneg (sq_nonneg _) (hs0 x).le
  have hvC : Continuous v := ((continuous_const.mul hudC.abs).add (huC.abs.div_const 2)).mul hsC
  have hvK : HasCompactSupport v := by
    have h1 : HasCompactSupport (fun x ↦ 2 * |deriv u x|) :=
      huK.deriv.comp_left (g := fun y : ℝ ↦ 2 * |y|) (by simp)
    have h2 : HasCompactSupport (fun x ↦ |u x| / 2) :=
      huK.comp_left (g := fun y : ℝ ↦ |y| / 2) (by simp)
    exact (h1.add h2).mul_right
  have hwC : Continuous w := ((hudC.abs.pow 2).add (huC.abs.pow 2)).mul hθc
  have hwK : HasCompactSupport w := by
    have h1 : HasCompactSupport (fun x ↦ |deriv u x| ^ 2) :=
      huK.deriv.comp_left (g := fun y : ℝ ↦ |y| ^ 2) (by simp)
    have h2 : HasCompactSupport (fun x ↦ |u x| ^ 2) :=
      huK.comp_left (g := fun y : ℝ ↦ |y| ^ 2) (by simp)
    exact (h1.add h2).mul_right
  have hg_le : ∀ᵐ x ∂volume, g' x ≤ |u x| * v x := by
    filter_upwards [hlb] with x hx
    have h1 : u x * deriv u x ≤ |u x| * |deriv u x| := by
      simpa only [abs_mul] using le_abs_self (u x * deriv u x)
    have h2 : l x ≤ 1 := (le_abs_self _).trans hx
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2))
      (hs0 x).le
    have h4 := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (hs0 x).le)
        (by norm_num : (0 : ℝ) ≤ 2))
      (sq_nonneg (u x))
    calc
      g' x ≤ 2 * (|u x| * |deriv u x|) * s x + u x ^ 2 * (1 * s x / 2) := by
        simpa only [g', mul_assoc (2 : ℝ)] using add_le_add h3 h4
      _ = |u x| * v x := by dsimp only [v]; rw [← sq_abs (u x)]; ring
  have hM : Integrable (fun x ↦ |u x| * v x) volume :=
    (huC.abs.mul hvC).integrable_of_hasCompactSupport huK.abs.mul_right
  -- Start the fundamental theorem of calculus below the support of `u`.
  have hg_bound (x : ℝ) : g x ≤ ∫ t, |u t| * v t := by
    obtain ⟨b, hb⟩ := huK.isCompact.bddBelow
    let a := min x b - 1
    have hax : a ≤ x := by dsimp [a]; linarith [min_le_left x b]
    have hab : a < b := by dsimp [a]; linarith [min_le_right x b]
    have hua : u a = 0 := by
      by_contra hne
      exact hab.not_ge (hb (subset_tsupport u (show a ∈ Function.support u from hne)))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hg' t)
      (hgc'.intervalIntegrable a x)
    have hzero : g a = 0 := by simp [g, hua]
    rw [hzero, sub_zero] at hftc
    rw [← hftc]
    refine (intervalIntegral.integral_mono_ae hax (hgc'.intervalIntegrable a x)
      ((huC.abs.mul hvC).intervalIntegrable a x) hg_le).trans ?_
    rw [intervalIntegral.integral_of_le hax]
    exact setIntegral_le_integral hM (.of_forall fun t ↦ mul_nonneg (abs_nonneg _) (hv0 t))
  let A : ℝ := ∫ x, u x ^ 2
  let B : ℝ := ∫ x, w x
  let V : ℝ := ∫ x, v x ^ 2
  have hA0 : 0 ≤ A := integral_nonneg (fun x ↦ sq_nonneg _)
  have hV0 : 0 ≤ V := integral_nonneg (fun x ↦ sq_nonneg _)
  -- The two factors are in unweighted L².
  have hCS : (∫ x, |u x| * v x) ≤ Real.sqrt A * Real.sqrt V := by
    have huLp : MemLp u (ENNReal.ofReal 2) volume := huC.memLp_of_hasCompactSupport huK
    have hvLp : MemLp v (ENNReal.ofReal 2) volume := hvC.memLp_of_hasCompactSupport hvK
    have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two huLp hvLp
    rw [integral_norm_rpow_two u, integral_norm_rpow_two v, ← Real.sqrt_eq_rpow A,
      ← Real.sqrt_eq_rpow V] at hh
    calc
      (∫ x, |u x| * v x) = ∫ x, ‖u x‖ * ‖v x‖ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by
          change |u x| * v x = ‖u x‖ * ‖v x‖
          rw [Real.norm_of_nonneg (hv0 x), Real.norm_eq_abs]
      _ ≤ Real.sqrt A * Real.sqrt V := hh
  have hv2I : Integrable (fun x ↦ v x ^ 2) volume := by
    simpa only [mul_one] using
      (integrable_compact_pow_mul hvC (continuous_const (y := (1 : ℝ))) hvK
        (n := 2) (by decide))
  have hwI : Integrable w volume := hwC.integrable_of_hasCompactSupport hwK
  have hVB : V ≤ 5 * B := by
    have hle (x : ℝ) : v x ^ 2 ≤ 5 * w x := by
      have h : (2 * |deriv u x| + |u x| / 2) ^ 2 ≤
          5 * (|deriv u x| ^ 2 + |u x| ^ 2) := by
        nlinarith [sq_nonneg (|deriv u x| - |u x|), sq_nonneg |u x|]
      dsimp only [v, w]
      rw [mul_pow, hs2, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right h (hθ x).le
    have hi : Integrable (fun x ↦ 5 * w x) volume := hwI.const_mul 5
    simpa only [V, B, integral_const_mul] using integral_mono hv2I hi hle
  have hpoint (x : ℝ) : g x ^ 2 ≤ 5 * A * B := calc
    _ ≤ (Real.sqrt A * Real.sqrt V) ^ 2 :=
      (sq_le_sq₀ (hg0 x) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
        ((hg_bound x).trans hCS)
    _ = A * V := by rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hV0]
    _ ≤ 5 * A * B := by
      calc A * V ≤ A * (5 * B) := mul_le_mul_of_nonneg_left hVB hA0
      _ = 5 * A * B := by ring
  have hnorm : (eLpNorm u 2 volume).toReal ^ (2 : ℕ) = A := by
    rw [toReal_eLpNorm,
      lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp) huC.aestronglyMeasurable]
    rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, integral_norm_rpow_two,
      ← one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA0]
  have hu6I : Integrable (fun x ↦ u x ^ 6 * θ x) volume :=
    integrable_compact_pow_mul huC hθc huK (n := 6) (by decide)
  have hu2I : Integrable (fun x ↦ u x ^ 2) volume := by
    simpa only [mul_one] using
      (integrable_compact_pow_mul huC (continuous_const (y := (1 : ℝ))) huK
        (n := 2) (by decide))
  have hrI : Integrable (fun x ↦ (5 * A * B) * u x ^ 2) volume :=
    hu2I.const_mul (5 * A * B)
  have hboundInt : (∫ x, u x ^ 6 * θ x) ≤ ∫ x, (5 * A * B) * u x ^ 2 := by
    refine integral_mono hu6I hrI ?_
    intro x
    change u x ^ 6 * θ x ≤ (5 * A * B) * u x ^ 2
    have heq : u x ^ 6 * θ x = g x ^ 2 * u x ^ 2 := by
      dsimp only [g]
      rw [mul_pow, hs2]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hpoint x) (sq_nonneg _)
  calc
    _ ≤ ∫ x, (5 * A * B) * u x ^ 2 := hboundInt
    _ = 5 * (eLpNorm u 2 volume).toReal ^ 4 * B := by
      rw [integral_const_mul]
      change (5 * A * B) * A = _
      rw [← hnorm]
      ring

end MathlibExt.Analysis.Calculus.WeightedSixthPowerGagliardoNirenbergWanted
