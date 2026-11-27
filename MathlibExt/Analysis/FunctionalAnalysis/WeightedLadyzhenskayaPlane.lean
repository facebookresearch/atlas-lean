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
31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_48.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; also distributed in the Hugging Face dataset
openbmb/MA-ProofBench), under the MIT license above. The ATLAS import converted the statement to
`theorem_wanted`, named and documented it in the namespace below, and rendered smoothness with
`∞`, the coercion of the top of `ℕ∞` (not analytic order). This file preserves the ATLAS
proposition and audited docstring, replaces the wanted statement with a proof, and narrows imports.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted Ladyzhenskaya inequality in the plane

Apply the two-dimensional $W^{1,1}$ Sobolev inequality to $u^2\sqrt{w}$. Its gradient is bounded
pointwise by three times $|u|$ times the square root of the weighted energy density.
Cauchy–Schwarz separates the unweighted $L^2$ norm of $u$ from the energy.
-/

open MeasureTheory
open scoped ContDiff ENNReal

namespace MathlibExt.Analysis.FunctionalAnalysis.WeightedLadyzhenskayaPlaneWanted

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The essential bound on the logarithmic derivative bounds the gradient almost everywhere. -/
private theorem weight_grad_bound {w : Plane → ℝ} (hw : ∀ x, 0 < w x)
    (hwC : ContDiff ℝ 1 w)
    (h : eLpNorm (fun x => ‖fderiv ℝ w x‖ / w x) ⊤ volume ≤ 1) :
    ∀ᵐ x ∂volume, ‖fderiv ℝ w x‖ ≤ w x := by
  let l (x : Plane) := ‖fderiv ℝ w x‖ / w x
  have hd : Continuous (fderiv ℝ w) := hwC.continuous_fderiv (by norm_num)
  have hl : Continuous l := hd.norm.div hwC.continuous (fun x => (hw x).ne')
  change eLpNorm l ⊤ volume ≤ 1 at h
  rw [eLpNorm_exponent_top hl.aestronglyMeasurable] at h
  filter_upwards [ae_le_eLpNormEssSup (f := l) (μ := volume)] with x hx
  have he := ENNReal.toReal_mono (b := (1 : ℝ≥0∞)) (by simp) (hx.trans h)
  rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_one,
    Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (hw x).le)] at he
  simpa only [one_mul] using (div_le_iff₀ (hw x)).mp he

/-- Pointwise derivative estimate for the square-root-weighted square. -/
private theorem weighted_sq_grad_le {u w : Plane → ℝ}
    (hu : ContDiff ℝ 1 u) (hw : ContDiff ℝ 1 w) {x : Plane} (hpos : 0 < w x)
    (hlog : ‖fderiv ℝ w x‖ ≤ w x) :
    ‖fderiv ℝ (fun y => u y ^ 2 * Real.sqrt (w y)) x‖ ≤
      3 * |u x| * Real.sqrt ((‖fderiv ℝ u x‖ ^ 2 + |u x| ^ 2) * w x) := by
  let s := Real.sqrt (w x)
  let a := ‖fderiv ℝ u x‖
  let b := |u x|
  let G := (a ^ 2 + b ^ 2) * w x
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hs : 0 < s := Real.sqrt_pos.2 hpos
  have hs2 : s ^ 2 = w x := Real.sq_sqrt hpos.le
  have hG : 0 ≤ G := mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hpos.le
  have hGa : s * a ≤ Real.sqrt G := by
    apply (sq_le_sq₀ (mul_nonneg hs.le ha) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, hs2, Real.sq_sqrt hG, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) hpos.le
  have hGb : s * b ≤ Real.sqrt G := by
    apply (sq_le_sq₀ (mul_nonneg hs.le hb) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, hs2, Real.sq_sqrt hG, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg _)) hpos.le
  have hlog' : (1 / (2 * s)) * ‖fderiv ℝ w x‖ ≤ s / 2 := by
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ (mul_pos (by norm_num) hs)).mpr
    calc
      ‖fderiv ℝ w x‖ ≤ w x := hlog
      _ = s / 2 * (2 * s) := by rw [← hs2]; ring
  have hD := (((hu.differentiable one_ne_zero x).hasFDerivAt).pow 2).mul
    (((hw.differentiable one_ne_zero x).hasFDerivAt).sqrt hpos.ne')
  change ‖fderiv ℝ ((fun y => u y ^ 2) * fun y => Real.sqrt (w y)) x‖ ≤
    3 * b * Real.sqrt G
  rw [hD.fderiv]
  calc
    ‖u x ^ 2 • ((1 / (2 * s)) • fderiv ℝ w x) +
        s • ((2 • u x ^ (2 - 1)) • fderiv ℝ u x)‖ ≤
        ‖u x ^ 2 • ((1 / (2 * s)) • fderiv ℝ w x)‖ +
          ‖s • ((2 • u x ^ (2 - 1)) • fderiv ℝ u x)‖ := norm_add_le _ _
    _ = b ^ 2 * ((1 / (2 * s)) * ‖fderiv ℝ w x‖) + 2 * b * (s * a) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hs.le, abs_of_nonneg
        (show 0 ≤ 1 / (2 * s) from by positivity), Nat.reduceSub, pow_one, two_nsmul, ← two_mul,
        abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), a, b]
      ring
    _ ≤ b ^ 2 * (s / 2) + 2 * b * (s * a) := by gcongr
    _ = b * (2 * (s * a) + (s * b) / 2) := by ring
    _ ≤ 3 * b * Real.sqrt G := by
      rw [mul_comm (3 : ℝ), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hb
      calc
        2 * (s * a) + s * b / 2 ≤ 2 * Real.sqrt G + Real.sqrt G / 2 := by gcongr
        _ ≤ 3 * Real.sqrt G := by nlinarith [Real.sqrt_nonneg G]


private theorem integral_norm_rpow_two (f : Plane → ℝ) :
    (∫ x, ‖f x‖ ^ (2 : ℝ)) = ∫ x, f x ^ (2 : ℕ) := by
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.norm_eq_abs, sq_abs]

private theorem toReal_eLpNorm_two_sq {f : Plane → ℝ} (hf : Continuous f) :
    (eLpNorm f 2 volume).toReal ^ (2 : ℕ) = ∫ x, f x ^ (2 : ℕ) := by
  rw [toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp) hf.aestronglyMeasurable]
  rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, integral_norm_rpow_two,
    ← one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

/-- **Weighted Ladyzhenskaya inequality in the plane.** There is a constant $C > 0$ such that
for every $C^1$ function $\omega : \mathbb{R}^2 \to \mathbb{R}$ with $\omega(x) > 0$ for all $x$
and $\|\nabla\omega/\omega\|_{L^\infty(\mathbb{R}^2)} \le 1$, and every smooth compactly supported
function $u : \mathbb{R}^2 \to \mathbb{R}$,
$$
\int_{\mathbb{R}^2} u^4 \omega \le C \|u\|_{L^2(\mathbb{R}^2)}^2
\int_{\mathbb{R}^2} \left(|\nabla u|^2 + |u|^2\right) \omega.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Inequalities
in real analysis), `benchmark/level2/ma_proofbench_l2_48.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_const_integral_pow_four_mul_weight_le :
  ∃ C : ℝ, 0 < C ∧
    ∀ w : EuclideanSpace ℝ (Fin 2) → ℝ,
      (∀ x : EuclideanSpace ℝ (Fin 2), 0 < w x) →
      ContDiff ℝ 1 w →
      eLpNorm (fun x : EuclideanSpace ℝ (Fin 2) => ‖fderiv ℝ w x‖ / w x) ⊤ volume ≤ 1 →
      ∀ u : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
        ∫ x : EuclideanSpace ℝ (Fin 2), (u x) ^ (4 : ℕ) * w x ≤
          C * (ENNReal.toReal (eLpNorm u 2 volume)) ^ (2 : ℕ) *
            ∫ x : EuclideanSpace ℝ (Fin 2), (‖fderiv ℝ u x‖ ^ (2 : ℕ) + |u x| ^ (2 : ℕ)) * w x := by
  let p : NNReal := 2
  let K := eLpNormLESNormFDerivOneConst (volume : Measure Plane) (p : ℝ)
  refine ⟨(3 * (K : ℝ)) ^ 2 + 1, by positivity, ?_⟩
  intro w hw hwC hlog u hu huK
  have hu₁ : ContDiff ℝ 1 u := hu.of_le (by simp)
  let v (x : Plane) := u x ^ 2 * Real.sqrt (w x)
  let G (x : Plane) := (‖fderiv ℝ u x‖ ^ 2 + |u x| ^ 2) * w x
  let g (x : Plane) := Real.sqrt (G x)
  have hv : ContDiff ℝ 1 v := (hu₁.pow 2).mul (hwC.sqrt fun x => (hw x).ne')
  have hvK : HasCompactSupport v :=
    (huK.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right
  have hD : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hDU : Continuous (fderiv ℝ u) := hu₁.continuous_fderiv (by norm_num)
  have hGC : Continuous G := ((hDU.norm.pow 2).add (hu₁.continuous.abs.pow 2)).mul hwC.continuous
  have hG (x : Plane) : 0 ≤ G x := mul_nonneg (by positivity) (hw x).le
  have hG2 (x : Plane) : g x ^ 2 = G x := Real.sq_sqrt (hG x)
  have hgC : Continuous g := Real.continuous_sqrt.comp hGC
  have hgK : HasCompactSupport g := by
    have h1 : HasCompactSupport (fun x => ‖fderiv ℝ u x‖ ^ 2) :=
      ((huK.fderiv ℝ).norm).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    have h2 : HasCompactSupport (fun x => |u x| ^ 2) :=
      huK.abs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    have hGK : HasCompactSupport G := (h1.add h2).mul_right
    exact hGK.comp_left Real.sqrt_zero
  let A := ∫ x, u x ^ (2 : ℕ)
  let B := ∫ x, G x
  have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg hG
  have huLp : MemLp u (ENNReal.ofReal 2) volume :=
    hu₁.continuous.memLp_of_hasCompactSupport huK
  have hgLp : MemLp g (ENNReal.ofReal 2) volume := hgC.memLp_of_hasCompactSupport hgK
  have hCS : (∫ x, |u x| * g x) ≤ Real.sqrt A * Real.sqrt B := by
    have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two huLp hgLp
    rw [integral_norm_rpow_two u, integral_norm_rpow_two g] at hh
    simp_rw [hG2] at hh
    rw [← Real.sqrt_eq_rpow A, ← Real.sqrt_eq_rpow B] at hh
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), g] using hh
  have hM : Integrable (fun x => |u x| * g x) volume :=
    (hu₁.continuous.abs.mul hgC).integrable_of_hasCompactSupport huK.abs.mul_right
  have hI : Integrable (fun x => ‖fderiv ℝ v x‖) volume :=
    hD.norm.integrable_of_hasCompactSupport (hvK.fderiv ℝ).norm
  have hInt : (∫ x, ‖fderiv ℝ v x‖) ≤ 3 * (Real.sqrt A * Real.sqrt B) := by
    calc
      _ ≤ ∫ x, 3 * (|u x| * g x) := by
        apply integral_mono_ae hI (hM.const_mul 3)
        filter_upwards [weight_grad_bound hw hwC hlog] with x hx
        simpa only [v, g, G, mul_assoc] using weighted_sq_grad_le hu₁ hwC (hw x) hx
      _ ≤ _ := by rw [integral_const_mul]; gcongr
  have hc : NNReal.HolderConjugate (Module.finrank ℝ Plane) p := by
    simpa [p, finrank_euclideanSpace] using NNReal.HolderConjugate.two_two
  have hSob := eLpNorm_le_eLpNorm_fderiv_one (volume : Measure Plane) hv hvK (p := p) hc
  have hpE : (p : ℝ≥0∞) = 2 := by norm_num [p]
  rw [hpE] at hSob
  have hDf : MemLp (fderiv ℝ v) 1 volume :=
    hD.memLp_of_hasCompactSupport (hvK.fderiv ℝ)
  have hSobR : (eLpNorm v 2 volume).toReal ≤ (K : ℝ) * ∫ x, ‖fderiv ℝ v x‖ := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hDf.eLpNorm_ne_top) hSob
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_eLpNorm,
      lpNorm_one_eq_integral_norm hD.aestronglyMeasurable] using hh
  have hK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
  have hSq := (sq_le_sq₀ ENNReal.toReal_nonneg (show 0 ≤ (K : ℝ) * (3 * (Real.sqrt A * Real.sqrt B))
    from by positivity)).mpr (hSobR.trans (mul_le_mul_of_nonneg_left hInt hK))
  rw [toReal_eLpNorm_two_sq hv.continuous, mul_pow, mul_pow (3 : ℝ),
    mul_pow (Real.sqrt A), Real.sq_sqrt hA, Real.sq_sqrt hB] at hSq
  have hEq : (∫ x, u x ^ (4 : ℕ) * w x) = ∫ x, v x ^ (2 : ℕ) := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [v]
    rw [mul_pow, Real.sq_sqrt (hw x).le]
    ring
  rw [hEq, toReal_eLpNorm_two_sq hu₁.continuous]
  calc
    _ ≤ (3 * (K : ℝ)) ^ 2 * A * B := hSq.trans_eq (by ring)
    _ ≤ ((3 * (K : ℝ)) ^ 2 + 1) * A * B := by gcongr; exact le_add_of_nonneg_right zero_le_one

end MathlibExt.Analysis.FunctionalAnalysis.WeightedLadyzhenskayaPlaneWanted
