/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

The definitions and theorem statement in `benchmark/level2/ma_proofbench_l2_80.lean`
(openbmb/ma-proofbench, commit 31bab4c78fd1b0c464e767d62e9202163d1e9029).
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors: L. Pu et al.

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

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Radial Sobolev embedding outside the unit ball

For radial functions supported outside the closed unit ball, the $W^{1,p}$ norm controls every
$L^q$ norm with $p \le q \le \infty$. The proof integrates the radial profile over intervals of
length one.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace MathlibExt.Analysis.FunctionalAnalysis.RadialSobolevExteriorBallWanted

/-- **Real $n$-space with the Euclidean norm.** For a natural number $n$, $\mathbb{R}^n$ denotes the
$n$-dimensional real Euclidean space: real $n$-tuples with the Euclidean inner product and norm. -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- **Closed unit ball of $\mathbb{R}^n$.** For a natural number $n$, the closed unit ball of
$\mathbb{R}^n$ is the set $\{x \in \mathbb{R}^n : \|x\| \le 1\}$, where $\|\cdot\|$ is the Euclidean
norm. -/
def ClosedUnitBall (n : ℕ) : Set (Rn n) := {x : Rn n | ‖x‖ ≤ 1}

/-- **Radial functions on $\mathbb{R}^n$.** A function $f \colon \mathbb{R}^n \to \mathbb{R}$ is
radial if $f(x) = f(y)$ for all $x, y \in \mathbb{R}^n$ with $\|x\| = \|y\|$, where $\|\cdot\|$ is
the Euclidean norm. -/
def IsRadial {n : ℕ} (f : Rn n → ℝ) : Prop :=
  ∀ x y : Rn n, ‖x‖ = ‖y‖ → f x = f y

open Set Filter

/-- Integrating the fundamental theorem of calculus on a unit interval bounds evaluation at
its left endpoint. -/
private lemma norm_le_unit_integrals {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (r : ℝ) :
    ‖u r‖ ≤ (∫ t in Ioc r (r + 1), ‖u t‖) + ∫ t in Ioc r (r + 1), ‖deriv u t‖ := by
  have hd := (hu.continuous_deriv le_rfl).norm
  let D := ∫ t in r..r + 1, ‖deriv u t‖
  have h (s : ℝ) (hs : s ∈ Ioc r (r + 1)) : ‖u r‖ ≤ ‖u s‖ + D := by
    apply (norm_le_norm_add_norm_sub (u s) (u r)).trans
    apply add_le_add_right
    rw [← intervalIntegral.integral_deriv_of_contDiffOn_Icc hu.contDiffOn hs.1.le]
    apply (intervalIntegral.norm_integral_le_integral_norm hs.1.le).trans
    exact intervalIntegral.integral_mono_interval le_rfl hs.1.le hs.2
      (.of_forall fun _ => norm_nonneg _) (hd.intervalIntegrable ..)
  have hm := integral_mono_ae (μ := volume.restrict (Ioc r (r + 1)))
    (continuous_const.integrableOn_Ioc) ((hu.continuous.norm.add continuous_const).integrableOn_Ioc)
    ((ae_restrict_mem measurableSet_Ioc).mono h)
  rw [integral_add' (μ := volume.restrict (Ioc r (r + 1))) (f := fun s => ‖u s‖) (g := fun _ => D)
    hu.continuous.norm.integrableOn_Ioc continuous_const.integrableOn_Ioc] at hm
  simpa [D, intervalIntegral.integral_of_le (show r ≤ r + 1 by linarith), measureReal_def,
    Real.volume_Ioc] using hm

private noncomputable def sphereArea (n : ℕ) : ℝ :=
  n * volume.real (Metric.ball (0 : Rn n) 1)

private lemma sphereArea_pos {n : ℕ} (hn : 0 < n) : 0 < sphereArea n := by
  apply mul_pos (Nat.cast_pos.mpr hn)
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne'
    measure_ball_lt_top.ne

/-- Outside radius one the polar Jacobian is at least one. Consequently an ambient
$L^p$ majorant controls the unweighted integral on any unit radial interval there. -/
private lemma integral_profile_le {n : ℕ} [Nontrivial (Rn n)] {p : ENNReal}
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) {g : ℝ → ℝ} (hg : Continuous g)
    {F : Rn n → ℝ} (hF : MemLp F p volume) (hdom : ∀ x, ‖g ‖x‖‖ ≤ ‖F x‖)
    {r : ℝ} (hr : 1 ≤ r) :
    (∫ t in Ioc r (r + 1), ‖g t‖) ≤ (sphereArea n)⁻¹ ^ p.toReal⁻¹ * lpNorm F p volume := by
  have hp₀ := (zero_lt_one.trans_le hp).ne'
  let w := fun t : ℝ => ‖g t‖ ^ p.toReal
  have hw (t : ℝ) : 0 ≤ w t := Real.rpow_nonneg (norm_nonneg _) _
  have hcont : Continuous w := hg.norm.rpow_const fun _ => Or.inr ENNReal.toReal_nonneg
  have hle (x : Rn n) : w ‖x‖ ≤ ‖F x‖ ^ p.toReal :=
    Real.rpow_le_rpow (norm_nonneg _) (hdom x) ENNReal.toReal_nonneg
  have hFi := hF.integrable_norm_rpow hp₀ hp'
  have hi : Integrable (fun x : Rn n => w ‖x‖) := hFi.mono'
    (hcont.comp continuous_norm).aestronglyMeasurable (.of_forall fun x => by
      simpa [Real.norm_of_nonneg (hw _)] using hle x)
  have hwi : IntegrableOn (fun t : ℝ => t ^ (n - 1) * w t) (Ioi 0) := by
    simpa [Rn, smul_eq_mul] using (integrable_fun_norm_addHaar volume).mp hi
  have hsub : Ioc r (r + 1) ⊆ Ioi 0 := fun _ ht => zero_lt_one.trans (hr.trans_lt ht.1)
  have hlocal : (∫ t in Ioc r (r + 1), w t) ≤ ∫ t in Ioi 0, t ^ (n - 1) * w t := by
    trans ∫ t in Ioc r (r + 1), t ^ (n - 1) * w t
    · apply integral_mono_ae hcont.integrableOn_Ioc (hwi.mono_set hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact le_mul_of_one_le_left (hw t) (one_le_pow₀ (hr.trans ht.1.le))
    · apply setIntegral_mono_set hwi _ (.of_forall hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (pow_nonneg ht.le _) (hw _)
  have hpolar := integral_fun_norm_addHaar (volume : Measure (Rn n)) w
  have harea : 0 < sphereArea n := sphereArea_pos (by
    simpa [Rn] using Module.finrank_pos (R := ℝ) (M := Rn n))
  have hpow : (∫ t in Ioc r (r + 1), w t) ≤ (sphereArea n)⁻¹ * ∫ x, ‖F x‖ ^ p.toReal := by
    rw [← div_eq_inv_mul, le_div_iff₀ harea, mul_comm]
    apply (mul_le_mul_of_nonneg_left hlocal harea.le).trans
    have heq : sphereArea n * (∫ t in Ioi 0, t ^ (n - 1) * w t) = ∫ x : Rn n, w ‖x‖ := by
      simpa [sphereArea, Rn, nsmul_eq_mul, smul_eq_mul, mul_assoc] using hpolar.symm
    exact heq.le.trans (integral_mono hi hFi hle)
  let μ := volume.restrict (Ioc r (r + 1))
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  have hgp : MemLp g p μ := by
    apply (integrable_norm_rpow_iff hg.aestronglyMeasurable hp₀ hp').mp
    exact hcont.integrableOn_Ioc
  calc
    _ = lpNorm g 1 μ := (lpNorm_one_eq_integral_norm hg.aestronglyMeasurable).symm
    _ ≤ lpNorm g p μ := ENNReal.toReal_mono hgp.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hp)
    _ ≤ _ := by
      rw [lpNorm_eq_integral_norm_rpow_toReal hp₀ hp' hg.aestronglyMeasurable,
        lpNorm_eq_integral_norm_rpow_toReal hp₀ hp' hF.aestronglyMeasurable,
        ← Real.mul_rpow (inv_nonneg.mpr harea.le) (integral_nonneg fun x =>
          Real.rpow_nonneg (norm_nonneg (F x)) _)]
      exact Real.rpow_le_rpow (integral_nonneg hw) hpow (by positivity)

/-- A common bound for the pointwise norm and the $L^p$ norm bounds all intermediate
$L^q$ norms. -/
private lemma intermediate_norm_le {n : ℕ} {f : Rn n → ℝ} {p q : ENNReal} {B : ℝ}
    (hp : 0 < p) (hp' : p ≠ ⊤) (hpq : p ≤ q) (hfp : MemLp f p volume)
    (hfq : MemLp f q volume) (hB : 0 ≤ B) (hpB : lpNorm f p volume ≤ B)
    (hpt : ∀ x, ‖f x‖ ≤ B) : eLpNorm f q volume ≤ ENNReal.ofReal B := by
  rcases eq_or_ne q ⊤ with rfl | hq
  · rw [eLpNorm_exponent_top hfq.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (.of_forall hpt)
  have hq₀ := hp.trans_le hpq
  have hPQ := ENNReal.toReal_mono hq hpq
  have hP := ENNReal.toReal_pos hp.ne' hp'
  have hQ := ENNReal.toReal_pos hq₀.ne' hq
  rw [lpNorm_eq_integral_norm_rpow_toReal hp.ne' hp' hfp.aestronglyMeasurable,
    Real.rpow_inv_le_iff_of_pos (integral_nonneg fun _ => by positivity) hB hP] at hpB
  rw [← ofReal_lpNorm hfq]
  apply ENNReal.ofReal_le_ofReal
  rw [lpNorm_eq_integral_norm_rpow_toReal hq₀.ne' hq hfq.aestronglyMeasurable,
    Real.rpow_inv_le_iff_of_pos (integral_nonneg fun _ => by positivity) hB hQ]
  let d := q.toReal - p.toReal
  have hd : 0 ≤ d := sub_nonneg.mpr hPQ
  have he : d + p.toReal = q.toReal := sub_add_cancel ..
  calc
    _ ≤ ∫ x, B ^ d * ‖f x‖ ^ p.toReal := by
      apply integral_mono (hfq.integrable_norm_rpow hq₀.ne' hq)
        ((hfp.integrable_norm_rpow hp.ne' hp').const_mul _)
      intro x
      dsimp only
      rw [← he, Real.rpow_add_of_nonneg (norm_nonneg _) hd hP.le]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (hpt x) hd)
        (Real.rpow_nonneg (norm_nonneg _) _)
    _ ≤ B ^ d * B ^ p.toReal := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hpB (Real.rpow_nonneg hB _)
    _ = _ := by rw [← Real.rpow_add_of_nonneg hB hd hP.le, he]

private lemma profile_deriv_le {n : ℕ} {f : Rn n → ℝ} (hf : Differentiable ℝ f)
    (hrad : IsRadial f) {e : Rn n} (he : ‖e‖ = 1) (x : Rn n) :
    ‖deriv (fun t : ℝ => f (t • e)) ‖x‖‖ ≤ ‖fderiv ℝ f x‖ := by
  obtain ⟨v, hv, hx⟩ : ∃ v : Rn n, ‖v‖ = 1 ∧ ‖x‖ • v = x := by
    by_cases hx : x = 0
    · exact ⟨e, he, by simp [hx]⟩
    · exact ⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx, smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) x⟩
  have heq : (fun t : ℝ => f (t • e)) = fun t : ℝ => f (t • v) :=
    funext fun t => hrad _ _ (by simp [norm_smul, he, hv])
  have hline : HasDerivAt (fun t : ℝ => t • v) v ‖x‖ := by
    simpa using (hasDerivAt_id' ‖x‖).smul_const v
  have hder := ((hf _).hasFDerivAt.comp_hasDerivAt ‖x‖ hline).deriv
  rw [heq, show deriv (fun t : ℝ => f (t • v)) ‖x‖ = _ from hder, hx]
  simpa [hv] using (fderiv ℝ f x).le_opNorm v

/-- **Radial Sobolev embedding outside the unit ball.** Let $n \ge 2$, let $B$ be the closed unit
ball of $\mathbb{R}^n$, and let $1 < p < 2$ and $p \le q \le \infty$. Then there is a constant
$C > 0$ such that every radial function $f \colon \mathbb{R}^n \to \mathbb{R}$ that has compact
support, whose closed support is contained in $\mathbb{R}^n \setminus B$, and which is $C^\infty$
on $\mathbb{R}^n \setminus B$, satisfies

$$\|f\|_{L^q} \le C \left( \|f\|_{L^p} + \big\| |Df| \big\|_{L^p} \right),$$

where the norms are taken with respect to Lebesgue measure and $|Df(x)|$ is the operator norm of
the derivative of $f$ at $x$.

Smoothness here means $C^\infty$. The source's formal statement asked for real-analyticity
instead, which makes the claim vacuous: an analytic, radial, compactly supported $f$ vanishes
outside the ball.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_80.lean` at
openbmb/ma-proofbench@31bab4c, with the change above.
-/
public theorem exists_eLpNorm_le_sobolev_of_radial_of_tsupport_subset_compl_closedBall
  (n : ℕ)
  (hn : 2 ≤ n)
  (p q : ENNReal)
  (hp1 : 1 < p)
  (hp2 : p < 2)
  (hpq : p ≤ q) :
  ∃ C : ℝ, 0 < C ∧
    ∀ f : Rn n → ℝ,
      ContDiffOn ℝ ∞ f ((ClosedUnitBall n)ᶜ) →
      HasCompactSupport f →
      tsupport f ⊆ (ClosedUnitBall n)ᶜ →
      IsRadial f →
      eLpNorm f q volume ≤
        ENNReal.ofReal C *
          (eLpNorm f p volume +
            eLpNorm (fun x : Rn n => ‖fderiv ℝ f x‖) p volume) := by
  have hn₀ : 0 < n := by omega
  have : Nontrivial (Rn n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa [Rn] using hn₀)
  have hp₀ := zero_lt_one.trans hp1
  have hp' : p ≠ ⊤ := (hp2.trans ENNReal.ofNat_lt_top).ne
  let K := (sphereArea n)⁻¹ ^ p.toReal⁻¹
  let C := max 1 K
  have hC : 1 ≤ C := le_max_left ..
  refine ⟨C, zero_lt_one.trans_le hC, fun f hsm hc hs hrad => ?_⟩
  have hf : ContDiff ℝ 1 f := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport f
    · have hopen : IsOpen (ClosedUnitBall n)ᶜ :=
        (isClosed_le continuous_norm continuous_const).isOpen_compl
      exact ((hsm x (hs hx)).contDiffAt (hopen.mem_nhds (hs hx))).of_le (by simp)
    · exact contDiff_zero_fun.contDiffAt.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp hx)
  let D := fun x => ‖fderiv ℝ f x‖
  have hfp : MemLp f p volume := hf.continuous.memLp_of_hasCompactSupport hc
  have hDp : MemLp D p volume := ((hf.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport
    (hc.fderiv ℝ)).norm
  let S := lpNorm f p volume + lpNorm D p volume
  have hS : 0 ≤ S := add_nonneg lpNorm_nonneg lpNorm_nonneg
  have hbase : lpNorm f p volume ≤ C * S :=
    (le_add_of_nonneg_right lpNorm_nonneg).trans (le_mul_of_one_le_left hS hC)
  rw [← ofReal_lpNorm hfp, ← ofReal_lpNorm hDp, ← ENNReal.ofReal_add lpNorm_nonneg lpNorm_nonneg,
    ← ENNReal.ofReal_mul (zero_le_one.trans hC)]
  apply intermediate_norm_le hp₀ hp' hpq hfp (hf.continuous.memLp_of_hasCompactSupport hc)
    (mul_nonneg (zero_le_one.trans hC) hS) hbase
  obtain ⟨e, he⟩ := exists_norm_eq (Rn n) zero_le_one
  let u := fun t : ℝ => f (t • e)
  have hu : ContDiff ℝ 1 u := hf.comp (ContinuousLinearMap.toSpanSingleton ℝ e).contDiff
  have hval (x : Rn n) : u ‖x‖ = f x := hrad _ _ (by simp [norm_smul, he])
  intro x
  by_cases hx : 1 ≤ ‖x‖
  · rw [← hval]
    apply (norm_le_unit_integrals hu ‖x‖).trans
    have h₁ := integral_profile_le hp1.le hp' hu.continuous hfp
      (fun y => (congrArg norm (hval y)).le) hx
    have h₂ := integral_profile_le hp1.le hp' (hu.continuous_deriv le_rfl) hDp
      (fun y => by simpa [D] using profile_deriv_le (hf.differentiable one_ne_zero) hrad he y) hx
    calc
      _ ≤ K * lpNorm f p volume + K * lpNorm D p volume := add_le_add h₁ h₂
      _ = K * S := (mul_add ..).symm
      _ ≤ C * S := mul_le_mul_of_nonneg_right (le_max_right ..) hS
  · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hs h (show ‖x‖ ≤ 1 from (lt_of_not_ge hx).le)
    simpa [hzero] using mul_nonneg (zero_le_one.trans hC) hS

end MathlibExt.Analysis.FunctionalAnalysis.RadialSobolevExteriorBallWanted
