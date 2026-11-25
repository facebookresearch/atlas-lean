/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_77.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the definitions of the Euclidean plane, the discs,
the annuli and the weight, and the statement of the weighted Hardy inequality.
Authors: L. Pu et al. (MA-ProofBench).
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

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weighted Hardy inequality on the annulus

`exists_eLpNorm_le_weighted_grad_add_outer_annulus` bounds the full-annulus norm by the
distance-weighted gradient norm and the outer-annulus norm. On each ray, integrate the
derivative of `(r - 1) * F r ^ p`, where `F` majorizes the absolute value of the function
by its outer trace plus the integral of its speed bound. The lower endpoint term has the
sign needed to pass to the open annulus. Polar integration then combines the ray estimates.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedHardyInequalityWanted

/-- The Euclidean plane. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- **Open discs about the origin for the annulus Hardy inequality.** For a real number $r$,
$B_r = \{x \in \mathbb{R}^2 : |x| < r\}$ is the open disc of radius $r$ about the origin of the
Euclidean plane $\mathbb{R}^2$, where $|x|$ is the Euclidean norm. -/
noncomputable abbrev B (r : ℝ) : Set R2 := Metric.ball (0 : R2) r

/-- **Full annulus of the weighted Hardy inequality.** $\Omega_1 = B_3 \setminus \overline{B}_1$,
where $B_r$ is the open disc of radius $r$ about the origin of the Euclidean plane $\mathbb{R}^2$
and $\overline{B}_1$ is the closure of $B_1$; that is, writing $|x|$ for the Euclidean norm,
$\Omega_1$ is the annulus $\{x \in \mathbb{R}^2 : 1 < |x| < 3\}$. -/
noncomputable abbrev Omega1 : Set R2 := B 3 \ closure (B 1)

/-- **Outer annulus of the weighted Hardy inequality.** $\Omega_2 = B_3 \setminus \overline{B}_2$,
where $B_r$ is the open disc of radius $r$ about the origin of the Euclidean plane $\mathbb{R}^2$
and $\overline{B}_2$ is the closure of $B_2$; that is, writing $|x|$ for the Euclidean norm,
$\Omega_2$ is the annulus $\{x \in \mathbb{R}^2 : 2 < |x| < 3\}$. -/
noncomputable abbrev Omega2 : Set R2 := B 3 \ closure (B 2)

/-- **Weight of the annulus Hardy inequality.** For $x$ in the Euclidean plane $\mathbb{R}^2$,
$\phi(x) = \max\{|x| - 1, 0\}$, where $|x|$ is the Euclidean norm; this is the distance from $x$
to the closed unit disc. -/
noncomputable def phi (x : R2) : ℝ := max (‖x‖ - 1) 0

private lemma mixed_bound {p m z : ℝ} (hp : 1 ≤ p) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    2 * p * m ^ (p - 1) * z ≤ m ^ p + (2 * p) ^ p * z ^ p := by
  have hp₀ : 0 ≤ p := by linarith
  have step {v : ℝ} (hv : 0 ≤ v) : v ^ (p - 1) * v = v ^ p := by
    rw [← Real.rpow_add_one' hv (by linarith : p - 1 + 1 ≠ 0), sub_add_cancel]
  have h : 0 ≤ 2 * p * z := by positivity
  rcases le_total m (2 * p * z) with hle | hle
  · have H := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hm hle (sub_nonneg.mpr hp)) h
    rw [step h, Real.mul_rpow (by positivity) hz] at H
    linarith [Real.rpow_nonneg hm p]
  · have H := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hm (p - 1))
    rw [step hm] at H
    linarith [mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 2 * p) p) (Real.rpow_nonneg hz p)]

/-- The weighted estimate on a closed radial segment, with its outer endpoint term. -/
private lemma segment_bound {p a b : ℝ} (hp : 1 ≤ p) (ha : 1 < a) (hab : a ≤ b)
    (hb : b < 3) {v d : ℝ → ℝ} (hv : DifferentiableOn ℝ v (Ioo 1 3))
    (hd : ContinuousOn d (Ioo 1 3))
    (hvd : ∀ r ∈ Ioo 1 3, ‖deriv v r‖ ≤ d r) :
    (∫ r in a..b, ‖v r‖ ^ p) ≤
      2 * (b - 1) * ‖v b‖ ^ p +
        (2 * p) ^ p * ∫ r in a..b, ((r - 1) * d r) ^ p := by
  have hp₀ : 0 ≤ p := by linarith
  have dint {x : ℝ} (hx : 1 < x) (hxb : x ≤ b) : IntervalIntegrable d volume x b :=
    (hd.mono (uIcc_of_le hxb ▸ Icc_subset_Ioo hx hb)).intervalIntegrable
  -- The speed integral gives a differentiable majorant even when p = 1 and v changes sign.
  let F (r : ℝ) := ‖v b‖ + ∫ t in r..b, d t
  have hF {r : ℝ} (hr : r ∈ Icc a b) : HasDerivAt F (-d r) r := by
    have hrs := Icc_subset_Ioo ha hb hr
    have hn := Ioo_mem_nhds hrs.1 hrs.2
    exact (intervalIntegral.integral_hasDerivAt_left (dint hrs.1 hr.2)
      (hd.stronglyMeasurableAtFilter isOpen_Ioo r hrs) (hd.continuousAt hn)).const_add _
  have hdom {r : ℝ} (hr : r ∈ Icc a b) : ‖v r‖ ≤ F r := by
    have hrs := Icc_subset_Ioo (ha.trans_le hr.1) hb
    have H := norm_sub_le_integral_of_norm_deriv_le_of_le hr.2
      (hv.continuousOn.mono hrs) (hv.mono (Ioo_subset_Icc_self.trans hrs))
      (.of_forall fun t ht ↦ hvd t (hrs (mem_Icc_of_Ioo ht))) (dint (ha.trans_le hr.1) hr.2)
    rw [norm_sub_rev] at H
    exact (norm_le_norm_add_norm_sub' _ _).trans (add_le_add_right H _)
  let W (r : ℝ) := ((r - 1) * d r) ^ p
  have hW : ContinuousOn W (Icc a b) :=
    ((continuous_id.sub continuous_const).continuousOn.mul (hd.mono (Icc_subset_Ioo ha hb))
      ).rpow_const (fun _ _ ↦ Or.inr hp₀)
  have hV := ((hv.continuousOn.mono (Icc_subset_Ioo ha hb)).norm.rpow_const (fun _ _ ↦ Or.inr hp₀))
  have hG {r : ℝ} (hr : r ∈ Icc a b) := ((hasDerivAt_id r |>.sub_const 1).mul
    ((hF hr).rpow_const (Or.inr hp))).const_mul 2
  have H := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab
    (g := fun r ↦ 2 * ((r - 1) * F r ^ p))
    (fun r hr ↦ (hG hr).continuousAt.continuousWithinAt)
    (fun r hr ↦ (hG (mem_Icc_of_Ioo hr)).hasDerivWithinAt)
    (φ := fun r ↦ ‖v r‖ ^ p - (2 * p) ^ p * W r)
    ((hV.sub (continuousOn_const.mul hW)).integrableOn_compact isCompact_Icc)
    (by
      intro r hr
      have hc := mem_Icc_of_Ioo hr
      have h := hdom hc
      have hm := (norm_nonneg _).trans h
      have hz := mul_nonneg (sub_nonneg.mpr (Icc_subset_Ioo ha hb hc).1.le)
        ((norm_nonneg _).trans (hvd r (Icc_subset_Ioo ha hb hc)))
      have H := mixed_bound hp hm hz
      have V := Real.rpow_le_rpow (norm_nonneg _) h hp₀
      dsimp [W, id] at *
      linarith)
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul] at H
  · have Fb : F b = ‖v b‖ := by simp [F]
    rw [Fb] at H
    have := Real.rpow_nonneg ((norm_nonneg _).trans (hdom (left_mem_Icc.mpr hab))) p
    dsimp only [W] at H
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.le) this]
  · exact (uIcc_of_le hab ▸ hV).intervalIntegrable
  · exact (uIcc_of_le hab ▸ (continuousOn_const.mul hW)).intervalIntegrable

private lemma ofReal_segment {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hn : ∀ r ∈ Icc a b, 0 ≤ f r) :
    ENNReal.ofReal (∫ r in a..b, f r) = ∫⁻ r in Ioc a b, ENNReal.ofReal (f r) := by
  rw [intervalIntegral.integral_of_le hab]
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (hf.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hr
    exact hn r (Ioc_subset_Icc_self hr)

private lemma inner_exhaustion (f : ℝ → ℝ≥0∞) {c : ℝ≥0∞}
    (h : ∀ a : ℝ, 1 < a → a ≤ 2 → (∫⁻ r in Ioc a 2, f r) ≤ c) :
    (∫⁻ r in Ioc 1 2, f r) ≤ c := by
  let S (q : {q : ℚ // 1 < (q : ℝ) ∧ (q : ℝ) ≤ 2}) := Ioc (q.val : ℝ) 2
  have hS : Ioc (1 : ℝ) 2 = ⋃ q, S q := by
    ext r
    constructor
    · intro hr
      obtain ⟨q, hq, hqr⟩ := exists_rat_btwn hr.1
      exact mem_iUnion.mpr ⟨⟨q, hq, hqr.le.trans hr.2⟩, hqr, hr.2⟩
    · intro hr
      obtain ⟨q, hq⟩ := mem_iUnion.mp hr
      exact ⟨q.2.1.trans hq.1, hq.2⟩
  have hdir : Directed (· ⊆ ·) S := by
    intro i j
    rcases le_total (i.val : ℝ) (j.val : ℝ) with hij | hji
    · exact ⟨i, Subset.rfl, Ioc_subset_Ioc_left hij⟩
    · exact ⟨j, Ioc_subset_Ioc_left hji, Subset.rfl⟩
  rw [hS, setLIntegral_iUnion_of_directed f hdir]
  exact iSup_le fun q ↦ h _ q.2.1 q.2.2

/-- Bound the unweighted inner moment, choosing the smallest outer trace on a fixed interval. -/
private lemma inner_bound {p : ℝ} (hp : 1 ≤ p) {v d : ℝ → ℝ}
    (hv : DifferentiableOn ℝ v (Ioo 1 3)) (hd : ContinuousOn d (Ioo 1 3))
    (hvd : ∀ r ∈ Ioo 1 3, ‖deriv v r‖ ≤ d r) :
    (∫⁻ r in Ioc 1 2, ENNReal.ofReal (‖v r‖ ^ p)) ≤
      8 * (∫⁻ r in Ioo 2 3, ENNReal.ofReal (‖v r‖ ^ p)) +
        ENNReal.ofReal ((2 * p) ^ p) *
          ∫⁻ r in Ioo 1 3, ENNReal.ofReal (((r - 1) * d r) ^ p) := by
  have hp₀ : 0 ≤ p := by linarith
  let V (r : ℝ) := ‖v r‖ ^ p
  let D (r : ℝ) := ((r - 1) * d r) ^ p
  have hV : ContinuousOn V (Ioo 1 3) :=
    hv.continuousOn.norm.rpow_const (fun _ _ ↦ Or.inr hp₀)
  have hD : ContinuousOn D (Ioo 1 3) :=
    (((continuous_id.sub continuous_const).continuousOn.mul hd).rpow_const
      (fun _ _ ↦ Or.inr hp₀))
  have hV₀ (r : ℝ) : 0 ≤ V r := Real.rpow_nonneg (norm_nonneg _) _
  have hD₀ r (hr : r ∈ Ioo 1 3) : 0 ≤ D r := Real.rpow_nonneg
    (mul_nonneg (sub_nonneg.mpr hr.1.le) ((norm_nonneg _).trans (hvd r hr))) _
  have h₂ : (2 : ℝ) ≤ 5 / 2 := by norm_num
  have houter := Icc_subset_Ioo (by norm_num : (1 : ℝ) < 2) (by norm_num : (5 : ℝ) / 2 < 3)
  obtain ⟨b, hb, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr h₂) (hV.mono houter)
  have hminint := intervalIntegral.integral_mono_on (μ := volume) h₂
    (f := fun _ ↦ V b) intervalIntegrable_const
    ((hV.mono (uIcc_of_le h₂ ▸ houter)).intervalIntegrable) (fun r hr ↦ hmin hr)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hminint
  apply inner_exhaustion
  intro a ha ha₂
  have hab := ha₂.trans hb.1
  have hb₃ := (houter hb).2
  have hseg := segment_bound hp ha hab hb₃ hv hd hvd
  change (∫ r in a..b, V r) ≤ 2 * (b - 1) * V b + (2 * p) ^ p * ∫ r in a..b, D r at hseg
  have hreal : (∫ r in a..b, V r) ≤ 8 * (∫ r in 2..5/2, V r) +
      (2 * p) ^ p * ∫ r in a..b, D r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb₃.le) (hV₀ b)]
  have hW := ENNReal.ofReal_le_ofReal hreal
  have hK := Real.rpow_nonneg (by positivity : 0 ≤ 2 * p) p
  have hint := intervalIntegral.integral_nonneg (μ := volume) h₂ (fun r _ ↦ hV₀ r)
  rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hK
      (intervalIntegral.integral_nonneg hab fun r hr ↦ hD₀ r (Icc_subset_Ioo ha hb₃ hr))),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), ENNReal.ofReal_mul hK,
    ofReal_segment hab (hV.mono (Icc_subset_Ioo ha hb₃)) (fun r _ ↦ hV₀ r),
    ofReal_segment h₂ (hV.mono houter) (fun r _ ↦ hV₀ r),
    ofReal_segment hab (hD.mono (Icc_subset_Ioo ha hb₃))
      (fun r hr ↦ hD₀ r (Icc_subset_Ioo ha hb₃ hr))] at hW
  norm_num only [ENNReal.ofReal_ofNat] at hW
  refine (lintegral_mono_set (Ioc_subset_Ioc_right hb.1)).trans (hW.trans ?_)
  gcongr
  · norm_num
  · exact Ioc_subset_Icc_self.trans (Icc_subset_Ioo ha hb₃)

/-- Insert the polar Jacobian and add the outer annulus to the estimate. -/
private lemma jacobian_bound (V D : ℝ → ℝ≥0∞) (K : ℝ≥0∞)
    (h : (∫⁻ r in Ioc 1 2, V r) ≤
      8 * (∫⁻ r in Ioo 2 3, V r) + K * ∫⁻ r in Ioo 1 3, D r) :
    (∫⁻ r in Ioo 1 3, ENNReal.ofReal r * V r) ≤
      17 * (∫⁻ r in Ioo 2 3, ENNReal.ofReal r * V r) +
        (2 * K) * ∫⁻ r in Ioo 1 3, ENNReal.ofReal r * D r := by
  have lower {k : ℝ} (hk : 1 ≤ k) (f : ℝ → ℝ≥0∞) :
      (∫⁻ r in Ioo k 3, f r) ≤ ∫⁻ r in Ioo k 3, ENNReal.ofReal r * f r := by
    apply setLIntegral_mono' measurableSet_Ioo
    intro r hr
    exact le_mul_of_one_le_left' (by simpa using ENNReal.ofReal_le_ofReal (hk.trans hr.1.le))
  have upper : (∫⁻ r in Ioc 1 2, ENNReal.ofReal r * V r) ≤
      2 * ∫⁻ r in Ioc 1 2, V r := by
    rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    apply setLIntegral_mono' measurableSet_Ioc
    intro r hr
    exact mul_le_mul_left (by simpa using ENNReal.ofReal_le_ofReal hr.2) _
  have split := lintegral_union_le (μ := volume)
    (fun r : ℝ ↦ ENNReal.ofReal r * V r) (Ioc 1 2) (Ioo 2 3)
  rw [Ioc_union_Ioo_eq_Ioo (by norm_num) (by norm_num)] at split
  apply split.trans
  calc
    _ ≤ 2 * (8 * (∫⁻ r in Ioo 2 3, ENNReal.ofReal r * V r) +
        K * ∫⁻ r in Ioo 1 3, ENNReal.ofReal r * D r) +
        (∫⁻ r in Ioo 2 3, ENNReal.ofReal r * V r) := by
      apply add_le_add_left
      refine upper.trans (mul_le_mul_right (h.trans ?_) _)
      exact add_le_add (mul_le_mul_right (lower (by norm_num) V) _)
        (mul_le_mul_right (lower le_rfl D) _)
    _ = _ := by ring

private noncomputable abbrev Direction := Metric.sphere (0 : R2) 1

private noncomputable def shell (k : ℝ) : Set R2 := (fun x ↦ ‖x‖) ⁻¹' Ioo k 3

private lemma shell_open (k : ℝ) : IsOpen (shell k) := isOpen_Ioo.preimage continuous_norm

private lemma annulus_shell {k : ℝ} (hk : k ≠ 0) : B 3 \ closure (B k) = shell k := by
  ext x
  simp [B, closure_ball _ hk, shell, Metric.mem_ball, Metric.mem_closedBall, and_comm]

private lemma norm_ray (θ : Direction) {r : ℝ} (hr : 0 ≤ r) : ‖r • (θ : R2)‖ = r := by
  simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, mem_sphere_zero_iff_norm.mp θ.2]

private noncomputable def rayIntegral (k : ℝ) (f : R2 → ℝ≥0∞) (θ : Direction) :=
  ∫⁻ r in Ioo k 3, ENNReal.ofReal r * f (r • (θ : R2))

/-- Polar integration of a function continuous only on the annulus of integration. -/
private lemma polar {k : ℝ} (hk : 0 ≤ k) {f : R2 → ℝ≥0∞} (hf : ContinuousOn f (shell k)) :
    Measurable (rayIntegral k f) ∧
      (∫⁻ x in shell k, f x) = ∫⁻ θ, rayIntegral k f θ ∂(volume : Measure R2).toSphere := by
  classical
  let g := (shell k).indicator f
  have hg : Measurable g :=
    hf.measurable_piecewise continuousOn_const (shell_open k).measurableSet
  let G (z : Direction × Ioi (0 : ℝ)) := g ((homeomorphUnitSphereProd R2).symm z).val
  have hG : Measurable G := hg.comp
    (measurable_subtype_coe.comp (homeomorphUnitSphereProd R2).symm.measurable)
  have inner (θ : Direction) :
      (∫⁻ r, G (θ, r) ∂Measure.volumeIoiPow 1) = rayIntegral k f θ := by
    rw [Measure.volumeIoiPow]
    rw [lintegral_withDensity_eq_lintegral_mul _ (f := fun r : Ioi (0 : ℝ) ↦
      ENNReal.ofReal (r.val ^ 1)) (g := fun r ↦ G (θ, r)) (by fun_prop)
      (hG.comp (measurable_const.prodMk measurable_id))]
    simp only [Pi.mul_apply, pow_one, G, homeomorphUnitSphereProd_symm_apply_coe]
    rw [lintegral_subtype_comap measurableSet_Ioi (fun r ↦ ENNReal.ofReal r * g (r • (θ : R2)))]
    have hsub : Ioo k 3 ⊆ Ioi (0 : ℝ) := fun _ hr ↦ hk.trans_lt hr.1
    rw [rayIntegral, ← Measure.restrict_restrict_of_subset hsub,
      ← lintegral_indicator measurableSet_Ioo]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    by_cases h : r ∈ Ioo k 3
    · have hx : r • (θ : R2) ∈ shell k := by simpa [shell, norm_ray θ hr.le] using h
      simp [g, indicator_of_mem h, indicator_of_mem hx]
    · have hx : r • (θ : R2) ∉ shell k := by simpa [shell, norm_ray θ hr.le] using h
      simp [g, indicator_of_notMem h, indicator_of_notMem hx]
  constructor
  · rw [← funext inner]
    exact hG.lintegral_prod_right'
  · rw [← lintegral_indicator (shell_open k).measurableSet]
    change (∫⁻ x, g x) = _
    calc
      _ = ∫⁻ x : ({0}ᶜ : Set R2), g (x : R2) ∂((volume : Measure R2).comap (↑)) := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
      _ = ∫⁻ z, G z ∂((volume : Measure R2).toSphere.prod (Measure.volumeIoiPow 1)) := by
        have H := (volume : Measure R2).measurePreserving_homeomorphUnitSphereProd.lintegral_comp hG
        rw [finrank_euclideanSpace_fin] at H
        simpa only [G, Homeomorph.symm_apply_apply] using H
      _ = _ := by
        rw [lintegral_prod _ hG.aemeasurable]
        simp_rw [inner]

private noncomputable def moment (p : ℝ) (u : R2 → ℝ) (x : R2) :=
  ENNReal.ofReal (‖u x‖ ^ p)

private noncomputable def gradTerm (u : R2 → ℝ) (x : R2) :=
  phi x * ‖fderivWithin ℝ u Omega1 x‖

private lemma ray_bound {p : ℝ} (hp : 1 ≤ p) {u : R2 → ℝ}
    (hu : ContDiffOn ℝ 1 u Omega1) (θ : Direction) :
    rayIntegral 1 (moment p u) θ ≤ 17 * rayIntegral 2 (moment p u) θ +
      (2 * ENNReal.ofReal ((2 * p) ^ p)) * rayIntegral 1 (moment p (gradTerm u)) θ := by
  let ray (r : ℝ) := r • (θ : R2)
  let v := u ∘ ray
  let d (r : ℝ) := ‖fderivWithin ℝ u Omega1 (ray r)‖
  have hΩ : Omega1 = shell 1 := annulus_shell one_ne_zero
  have hopen : IsOpen Omega1 := hΩ ▸ shell_open 1
  have maps : MapsTo ray (Ioo 1 3) Omega1 := by
    intro r hr
    rw [hΩ]
    change ‖r • (θ : R2)‖ ∈ Ioo 1 3
    rwa [norm_ray θ (zero_le_one.trans hr.1.le)]
  have hray : Continuous ray := continuous_id.smul continuous_const
  have hd : ContinuousOn d (Ioo 1 3) :=
    (hu.continuousOn_fderivWithin hopen.uniqueDiffOn le_rfl).norm.comp hray.continuousOn maps
  have hdr r (hr : r ∈ Ioo 1 3) :
      HasDerivAt v (fderivWithin ℝ u Omega1 (ray r) θ) r := by
    have H := (hu.differentiableOn_one (ray r) (maps hr)).hasFDerivWithinAt.hasFDerivAt
      (hopen.mem_nhds (maps hr))
    apply H.comp_hasDerivAt
    simpa using (hasDerivAt_id' r).smul_const (θ : R2)
  have hv : DifferentiableOn ℝ v (Ioo 1 3) := fun r hr ↦
    (hdr r hr).differentiableAt.differentiableWithinAt
  have hvd r (hr : r ∈ Ioo 1 3) : ‖deriv v r‖ ≤ d r := by
    rw [(hdr r hr).deriv]
    simpa only [mem_sphere_zero_iff_norm.mp θ.2, mul_one] using
      (fderivWithin ℝ u Omega1 (ray r)).le_opNorm (θ : R2)
  have h := jacobian_bound _ _ _ (inner_bound hp hv hd hvd)
  apply h.trans_eq
  congr 2
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hn := zero_le_one.trans hr.1.le
  have hw : phi (ray r) = r - 1 := by
    simp [phi, ray, norm_ray θ hn, max_eq_left (sub_nonneg.mpr hr.1.le)]
  simp only [moment, gradTerm, Real.norm_eq_abs]
  rw [show r • (θ : R2) = ray r from rfl, hw, abs_of_nonneg
    (mul_nonneg (sub_nonneg.mpr hr.1.le) (norm_nonneg _))]

private lemma norm_moment {p : ℝ} (hp : 0 < p) {s : Set R2} (hs : MeasurableSet s)
    {u : R2 → ℝ} (hu : ContinuousOn u s) :
    eLpNorm u (ENNReal.ofReal p) (volume.restrict s) =
      (∫⁻ x in s, moment p u x) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top (hu.aestronglyMeasurable hs), ENNReal.toReal_ofReal hp.le]
  simp only [moment, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ofReal_norm]

/-- **Weighted Hardy inequality on the annulus.** For $r > 0$ let $B_r$ be the open disc of
radius $r$ about the origin of $\mathbb{R}^2$, let $|x|$ be the Euclidean norm, and let
$\phi(x) = \max\{|x| - 1, 0\}$ be the distance from $x$ to the closed unit disc. Let
$\Omega_1 = B_3 \setminus \overline{B}_1$ and $\Omega_2 = B_3 \setminus \overline{B}_2$, with
Lebesgue measure. For every real number $p \ge 1$ there is a constant $C > 0$ such that every
function $u \colon \mathbb{R}^2 \to \mathbb{R}$ that is continuously differentiable on $\Omega_1$,
and for which $\|\phi \, |\nabla u|\|_{L^p(\Omega_1)}$ and $\|u\|_{L^p(\Omega_2)}$ are finite,
satisfies
$$\|u\|_{L^p(\Omega_1)} \le C \|\phi \, |\nabla u|\|_{L^p(\Omega_1)} + C \|u\|_{L^p(\Omega_2)}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_77.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_eLpNorm_le_weighted_grad_add_outer_annulus
  (p : ℝ)
  (hp : 1 ≤ p) :
  ∃ C : ℝ, 0 < C ∧
    ∀ u : R2 → ℝ,
      ContDiffOn ℝ 1 u Omega1 →
      eLpNorm (fun x : R2 => phi x * ‖fderivWithin ℝ u Omega1 x‖)
          (ENNReal.ofReal p) (volume.restrict Omega1) ≠ ⊤ →
      eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega2) ≠ ⊤ →
      eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega1) ≤
        ENNReal.ofReal C *
            eLpNorm (fun x : R2 => phi x * ‖fderivWithin ℝ u Omega1 x‖)
              (ENNReal.ofReal p) (volume.restrict Omega1) +
          ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega2) := by
  have hp₀ : 0 < p := by linarith
  let K := 17 + 2 * (2 * p) ^ p
  have hK₀ : 0 < K := by dsimp [K]; positivity
  refine ⟨K ^ (1 / p), Real.rpow_pos_of_pos hK₀ _, ?_⟩
  intro u hu _ _
  have h₁ : Omega1 = shell 1 := annulus_shell one_ne_zero
  have h₂ : Omega2 = shell 2 := annulus_shell (by norm_num)
  have hopen : IsOpen Omega1 := h₁ ▸ shell_open 1
  have hsub : shell 2 ⊆ shell 1 := fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
  have hc : ContinuousOn (gradTerm u) Omega1 := by
    apply ContinuousOn.mul
    · exact (((continuous_norm.sub continuous_const).max continuous_const).continuousOn)
    · exact (hu.continuousOn_fderivWithin hopen.uniqueDiffOn le_rfl).norm
  have hu₁ := h₁ ▸ hu.continuousOn
  have hu₂ := hu₁.mono hsub
  have hg := h₁ ▸ hc
  have hmoment {f : R2 → ℝ} {s : Set R2} (h : ContinuousOn f s) :
      ContinuousOn (moment p f) s :=
    ENNReal.continuous_ofReal.comp_continuousOn (h.norm.rpow_const fun _ _ ↦ Or.inr hp₀.le)
  obtain ⟨_, hfull⟩ := polar (by norm_num : (0 : ℝ) ≤ 1) (hmoment hu₁)
  obtain ⟨mouter, houter⟩ := polar (by norm_num : (0 : ℝ) ≤ 2) (hmoment hu₂)
  obtain ⟨_, hgrad⟩ := polar (by norm_num : (0 : ℝ) ≤ 1) (hmoment hg)
  have bound := lintegral_mono (μ := (volume : Measure R2).toSphere) (ray_bound hp hu)
  rw [lintegral_add_left (f := fun θ ↦ 17 * rayIntegral 2 (moment p u) θ)
      (measurable_const.mul mouter), lintegral_const_mul _ mouter,
    lintegral_const_mul' _ _ (by finiteness), ← hfull, ← houter, ← hgrad] at bound
  have hk := Real.rpow_nonneg (by positivity : 0 ≤ 2 * p) p
  have hk₁ : (17 : ℝ≥0∞) ≤ ENNReal.ofReal K := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show 17 ≤ K by dsimp [K]; linarith)
  have hk₂ : 2 * ENNReal.ofReal ((2 * p) ^ p) ≤ ENNReal.ofReal K := by
    rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by dsimp [K]; linarith)
  have H := bound.trans (add_le_add (mul_le_mul_left hk₁ _) (mul_le_mul_left hk₂ _))
  rw [← mul_add, add_comm (∫⁻ x in shell 2, _)] at H
  change eLpNorm u _ _ ≤ _ * eLpNorm (gradTerm u) _ _ + _ * eLpNorm u _ _
  rw [h₁, h₂, norm_moment hp₀ (shell_open 1).measurableSet hu₁,
    norm_moment hp₀ (shell_open 1).measurableSet hg,
    norm_moment hp₀ (shell_open 2).measurableSet hu₂]
  have hq : 0 ≤ 1 / p := by positivity
  have H' := ENNReal.rpow_le_rpow H hq
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq, ENNReal.ofReal_rpow_of_nonneg hK₀.le hq] at H'
  rw [← mul_add]
  exact H'.trans (mul_le_mul_right (ENNReal.rpow_add_le_add_rpow _ _ hq
    ((div_le_one hp₀).mpr hp)) _)

end MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedHardyInequalityWanted
