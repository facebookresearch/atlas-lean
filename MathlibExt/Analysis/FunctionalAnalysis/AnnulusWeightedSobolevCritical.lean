/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_65.lean` (OpenBMB MA-ProofBench):
Copyright (c) 2026 OpenBMB.
Authors: L. Pu et al.
Licensed under the MIT License.

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

The definitions and theorem statement are adapted from openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029, also distributed in the Hugging Face dataset
openbmb/MA-ProofBench. The proof is new.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Critical weighted Sobolev inequality on an annulus

We bound the critical Sobolev norm of a radially weighted function by its weighted derivative
and its norm on the outer annulus. A radial Hardy estimate provides the unweighted term needed
in the product rule.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedSobolevCriticalWanted

@[expose] public section

/-- **The plane of the critical weighted Sobolev inequality.** $\mathbb{R}^2$ denotes the Euclidean
plane, the space of pairs of real numbers with the Euclidean norm. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- **Discs about the origin for the critical weighted Sobolev inequality.** For a real number $r$,
$B_r$ is the open disc $\{x \in \mathbb{R}^2 : |x| < r\}$ of radius $r$ about the origin of the
Euclidean plane $\mathbb{R}^2$. -/
noncomputable abbrev B (r : ℝ) : Set R2 := Metric.ball (0 : R2) r

/-- **The annulus of the critical weighted Sobolev inequality.** Let $B_r$ denote the open disc of
radius $r$ about the origin of the Euclidean plane $\mathbb{R}^2$. The annulus $\Omega_1$ is
$B_3 \setminus \overline{B}_1$, the set of points of $B_3$ outside the closure of $B_1$, that is,
$\Omega_1 = \{x \in \mathbb{R}^2 : 1 < |x| < 3\}$. -/
noncomputable abbrev Omega1 : Set R2 := B 3 \ closure (B 1)

/-- **The outer annulus of the critical weighted Sobolev inequality.** Let $B_r$ denote the open
disc of radius $r$ about the origin of the Euclidean plane $\mathbb{R}^2$. The outer annulus
$\Omega_2$ is $B_3 \setminus \overline{B}_2$, the set of points of $B_3$ outside the closure of
$B_2$, that is, $\Omega_2 = \{x \in \mathbb{R}^2 : 2 < |x| < 3\}$. -/
noncomputable abbrev Omega2 : Set R2 := B 3 \ closure (B 2)

/-- **The weight of the critical weighted Sobolev inequality.** For $x$ in the Euclidean plane
$\mathbb{R}^2$, the weight is $\phi(x) = \max\{|x| - 1, 0\}$, the distance from $x$ to the closed
unit disc. -/
noncomputable def phi (x : R2) : ℝ := max (‖x‖ - 1) 0

/-- **Sobolev conjugate exponent in dimension two.** For a real number $p$, the Sobolev conjugate
exponent is $p^* = 2p/(2 - p)$ (at $p = 2$, where the denominator vanishes, this is $0$ by the
convention that division by zero gives zero). -/
noncomputable def pStar (p : ℝ) : ℝ := 2 * p / (2 - p)

end

private theorem norm_sub_le_setIntegral {f g : ℝ → ℝ} {a b x y : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg₀ : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hd : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t ∧ ‖deriv f t‖ ≤ g t)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ≤ ∫ t in Icc a b, g t := by
  suffices h : ∀ {x y : ℝ}, x ∈ Icc a b → y ∈ Icc a b → x ≤ y →
      ‖f y - f x‖ ≤ ∫ t in Icc a b, g t by
    rcases le_total x y with hxy | hyx
    · rw [norm_sub_rev]
      exact h hx hy hxy
    · exact h hy hx hyx
  intro x y hx hy hxy
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hgi : IntegrableOn g (Icc a b) := hg.integrableOn_compact isCompact_Icc
  calc
    ‖f y - f x‖ ≤ ∫ t in x..y, g t := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hxy (hf.mono hsub)
      · exact fun t ht => (hd t (hsub (Ioo_subset_Icc_self ht))).1.differentiableWithinAt
      · exact ae_of_all _ fun t ht => (hd t (hsub (Ioo_subset_Icc_self ht))).2
      · apply (hg.mono hsub).intervalIntegrable_of_Icc hxy
    _ ≤ ∫ t in Icc a b, g t := by
      rw [intervalIntegral.integral_of_le hxy, ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_mono_set hgi (ae_restrict_of_forall_mem measurableSet_Icc hg₀)
        (ae_of_all _ fun _ ht => hsub ht)

private theorem abs_rpow_sub_bound {f g : ℝ → ℝ} {a b x y p : ℝ}
    (hp : 1 ≤ p) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg₀ : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hd : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t ∧ ‖deriv f t‖ ≤ g t)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x‖ ^ p ≤ ‖f y‖ ^ p + ∫ t in Icc a b, p * ‖f t‖ ^ (p - 1) * g t := by
  rcases hp.eq_or_lt with rfl | hp
  · simp only [Real.rpow_one, sub_self, Real.rpow_zero, mul_one, one_mul]
    calc
      ‖f x‖ = ‖f y + (f x - f y)‖ := by rw [add_sub_cancel]
      _ ≤ ‖f y‖ + ‖f x - f y‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right (norm_sub_le_setIntegral hf hg hg₀ hd hx hy) _
  let H (t : ℝ) := p * ‖f t‖ ^ (p - 1) * g t
  have hH : ContinuousOn H (Icc a b) :=
    (continuousOn_const.mul (hf.norm.rpow_const fun _ _ => Or.inr (by linarith))).mul hg
  have hH₀ (t) (ht : t ∈ Icc a b) : 0 ≤ H t :=
    mul_nonneg (by dsimp [H]; positivity) (hg₀ t ht)
  have hF : ContinuousOn (fun t => ‖f t‖ ^ p) (Icc a b) :=
    hf.norm.rpow_const fun _ _ => Or.inr (by linarith)
  have hD (t) (ht : t ∈ Icc a b) :
      DifferentiableAt ℝ (fun t => ‖f t‖ ^ p) t ∧
        ‖deriv (fun t => ‖f t‖ ^ p) t‖ ≤ H t := by
    have h := ((hasDerivAt_norm_rpow (f t) hp).comp t (hd t ht).1.hasDerivAt)
    refine ⟨h.differentiableAt, ?_⟩
    change ‖deriv ((fun x => ‖x‖ ^ p) ∘ f) t‖ ≤ H t
    rw [h.deriv, norm_mul, norm_mul, norm_mul, Real.norm_eq_abs p,
      abs_of_pos (zero_lt_one.trans hp), Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      mul_assoc p, ← Real.rpow_add_one' (norm_nonneg _) (by linarith : p - 2 + 1 ≠ 0)]
    rw [show p - 2 + 1 = p - 1 by ring]
    exact mul_le_mul_of_nonneg_left (hd t ht).2 (by positivity)
  have h := norm_sub_le_setIntegral hF hH hH₀ hD hx hy
  rw [Real.norm_eq_abs] at h
  linarith [le_abs_self (‖f x‖ ^ p - ‖f y‖ ^ p)]

private theorem hardy_integrand_le {p u v : ℝ} (hp : 1 ≤ p) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    p * u ^ (p - 1) * v ≤ u ^ p / 2 + (p * (2 * p) ^ (p - 1)) * v ^ p := by
  have he : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have hu' : u ^ (p - 1) * u = u ^ p := by
    rw [← Real.rpow_add_one' hu (by linarith : p - 1 + 1 ≠ 0), sub_add_cancel]
  have hv' : v ^ (p - 1) * v = v ^ p := by
    rw [← Real.rpow_add_one' hv (by linarith : p - 1 + 1 ≠ 0), sub_add_cancel]
  by_cases h : 2 * p * v ≤ u
  · calc
      p * u ^ (p - 1) * v = u ^ (p - 1) * (2 * p * v) / 2 := by ring
      _ ≤ u ^ (p - 1) * u / 2 := by gcongr
      _ ≤ _ := by rw [hu']; exact le_add_of_nonneg_right (by positivity)
  · calc
      p * u ^ (p - 1) * v ≤ p * (2 * p * v) ^ (p - 1) * v := by
        gcongr
        exact le_of_not_ge h
      _ = (p * (2 * p) ^ (p - 1)) * v ^ p := by
        rw [Real.mul_rpow (by positivity) hv, ← hv']
        ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

open intervalIntegral in
private theorem integral_tail {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, ∫ t in x..b, g t) = ∫ t in a..b, (t - a) * g t := by
  let F (x : ℝ) := ∫ t in x..b, g t
  have hi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab
  have hF : ContinuousOn F (uIcc a b) := by
    apply continuousOn_primitive_interval_left
    rw [uIcc_of_le hab]
    exact hg.integrableOn_compact isCompact_Icc
  have hD (x : ℝ) (hx : x ∈ Ioo (min a b) (max a b)) : HasDerivAt F (-g x) x := by
    have hx' : x ∈ Ioo a b := by simpa [min_eq_left hab, max_eq_right hab] using hx
    have hc := (hg.mono Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds hx')
    exact integral_hasDerivAt_left
      ((hg.mono (Icc_subset_Icc_left hx'.1.le)).intervalIntegrable_of_Icc hx'.2.le)
      ((hg.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx') hc
  have hW : Continuous (fun x : ℝ => x - a) := continuous_id.sub continuous_const
  have h := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hF hW.continuousOn hD
    (fun x _ => (hasDerivAt_id x).sub_const a) hi.neg
    (continuous_const.intervalIntegrable a b)
  simpa [F, neg_mul, mul_comm (g _) (_ - a)] using h

open intervalIntegral in
/-- The unweighted radial norm is controlled by the weighted derivative and outer norm. -/
private theorem radial_integral_le {p a b : ℝ} (hp : 1 ≤ p) (ha : 1 ≤ a) (ha' : a ≤ 2)
    (hb : 5 / 2 ≤ b) {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hg₀ : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hd : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t ∧ ‖deriv f t‖ ≤ g t) :
    (∫ t in Icc a b, ‖f t‖ ^ p) ≤
      6 * (∫ t in Icc 2 b, ‖f t‖ ^ p) +
        (2 * (p * (2 * p) ^ (p - 1))) * ∫ t in Icc a b, ((t - 1) * g t) ^ p := by
  let U (t : ℝ) := ‖f t‖ ^ p
  let W (t : ℝ) := (t - 1) * g t
  let H (t : ℝ) := p * ‖f t‖ ^ (p - 1) * g t
  have hab : a ≤ b := by linarith
  have hU : ContinuousOn U (Icc a b) :=
    hf.norm.rpow_const (fun _ _ => Or.inr (by linarith))
  have hW : ContinuousOn W (Icc a b) := (continuous_id.sub continuous_const).continuousOn.mul hg
  have hH : ContinuousOn H (Icc a b) :=
    (continuousOn_const.mul (hf.norm.rpow_const fun _ _ => Or.inr (sub_nonneg.mpr hp))).mul hg
  have hH₀ (t) (ht : t ∈ Icc a b) : 0 ≤ H t :=
    mul_nonneg (by dsimp [H]; positivity) (hg₀ t ht)
  have hJ : ContinuousOn (fun t => (t - 1) * H t) (Icc a b) :=
    (continuous_id.sub continuous_const).continuousOn.mul hH
  have hsplit : (∫ t in a..2, U t) + (∫ t in 2..b, U t) = ∫ t in a..b, U t :=
    integral_add_adjacent_intervals
      ((hU.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc ha')
      ((hU.mono (Icc_subset_Icc_left ha')).intervalIntegrable_of_Icc (by linarith))
  -- Anchor the radial estimate at a point of the outer annulus.
  have hbound (y : ℝ) (hy : y ∈ Icc 2 (5 / 2)) :
      (∫ t in a..2, U t) ≤ U y + ∫ t in a..b, (t - 1) * H t := by
    have hay : a ≤ y := ha'.trans hy.1
    have hyb : y ≤ b := hy.2.trans hb
    let F (x : ℝ) := ∫ t in x..y, H t
    have hFi : ContinuousOn F (Icc a y) := by
      rw [← uIcc_of_le hay]
      apply continuousOn_primitive_interval_left
      rw [uIcc_of_le hay]
      exact (hH.mono (Icc_subset_Icc_right hyb)).integrableOn_compact isCompact_Icc
    have hF₀ (x : ℝ) (hx : x ∈ Icc a y) : 0 ≤ F x :=
      integral_nonneg hx.2 fun t ht => hH₀ t ((Icc_subset_Icc hx.1 hyb) ht)
    have hsub : Icc a 2 ⊆ Icc a y := Icc_subset_Icc_right hy.1
    have hU' : IntervalIntegrable U volume a 2 :=
      (hU.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc ha'
    have hF' : IntervalIntegrable F volume a 2 :=
      (hFi.mono hsub).intervalIntegrable_of_Icc ha'
    calc
      (∫ t in a..2, U t) ≤ ∫ t in a..2, U y + F t := by
        apply integral_mono_on ha' hU' ((intervalIntegrable_const).add hF')
        intro x hx
        have hxy := (hsub hx).2
        have hs : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hyb
        have h := abs_rpow_sub_bound hp (hf.mono hs) (hg.mono hs)
          (fun t ht => hg₀ t (hs ht)) (fun t ht => hd t (hs ht))
          (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
        rwa [integral_Icc_eq_integral_Ioc, ← integral_of_le hxy] at h
      _ = (2 - a) * U y + (∫ t in a..2, F t) := by
        rw [integral_add intervalIntegrable_const hF', intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ U y + (∫ t in a..y, F t) := by
        apply add_le_add
        · exact mul_le_of_le_one_left (by dsimp [U]; positivity) (by linarith)
        · rw [integral_of_le ha', integral_of_le hay, ← integral_Icc_eq_integral_Ioc,
            ← integral_Icc_eq_integral_Ioc]
          exact setIntegral_mono_set (hFi.integrableOn_compact isCompact_Icc)
            (ae_restrict_of_forall_mem measurableSet_Icc hF₀) (ae_of_all _ fun _ ht => hsub ht)
      _ ≤ _ := by
        rw [show (∫ t in a..y, F t) = ∫ t in a..y, (t - a) * H t from
          integral_tail hay (hH.mono (Icc_subset_Icc_right hyb))]
        gcongr
        calc
          (∫ t in a..y, (t - a) * H t) ≤ ∫ t in a..y, (t - 1) * H t := by
            apply integral_mono_on hay
            · exact (((continuous_id.sub continuous_const).continuousOn).mul
                (hH.mono (Icc_subset_Icc_right hyb))).intervalIntegrable_of_Icc hay
            · exact (hJ.mono (Icc_subset_Icc_right hyb)).intervalIntegrable_of_Icc hay
            · exact fun t ht => mul_le_mul_of_nonneg_right (by linarith)
                (hH₀ t (Icc_subset_Icc_right hyb ht))
          _ ≤ _ := by
            rw [integral_of_le hay, integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
              ← integral_Icc_eq_integral_Ioc]
            exact setIntegral_mono_set (hJ.integrableOn_compact isCompact_Icc)
              (ae_restrict_of_forall_mem measurableSet_Icc fun t ht =>
                mul_nonneg (by linarith [ht.1]) (hH₀ t ht))
              (ae_of_all _ fun _ ht => Icc_subset_Icc_right hyb ht)
  have hminSet : Icc (2 : ℝ) (5 / 2) ⊆ Icc a b := Icc_subset_Icc ha' hb
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by norm_num : (2 : ℝ) ≤ 5 / 2)) (hU.mono hminSet)
  have hyBound : U y ≤ 2 * ∫ t in 2..b, U t := by
    have hhalf : (1 / 2 : ℝ) * U y ≤ ∫ t in 2..(5 / 2), U t := by
      have h := integral_mono_on (μ := volume) (by norm_num : (2 : ℝ) ≤ 5 / 2)
        (f := fun _ => U y) (g := U) intervalIntegrable_const
        ((hU.mono hminSet).intervalIntegrable_of_Icc (by norm_num)) (fun t ht => hmin ht)
      rw [intervalIntegral.integral_const, smul_eq_mul] at h
      linarith
    have hle : (∫ t in 2..(5 / 2), U t) ≤ ∫ t in 2..b, U t := by
      rw [integral_of_le (by norm_num : (2 : ℝ) ≤ 5 / 2), integral_of_le (by linarith : 2 ≤ b),
        ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_mono_set ((hU.mono (Icc_subset_Icc_left ha')).integrableOn_compact
        (μ := volume) isCompact_Icc) (ae_of_all _ fun _ => by dsimp [U]; positivity)
        (ae_of_all _ fun _ ht => Icc_subset_Icc_right hb ht)
    linarith
  have hW' : ContinuousOn (fun t => W t ^ p) (Icc a b) :=
    hW.rpow_const fun _ _ => Or.inr (by linarith)
  have hUi : IntervalIntegrable U volume a b := hU.intervalIntegrable_of_Icc hab
  have hWi : IntervalIntegrable (fun t => W t ^ p) volume a b := hW'.intervalIntegrable_of_Icc hab
  have hYoung : (∫ t in a..b, (t - 1) * H t) ≤ (∫ t in a..b, U t) / 2 +
      (p * (2 * p) ^ (p - 1)) * ∫ t in a..b, W t ^ p := by
    have hmono := integral_mono_on hab (hJ.intervalIntegrable_of_Icc hab)
      ((hUi.div_const 2).add (hWi.const_mul (p * (2 * p) ^ (p - 1)))) (fun t ht => by
        have ht₀ : 0 ≤ t - 1 := sub_nonneg.mpr (ha.trans ht.1)
        have h := hardy_integrand_le hp (norm_nonneg (f t)) (mul_nonneg ht₀ (hg₀ t ht))
        dsimp only [H, U, W]
        rw [show (t - 1) * (p * ‖f t‖ ^ (p - 1) * g t) =
          p * ‖f t‖ ^ (p - 1) * ((t - 1) * g t) by ring]
        exact h)
    rwa [integral_add (hUi.div_const 2) (hWi.const_mul _), intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul] at hmono
  simp only [integral_Icc_eq_integral_Ioc, ← integral_of_le hab,
    ← integral_of_le (show (2 : ℝ) ≤ b by linarith)]
  change (∫ t in a..b, U t) ≤ 6 * (∫ t in 2..b, U t) +
    (2 * (p * (2 * p) ^ (p - 1))) * ∫ t in a..b, W t ^ p
  linarith [hbound y hy]

private theorem ofReal_rpow_norm {p : ℝ} (hp : 0 ≤ p) (x : ℝ) :
    ENNReal.ofReal (‖x‖ ^ p) = ‖x‖ₑ ^ p := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp, ofReal_norm]

private theorem line_power_bound {a b x γ : ℝ} (hab : 1 ≤ b - a) (hγ : 1 ≤ γ)
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg₀ : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hd : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t ∧ ‖deriv f t‖ ≤ g t)
    (hx : x ∈ Icc a b) :
    ‖f x‖ₑ ^ γ ≤ ∫⁻ t in Icc a b,
      ‖f t‖ₑ ^ γ + ENNReal.ofReal γ * ‖f t‖ₑ ^ (γ - 1) * ENNReal.ofReal (g t) := by
  let U (t : ℝ) := ‖f t‖ ^ γ
  let G (t : ℝ) := γ * ‖f t‖ ^ (γ - 1) * g t
  have hU : ContinuousOn U (Icc a b) := hf.norm.rpow_const fun _ _ => Or.inr (by linarith)
  have hG : ContinuousOn G (Icc a b) :=
    (continuousOn_const.mul (hf.norm.rpow_const fun _ _ => Or.inr (by linarith))).mul hg
  have hGi : IntegrableOn G (Icc a b) := hG.integrableOn_compact isCompact_Icc
  have hUi : IntegrableOn U (Icc a b) := hU.integrableOn_compact isCompact_Icc
  have hG₀ (t) (ht : t ∈ Icc a b) : 0 ≤ G t :=
    mul_nonneg (by dsimp [G]; positivity) (hg₀ t ht)
  let K := ∫ t in Icc a b, G t
  have hK : 0 ≤ K := setIntegral_nonneg measurableSet_Icc hG₀
  have hC : Integrable (fun _ : ℝ => U x - K) (volume.restrict (Icc a b)) :=
    integrable_const _
  have h := setIntegral_mono_on hC hUi measurableSet_Icc (fun y hy =>
    sub_le_iff_le_add.mpr (abs_rpow_sub_bound hγ hf hg hg₀ hd hx hy))
  rw [setIntegral_const, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at h
  have hU₀ : 0 ≤ (∫ t in Icc a b, U t) :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have hle : U x ≤ ∫ t in Icc a b, U t + G t := by
    rw [integral_add hUi hGi]
    have hle' : U x - K ≤ ∫ t in Icc a b, U t := by
      by_cases hsign : 0 ≤ U x - K
      · exact (le_mul_of_one_le_left hsign hab).trans h
      · exact (le_of_not_ge hsign).trans hU₀
    linarith
  have hγ₀ : 0 ≤ γ := by linarith
  rw [← ofReal_rpow_norm hγ₀]
  refine (ENNReal.ofReal_le_ofReal hle).trans_eq ?_
  change ENNReal.ofReal (∫ t in Icc a b, (U + G) t) = _
  rw [ofReal_integral_eq_lintegral_ofReal (hUi.add hGi)
    (ae_restrict_of_forall_mem measurableSet_Icc fun t ht =>
      add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hG₀ t ht))]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  change ENNReal.ofReal (U t + G t) = _
  rw [ENNReal.ofReal_add (Real.rpow_nonneg (norm_nonneg _) _) (hG₀ t ht)]
  dsimp only [U, G]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ γ * ‖f t‖ ^ (γ - 1)),
    ENNReal.ofReal_mul hγ₀, ofReal_rpow_norm hγ₀, ofReal_rpow_norm (sub_nonneg.mpr hγ)]

section Rectangle

variable {a b c d : ℝ}

private abbrev rectangle (a b c d : ℝ) := Icc a b ×ˢ Icc c d

private theorem rect_power {γ : ℝ} (hab : 1 ≤ b - a) (hcd : 1 ≤ d - c) (hγ : 1 ≤ γ)
    {f g : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (rectangle a b c d)) (hg : ContinuousOn g (rectangle a b c d))
    (hg₀ : ∀ z ∈ rectangle a b c d, 0 ≤ g z)
    (hDx : ∀ z ∈ rectangle a b c d, DifferentiableAt ℝ (fun x => f (x, z.2)) z.1 ∧
      ‖deriv (fun x => f (x, z.2)) z.1‖ ≤ g z)
    (hDy : ∀ z ∈ rectangle a b c d, DifferentiableAt ℝ (fun y => f (z.1, y)) z.2 ∧
      ‖deriv (fun y => f (z.1, y)) z.2‖ ≤ g z) :
    (∫⁻ z in rectangle a b c d, ‖f z‖ₑ ^ (2 * γ)) ≤
      (∫⁻ z in rectangle a b c d,
        ‖f z‖ₑ ^ γ + ENNReal.ofReal γ * ‖f z‖ₑ ^ (γ - 1) * ENNReal.ofReal (g z)) ^ 2 := by
  let A (z : ℝ × ℝ) :=
    ‖f z‖ₑ ^ γ + ENNReal.ofReal γ * ‖f z‖ₑ ^ (γ - 1) * ENNReal.ofReal (g z)
  let X (y : ℝ) := ∫⁻ x in Icc a b, A (x, y)
  let Y (x : ℝ) := ∫⁻ y in Icc c d, A (x, y)
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let ν : Measure ℝ := volume.restrict (Icc c d)
  have hm : MeasurableSet (rectangle a b c d) := measurableSet_Icc.prod measurableSet_Icc
  have hμν : μ.prod ν = volume.restrict (rectangle a b c d) := by
    dsimp [μ, ν]
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hAm : AEMeasurable A (μ.prod ν) := by
    rw [hμν]
    have hf' := (hf.aestronglyMeasurable hm (μ := volume)).eNorm
    have hg' := (hg.aestronglyMeasurable hm (μ := volume)).aemeasurable.ennreal_ofReal
    exact (hf'.pow_const γ).add ((aemeasurable_const.mul (hf'.pow_const (γ - 1))).mul hg')
  -- The line estimates depend on one coordinate each, so their product integrates by Tonelli.
  have hX (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
      ‖f (x, y)‖ₑ ^ γ ≤ X y := by
    have hm' : MapsTo (fun t : ℝ => (t, y)) (Icc a b) (rectangle a b c d) :=
      fun _ ht => ⟨ht, hy⟩
    exact line_power_bound hab hγ (hf.comp (by fun_prop) hm') (hg.comp (by fun_prop) hm')
      (fun t ht => hg₀ (t, y) (hm' ht)) (fun t ht => hDx (t, y) (hm' ht)) hx
  have hY (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
      ‖f (x, y)‖ₑ ^ γ ≤ Y x := by
    have hm' : MapsTo (fun t : ℝ => (x, t)) (Icc c d) (rectangle a b c d) :=
      fun _ ht => ⟨hx, ht⟩
    exact line_power_bound hcd hγ (hf.comp (by fun_prop) hm') (hg.comp (by fun_prop) hm')
      (fun t ht => hg₀ (x, t) (hm' ht)) (fun t ht => hDy (x, t) (hm' ht)) hy
  change (∫⁻ z in rectangle a b c d, ‖f z‖ₑ ^ (2 * γ)) ≤
    (∫⁻ z in rectangle a b c d, A z) ^ 2
  calc
    (∫⁻ z in rectangle a b c d, ‖f z‖ₑ ^ (2 * γ)) ≤
        ∫⁻ z in rectangle a b c d, Y z.1 * X z.2 := by
      apply setLIntegral_mono' hm
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      rw [two_mul, ENNReal.rpow_add_of_nonneg γ γ (by linarith) (by linarith)]
      exact mul_le_mul' (hY x y hx hy) (hX x y hx hy)
    _ = (∫⁻ z in rectangle a b c d, A z) ^ 2 := by
      rw [← hμν, lintegral_prod_mul hAm.lintegral_prod_right' hAm.lintegral_prod_left',
        ← lintegral_prod A hAm, ← lintegral_prod_symm A hAm, pow_two]

private theorem rect_sobolev {p : ℝ} (hp : 1 ≤ p) (hp' : p < 2)
    (hab : 1 ≤ b - a) (hcd : 1 ≤ d - c) {f g : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (rectangle a b c d)) (hg : ContinuousOn g (rectangle a b c d))
    (hg₀ : ∀ z ∈ rectangle a b c d, 0 ≤ g z)
    (hDx : ∀ z ∈ rectangle a b c d, DifferentiableAt ℝ (fun x => f (x, z.2)) z.1 ∧
      ‖deriv (fun x => f (x, z.2)) z.1‖ ≤ g z)
    (hDy : ∀ z ∈ rectangle a b c d, DifferentiableAt ℝ (fun y => f (z.1, y)) z.2 ∧
      ‖deriv (fun y => f (z.1, y)) z.2‖ ≤ g z) :
    eLpNorm' f (pStar p) (volume.restrict (rectangle a b c d)) ≤
      ENNReal.ofReal (p / (2 - p)) *
        eLpNorm' (fun z => ‖f z‖ + g z) p (volume.restrict (rectangle a b c d)) := by
  let S := rectangle a b c d
  let μ : Measure (ℝ × ℝ) := volume.restrict S
  let γ := p / (2 - p)
  let F (z : ℝ × ℝ) := ‖f z‖ + g z
  let A (z : ℝ × ℝ) :=
    ‖f z‖ₑ ^ γ + ENNReal.ofReal γ * ‖f z‖ₑ ^ (γ - 1) * ENNReal.ofReal (g z)
  have hγ : 1 ≤ γ := (le_div_iff₀ (by linarith)).2 (by linarith)
  have hγ' : 0 < γ := by linarith
  have hq : pStar p = 2 * γ := by unfold pStar γ; ring
  have hm : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hf' : AEStronglyMeasurable f μ := hf.aestronglyMeasurable hm
  have hF : AEStronglyMeasurable F μ := (hf.norm.add hg).aestronglyMeasurable hm
  let L := eLpNorm' f (pStar p) μ
  have hL : L ^ γ ≤ ∫⁻ z, A z ∂μ := by
    have h := rect_power hab hcd hγ hf hg hg₀ hDx hDy
    change (∫⁻ z, ‖f z‖ₑ ^ (2 * γ) ∂μ) ≤ (∫⁻ z, A z ∂μ) ^ 2 at h
    dsimp only [L]
    rw [eLpNorm'_eq_lintegral_eNorm, hq, ← ENNReal.rpow_mul,
      show 1 / (2 * γ) * γ = 1 / 2 by field_simp]
    rw [one_div, ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2), ENNReal.rpow_two]
    exact h
  have hF₀ (z : ℝ × ℝ) (hz : z ∈ S) : 0 ≤ F z :=
    add_nonneg (norm_nonneg _) (hg₀ z hz)
  have hFnorm (z : ℝ × ℝ) (hz : z ∈ S) :
      ‖F z‖ₑ = ‖f z‖ₑ + ENNReal.ofReal (g z) := by
    rw [← ofReal_norm, Real.norm_of_nonneg (hF₀ z hz), show F z = ‖f z‖ + g z from rfl,
      ENNReal.ofReal_add (norm_nonneg _) (hg₀ z hz), ofReal_norm]
  change L ≤ ENNReal.ofReal γ * eLpNorm' F p μ
  rcases hp.eq_or_lt with hp | hp
  · have hγ1 : γ = 1 := by norm_num [γ, ← hp]
    have h : (∫⁻ z, A z ∂μ) = eLpNorm' F p μ := by
      rw [eLpNorm'_eq_lintegral_eNorm, ← hp]
      simp only [one_div, inv_one, ENNReal.rpow_one]
      apply setLIntegral_congr_fun hm
      intro z hz
      simp [A, hγ1, hFnorm z hz]
    simpa [hγ1, h] using hL
  let q := Real.conjExponent p
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hqγ : (γ - 1) * q = 2 * γ := by
    rw [hpq.conjugate_eq]
    dsimp only [γ]
    field_simp
    ring
  have hqInv : 1 / (2 * γ) * (γ - 1) = 1 / q := by
    have hqpos := hpq.symm.pos
    apply (eq_div_iff hqpos.ne').2
    rw [mul_assoc, hqγ]
    field_simp
  have hprod : (∫⁻ z, ‖F z‖ₑ * ‖f z‖ₑ ^ (γ - 1) ∂μ) ≤
      eLpNorm' F p μ * L ^ (γ - 1) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hF.eNorm
      (hf'.eNorm.pow_const (γ - 1))
    simpa only [Pi.mul_apply, eLpNorm'_eq_lintegral_eNorm, L, hq, ← ENNReal.rpow_mul,
      hqγ, hqInv] using h
  have hA : (∫⁻ z, A z ∂μ) ≤
      ENNReal.ofReal γ * (∫⁻ z, ‖F z‖ₑ * ‖f z‖ₑ ^ (γ - 1) ∂μ) := by
    have hM : AEMeasurable (fun z => ‖F z‖ₑ * ‖f z‖ₑ ^ (γ - 1)) μ :=
      hF.eNorm.mul (hf'.eNorm.pow_const (γ - 1))
    rw [← lintegral_const_mul'' _ hM]
    apply setLIntegral_mono' hm
    intro z hz
    have hpow : ‖f z‖ₑ ^ γ = ‖f z‖ₑ * ‖f z‖ₑ ^ (γ - 1) := by
      conv_lhs => rw [show γ = 1 + (γ - 1) by ring]
      rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one]
    dsimp only [A]
    rw [hFnorm z hz, hpow, add_mul, mul_add]
    gcongr ?_ + ?_
    · exact le_mul_of_one_le_left' (by simpa using ENNReal.ofReal_le_ofReal hγ)
    · exact le_of_eq (by ring)
  have hLfin : L ≠ ⊤ := by
    have hQc : ContinuousOn (fun z => ‖f z‖ ^ (pStar p)) S :=
      hf.norm.rpow_const fun _ _ => Or.inr (by rw [hq]; positivity)
    have hQi : IntegrableOn (fun z => ‖f z‖ ^ (pStar p)) S :=
      hQc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have h := ofReal_integral_eq_lintegral_ofReal hQi
      (ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg (f z)) (pStar p))
    simp_rw [ofReal_rpow_norm (show 0 ≤ pStar p by rw [hq]; positivity)] at h
    dsimp only [L]
    rw [eLpNorm'_eq_lintegral_eNorm, ← h]
    exact (ENNReal.rpow_lt_top_of_nonneg (by rw [hq]; positivity) ENNReal.ofReal_ne_top).ne
  by_cases hL₀ : L = 0
  · simp [hL₀]
  have hpow : L ^ γ = L * L ^ (γ - 1) := by
    conv_lhs => rw [show γ = 1 + (γ - 1) by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one]
  have h := hL.trans (hA.trans (mul_le_mul' le_rfl hprod))
  rw [hpow, ← mul_assoc] at h
  exact (ENNReal.mul_le_mul_iff_left (c := L ^ (γ - 1))
    (by simp [ENNReal.rpow_eq_zero_iff, hL₀, hLfin])
    (ENNReal.rpow_lt_top_of_nonneg (by linarith) hLfin).ne).1 h

end Rectangle

private theorem annulus_mem {r : ℝ} (hr : r ≠ 0) {x : R2} :
    x ∈ B 3 \ closure (B r) ↔ r < ‖x‖ ∧ ‖x‖ < 3 := by
  simp [B, closure_ball _ hr, and_comm]

private theorem isOpen_omega1 : IsOpen Omega1 := Metric.isOpen_ball.sdiff isClosed_closure

private noncomputable abbrev planeRepr : ℂ ≃ₗᵢ[ℝ] R2 := Complex.orthonormalBasisOneI.repr

private noncomputable def polar (z : ℝ × ℝ) : R2 := planeRepr (Complex.polarCoord.symm z)

private theorem polar_eq (z : ℝ × ℝ) :
    polar z = planeRepr ((z.1 : ℂ) * Complex.exp ((z.2 : ℂ) * Complex.I)) := by
  rw [polar, Complex.polarCoord_symm_apply, Complex.exp_mul_I, Complex.ofReal_cos,
    Complex.ofReal_sin]

private theorem continuous_polar : Continuous polar := by
  convert planeRepr.continuous.comp
    (show Continuous (fun z : ℝ × ℝ => (z.1 : ℂ) * Complex.exp ((z.2 : ℂ) * Complex.I))
      by fun_prop) using 1
  exact funext polar_eq

private theorem norm_polar (z : ℝ × ℝ) : ‖polar z‖ = |z.1| := by
  rw [polar, planeRepr.norm_map, Complex.norm_polarCoord_symm]

private theorem polar_mem {r : ℝ} (hr : 0 < r) {z : ℝ × ℝ} (hz : 0 < z.1) :
    polar z ∈ B 3 \ closure (B r) ↔ z.1 ∈ Ioo r 3 := by
  rw [annulus_mem hr.ne', norm_polar, abs_of_pos hz]
  rfl

private theorem phi_polar {z : ℝ × ℝ} (hz : 1 ≤ z.1) : phi (polar z) = z.1 - 1 := by
  rw [phi, norm_polar, abs_of_nonneg (zero_le_one.trans hz), max_eq_left (sub_nonneg.mpr hz)]

private theorem hasDerivAt_polar_radius (r θ : ℝ) :
    HasDerivAt (fun t => polar (t, θ)) (planeRepr (Complex.exp ((θ : ℂ) * Complex.I))) r := by
  let v := Complex.exp ((θ : ℂ) * Complex.I)
  have h := (Complex.ofRealCLM.hasFDerivAt (x := r)).hasDerivAt.mul_const v
  have h' := planeRepr.toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r h
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    Function.comp_def, polar_eq, Prod.fst, Prod.snd, v] using h'

private theorem hasDerivAt_polar_angle (r θ : ℝ) :
    HasDerivAt (fun t => polar (r, t))
      (planeRepr ((r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))) θ := by
  have hI := (hasDerivAt_id (θ : ℂ)).mul_const Complex.I
  have hE := ((Complex.hasDerivAt_exp ((θ : ℂ) * Complex.I)).comp (θ : ℂ) hI).comp_ofReal
  have h := planeRepr.toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ
    (hE.const_mul (r : ℂ))
  simpa only [id_eq, one_mul, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, Function.comp_def, polar_eq, Prod.fst,
    Prod.snd] using h

private noncomputable abbrev angles := Icc (-Real.pi) Real.pi

private theorem polar_lintegral {r : ℝ} (hr : 0 < r) (F : R2 → ℝ≥0∞) :
    (∫⁻ x in B 3 \ closure (B r), F x) =
      ∫⁻ z in Ioo r 3 ×ˢ angles, ENNReal.ofReal z.1 * F (polar z) := by
  let S := B 3 \ closure (B r)
  let T := Complex.polarCoord.target
  let U := Ioo r 3 ×ˢ Ioo (-Real.pi) Real.pi
  have hS : MeasurableSet S := (Metric.isOpen_ball.sdiff isClosed_closure).measurableSet
  have hT : MeasurableSet T := Complex.polarCoord.open_target.measurableSet
  have hU : MeasurableSet U := measurableSet_Ioo.prod measurableSet_Ioo
  have hUT : U ⊆ T :=
    prod_mono (fun _ hx => hr.trans hx.1) Subset.rfl
  have hTU (z : ℝ × ℝ) (hz : z ∈ T) : polar z ∈ S ↔ z ∈ U := by
    change z ∈ Complex.polarCoord.target at hz
    rw [Complex.polarCoord_target] at hz
    exact (polar_mem hr hz.1).trans (and_iff_left hz.2).symm
  have hAng : U =ᵐ[(volume : Measure (ℝ × ℝ))] Ioo r 3 ×ˢ angles := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_of_all _ fun _ => Iff.rfl) Ioo_ae_eq_Icc
  rw [← Measure.restrict_congr_set hAng]
  change (∫⁻ x in S, F x) = ∫⁻ z in U, ENNReal.ofReal z.1 * F (polar z)
  rw [← lintegral_indicator hS, ← planeRepr.measurePreserving.lintegral_comp_emb
    planeRepr.toHomeomorph.toMeasurableEquiv.measurableEmbedding,
    ← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ z in T, ENNReal.ofReal z.1 * S.indicator F (polar z)) = _
  rw [← Measure.restrict_restrict_of_subset hUT, ← lintegral_indicator hU]
  apply setLIntegral_congr_fun hT
  intro z hz
  change ENNReal.ofReal z.1 * S.indicator F (polar z) = _
  by_cases h : z ∈ U
  · rw [indicator_of_mem h, indicator_of_mem ((hTU z hz).mpr h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (mt (hTU z hz).mp h), mul_zero]

private theorem eLpNorm'_ofReal {f : R2 → ℝ} {p : ℝ} {μ : Measure R2} (hp : 0 < p)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal p) μ = eLpNorm' f p μ := by
  rw [eLpNorm_eq_eLpNorm' (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le]

private theorem le_annulus_norm {r a b p : ℝ} (hr : 1 ≤ r) (ha : r ≤ a) (hb : b < 3)
    (hp : 0 < p) (f : R2 → ℝ) :
    eLpNorm' (f ∘ polar) p (volume.restrict (Icc a b ×ˢ angles)) ≤
      eLpNorm' f p (volume.restrict (B 3 \ closure (B r))) := by
  have hAb : Ioc a b ×ˢ angles ⊆ Ioo r 3 ×ˢ angles :=
    prod_mono (fun _ hx => ⟨ha.trans_lt hx.1, hx.2.trans_lt hb⟩) Subset.rfl
  have hAe : Ioc a b ×ˢ angles =ᵐ[(volume : Measure (ℝ × ℝ))] Icc a b ×ˢ angles := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc (ae_of_all _ fun _ => Iff.rfl)
  rw [eLpNorm'_eq_lintegral_eNorm, eLpNorm'_eq_lintegral_eNorm,
    polar_lintegral (zero_lt_one.trans_le hr), ← Measure.restrict_congr_set hAe]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  calc
    (∫⁻ z in Ioc a b ×ˢ angles, ‖(f ∘ polar) z‖ₑ ^ p) ≤
        ∫⁻ z in Ioo r 3 ×ˢ angles, ‖f (polar z)‖ₑ ^ p :=
      lintegral_mono_set hAb
    _ ≤ _ := by
      apply setLIntegral_mono' (measurableSet_Ioo.prod measurableSet_Icc)
      intro z hz
      have hz₁ : 1 ≤ z.1 := hr.trans hz.1.1.le
      have hR : (1 : ℝ≥0∞) ≤ ENNReal.ofReal z.1 := by
        simpa using ENNReal.ofReal_le_ofReal hz₁
      exact le_mul_of_one_le_left' hR

private theorem annulus_norm_le {p : ℝ} (hp : 0 < p) (f : R2 → ℝ) :
    eLpNorm' f p (volume.restrict Omega1) ≤
      (3 : ℝ≥0∞) ^ (1 / p) *
        eLpNorm' (f ∘ polar) p (volume.restrict (Ioo 1 3 ×ˢ angles)) := by
  rw [eLpNorm'_eq_lintegral_eNorm, eLpNorm'_eq_lintegral_eNorm,
    show Omega1 = B 3 \ closure (B 1) from rfl, polar_lintegral (by norm_num : 0 < (1 : ℝ)),
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  rw [← lintegral_const_mul' _ _ (by simp)]
  apply setLIntegral_mono' (measurableSet_Ioo.prod measurableSet_Icc)
  intro z hz
  apply mul_le_mul' _ le_rfl
  simpa using ENNReal.ofReal_le_ofReal hz.1.2.le

private noncomputable def hardyConstant (p : ℝ) : ℝ :=
  (6 + 2 * (p * (2 * p) ^ (p - 1))) ^ (1 / p)

private theorem radial_rect_norm {a b p : ℝ} (hp : 1 ≤ p) (ha : 1 ≤ a) (ha' : a ≤ 2)
    (hb : 5 / 2 ≤ b) {U D : ℝ × ℝ → ℝ}
    (hU : ContinuousOn U (Icc a b ×ˢ angles)) (hD : ContinuousOn D (Icc a b ×ˢ angles))
    (hD₀ : ∀ z ∈ Icc a b ×ˢ angles, 0 ≤ D z)
    (hDu : ∀ z ∈ Icc a b ×ˢ angles, DifferentiableAt ℝ (fun t => U (t, z.2)) z.1 ∧
      ‖deriv (fun t => U (t, z.2)) z.1‖ ≤ D z) :
    eLpNorm' U p (volume.restrict (Icc a b ×ˢ angles)) ≤ ENNReal.ofReal (hardyConstant p) *
      (eLpNorm' (fun z => (z.1 - 1) * D z) p (volume.restrict (Icc a b ×ˢ angles)) +
        eLpNorm' U p (volume.restrict (Icc 2 b ×ˢ angles))) := by
  let S := Icc a b ×ˢ angles
  let T := Icc 2 b ×ˢ angles
  let W (z : ℝ × ℝ) := (z.1 - 1) * D z
  let K := 2 * (p * (2 * p) ^ (p - 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hp₀ : 0 < p := by linarith
  have hT : T ⊆ S := prod_mono (Icc_subset_Icc_left ha') Subset.rfl
  have hSc : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hTc : MeasurableSet T := measurableSet_Icc.prod measurableSet_Icc
  have hW : ContinuousOn W S := (continuous_fst.sub continuous_const).continuousOn.mul hD
  have h₁ {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hf : ContinuousOn f s)
      (hs : MeasurableSet s) :
      AEMeasurable (fun z => ‖f z‖ₑ ^ p) (volume.restrict s) :=
    (hf.aestronglyMeasurable hs).eNorm.pow_const p
  have hUS := h₁ hU hSc
  have hUT := h₁ (hU.mono hT) hTc
  have hWS := h₁ hW hSc
  have hfubini {l : ℝ} {f : ℝ × ℝ → ℝ}
      (hf : AEMeasurable (fun z => ‖f z‖ₑ ^ p) (volume.restrict (Icc l b ×ˢ angles))) :
      (∫⁻ z in Icc l b ×ˢ angles, ‖f z‖ₑ ^ p) =
        ∫⁻ y in angles, ∫⁻ t in Icc l b, ‖f (t, y)‖ₑ ^ p := by
    rw [Measure.volume_eq_prod] at hf ⊢
    exact setLIntegral_prod_symm _ hf
  have hlin : (∫⁻ z in S, ‖U z‖ₑ ^ p) ≤ 6 * (∫⁻ z in T, ‖U z‖ₑ ^ p) +
      ENNReal.ofReal K * (∫⁻ z in S, ‖W z‖ₑ ^ p) := by
    rw [hfubini hUS, hfubini hUT, hfubini hWS]
    rw [← lintegral_const_mul' _ _ (by simp), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hMeas : AEMeasurable (fun y => ∫⁻ t in Icc 2 b, ‖U (t, y)‖ₑ ^ p)
        (volume.restrict angles) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hUT
      exact hUT.lintegral_prod_left'
    rw [← lintegral_add_left' (hMeas.const_mul 6)]
    apply setLIntegral_mono' measurableSet_Icc
    intro y hy
    have hs : ∀ t ∈ Icc a b, (t, y) ∈ S := fun _ ht => ⟨ht, hy⟩
    have hUc : ContinuousOn (fun t => U (t, y)) (Icc a b) := hU.comp (by fun_prop) hs
    have hDc : ContinuousOn (fun t => D (t, y)) (Icc a b) := hD.comp (by fun_prop) hs
    have hWc : ContinuousOn (fun t => W (t, y)) (Icc a b) := hW.comp (by fun_prop) hs
    have hW₀ (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ W (t, y) :=
      mul_nonneg (sub_nonneg.mpr (ha.trans ht.1)) (hD₀ _ (hs _ ht))
    have h := radial_integral_le hp ha ha' hb hUc hDc (fun t ht => hD₀ _ (hs t ht))
      (fun t ht => hDu _ (hs t ht))
    change (∫ t in Icc a b, ‖U (t, y)‖ ^ p) ≤ 6 * (∫ t in Icc 2 b, ‖U (t, y)‖ ^ p) +
      K * ∫ t in Icc a b, W (t, y) ^ p at h
    have hIntegral {l : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc l b)) :
        ENNReal.ofReal (∫ t in Icc l b, ‖f t‖ ^ p) = ∫⁻ t in Icc l b, ‖f t‖ₑ ^ p := by
      have hi : IntegrableOn (fun t => ‖f t‖ ^ p) (Icc l b) :=
        (hf.norm.rpow_const fun _ _ => Or.inr hp₀.le).integrableOn_compact isCompact_Icc
      rw [ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ fun t => Real.rpow_nonneg (norm_nonneg (f t)) p)]
      simp only [ofReal_rpow_norm hp₀.le]
    have hW' : (∫ t in Icc a b, W (t, y) ^ p) = ∫ t in Icc a b, ‖W (t, y)‖ ^ p := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      simp only [Real.norm_of_nonneg (hW₀ t ht)]
    rw [hW'] at h
    have hO := integral_nonneg (μ := volume.restrict (Icc 2 b))
      (f := fun t => ‖U (t, y)‖ ^ p) (fun t => Real.rpow_nonneg (norm_nonneg _) _)
    have hG := integral_nonneg (μ := volume.restrict (Icc a b))
      (f := fun t => ‖W (t, y)‖ ^ p) (fun t => Real.rpow_nonneg (norm_nonneg _) _)
    have h' := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hO) (mul_nonneg hK hG),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_mul hK,
      hIntegral hUc, hIntegral (hUc.mono (Icc_subset_Icc_left ha')), hIntegral hWc] at h'
    simpa using h'
  let E := eLpNorm' W p (volume.restrict S) + eLpNorm' U p (volume.restrict T)
  have hpow : (∫⁻ z in S, ‖U z‖ₑ ^ p) ≤ (6 + ENNReal.ofReal K) * E ^ p := by
    apply hlin.trans
    rw [add_mul, lintegral_rpow_eNorm_eq_rpow_eLpNorm' hp₀,
      lintegral_rpow_eNorm_eq_rpow_eLpNorm' hp₀]
    gcongr
    · exact le_add_self
    · exact le_self_add
  change eLpNorm' U p (volume.restrict S) ≤ ENNReal.ofReal (hardyConstant p) * E
  rw [eLpNorm'_eq_lintegral_eNorm]
  apply (ENNReal.rpow_le_rpow hpow (by positivity : 0 ≤ 1 / p)).trans_eq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one]
  have hC : (6 : ℝ≥0∞) + ENNReal.ofReal K = ENNReal.ofReal (6 + K) := by
    rw [ENNReal.ofReal_add (by norm_num) hK]
    norm_num
  rw [hC, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  rfl

private theorem rectangle_estimate {a b p : ℝ} (ha : 1 < a) (ha' : a ≤ 3 / 2)
    (hb : 5 / 2 ≤ b) (hb' : b < 3) (hp : 1 ≤ p) (hp' : p < 2)
    {u : R2 → ℝ} (hu : ContDiffOn ℝ 1 u Omega1) :
    eLpNorm' ((fun x => phi x * u x) ∘ polar) (pStar p)
        (volume.restrict (Icc a b ×ˢ angles)) ≤
      ENNReal.ofReal (p / (2 - p)) * (3 * (ENNReal.ofReal (hardyConstant p) + 1)) *
        (eLpNorm' (fun x => phi x * ‖fderivWithin ℝ u Omega1 x‖) p (volume.restrict Omega1) +
          eLpNorm' u p (volume.restrict Omega2)) := by
  let S := Icc a b ×ˢ angles
  let μ : Measure (ℝ × ℝ) := volume.restrict S
  let U (z : ℝ × ℝ) := u (polar z)
  let D (z : ℝ × ℝ) := ‖fderivWithin ℝ u Omega1 (polar z)‖
  let W (z : ℝ × ℝ) := (z.1 - 1) * D z
  let V (z : ℝ × ℝ) := (z.1 - 1) * U z
  let H (z : ℝ × ℝ) := ‖U z‖ + 3 * W z
  let G := eLpNorm' (fun x => phi x * ‖fderivWithin ℝ u Omega1 x‖) p
    (volume.restrict Omega1)
  let O := eLpNorm' u p (volume.restrict Omega2)
  have hp₀ : 0 < p := by linarith
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hmaps (z : ℝ × ℝ) (hz : z ∈ S) : polar z ∈ Omega1 :=
    (polar_mem (by norm_num : (0 : ℝ) < 1) (by linarith [hz.1.1])).2
      ⟨ha.trans_le hz.1.1, hz.1.2.trans_lt hb'⟩
  have hU : ContinuousOn U S := hu.continuousOn.comp continuous_polar.continuousOn hmaps
  have hD : ContinuousOn D S :=
    (hu.continuousOn_fderivWithin isOpen_omega1.uniqueDiffOn (by norm_num)).norm.comp
      continuous_polar.continuousOn hmaps
  have hR : Continuous (fun z : ℝ × ℝ => z.1 - 1) := continuous_fst.sub continuous_const
  have hW : ContinuousOn W S := hR.continuousOn.mul hD
  have hV : ContinuousOn V S := hR.continuousOn.mul hU
  have hH : ContinuousOn H S := hU.norm.add (continuousOn_const.mul hW)
  have hW₀ (z : ℝ × ℝ) (hz : z ∈ S) : 0 ≤ W z :=
    mul_nonneg (sub_nonneg.mpr (ha.le.trans hz.1.1)) (norm_nonneg _)
  have hH₀ (z : ℝ × ℝ) (hz : z ∈ S) : 0 ≤ H z :=
    add_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (hW₀ z hz))
  have hdiff (z : ℝ × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ u (polar z) :=
    (hu.contDiffAt (isOpen_omega1.mem_nhds (hmaps z hz))).differentiableAt one_ne_zero
  have hUr (z : ℝ × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun t => U (t, z.2)) z.1 ∧
        ‖deriv (fun t => U (t, z.2)) z.1‖ ≤ D z := by
    have hd := (hdiff z hz).hasFDerivAt.comp_hasDerivAt z.1
      (hasDerivAt_polar_radius z.1 z.2)
    have hd' : HasDerivAt (fun t => U (t, z.2))
        (fderiv ℝ u (polar z) (planeRepr (Complex.exp ((z.2 : ℂ) * Complex.I)))) z.1 := hd
    refine ⟨hd'.differentiableAt, ?_⟩
    rw [hd'.deriv]
    dsimp only [D]
    rw [fderivWithin_of_isOpen isOpen_omega1 (hmaps z hz)]
    exact (ContinuousLinearMap.le_opNorm _ _).trans_eq (by
      rw [planeRepr.norm_map, Complex.norm_exp_ofReal_mul_I, mul_one])
  have hUθ (z : ℝ × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun t => U (z.1, t)) z.2 ∧
        ‖deriv (fun t => U (z.1, t)) z.2‖ ≤ 3 * D z := by
    let tangent := planeRepr ((z.1 : ℂ) * (Complex.exp ((z.2 : ℂ) * Complex.I) * Complex.I))
    have hd : HasDerivAt (fun t => U (z.1, t))
        (fderiv ℝ u (polar z) tangent) z.2 :=
      (hdiff z hz).hasFDerivAt.comp_hasDerivAt z.2 (hasDerivAt_polar_angle z.1 z.2)
    have ht : ‖tangent‖ ≤ 3 := by
      dsimp only [tangent]
      rw [planeRepr.norm_map, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
        Complex.norm_I, one_mul, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by linarith [hz.1.1])]
      exact hz.1.2.trans hb'.le
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    dsimp only [D]
    rw [fderivWithin_of_isOpen isOpen_omega1 (hmaps z hz), mul_comm]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
  have hVr (z : ℝ × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun t => V (t, z.2)) z.1 ∧
        ‖deriv (fun t => V (t, z.2)) z.1‖ ≤ H z := by
    have hd := ((hasDerivAt_id z.1).sub_const 1).fun_mul (hUr z hz).1.hasDerivAt
    have hd' : HasDerivAt (fun t => V (t, z.2))
        (U z + (z.1 - 1) * deriv (fun t => U (t, z.2)) z.1) z.1 := by
      simpa only [id_eq, one_mul, V, Prod.fst, Prod.mk.eta] using hd
    have h₀ : 0 ≤ z.1 - 1 := sub_nonneg.mpr (ha.le.trans hz.1.1)
    refine ⟨hd'.differentiableAt, ?_⟩
    rw [hd'.deriv]
    calc
      _ ≤ ‖U z‖ + (z.1 - 1) * ‖deriv (fun t => U (t, z.2)) z.1‖ := by
        simpa only [norm_mul, Real.norm_of_nonneg h₀] using norm_add_le
          (U z) ((z.1 - 1) * deriv (fun t => U (t, z.2)) z.1)
      _ ≤ ‖U z‖ + W z := add_le_add_right (mul_le_mul_of_nonneg_left (hUr z hz).2 h₀) _
      _ ≤ H z := by
        dsimp only [H]
        linarith [hW₀ z hz]
  have hVθ (z : ℝ × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun t => V (z.1, t)) z.2 ∧
        ‖deriv (fun t => V (z.1, t)) z.2‖ ≤ H z := by
    have hd : HasDerivAt (fun t => V (z.1, t))
        ((z.1 - 1) * deriv (fun t => U (z.1, t)) z.2) z.2 :=
      (hUθ z hz).1.hasDerivAt.const_mul (z.1 - 1)
    have h₀ : 0 ≤ z.1 - 1 := sub_nonneg.mpr (ha.le.trans hz.1.1)
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv, norm_mul, Real.norm_of_nonneg h₀]
    calc
      _ ≤ (z.1 - 1) * (3 * D z) := mul_le_mul_of_nonneg_left (hUθ z hz).2 h₀
      _ = 3 * W z := by dsimp only [W]; ring
      _ ≤ H z := le_add_of_nonneg_left (norm_nonneg _)
  have hVeq : eLpNorm' ((fun x => phi x * u x) ∘ polar) (pStar p) μ = eLpNorm' V (pStar p) μ := by
    apply eLpNorm'_congr_ae
    exact ae_restrict_of_forall_mem hS fun z hz => by
      simp only [V, U, Function.comp_apply, phi_polar (ha.le.trans hz.1.1)]
  have hWle : eLpNorm' W p μ ≤ G := by
    calc
      _ = eLpNorm' ((fun x => phi x * ‖fderivWithin ℝ u Omega1 x‖) ∘ polar) p μ := by
        apply eLpNorm'_congr_ae
        exact ae_restrict_of_forall_mem hS fun z hz => by
          simp only [W, D, Function.comp_apply, phi_polar (ha.le.trans hz.1.1)]
      _ ≤ G := le_annulus_norm (by norm_num) ha.le hb' hp₀ _
  have hOle : eLpNorm' U p (volume.restrict (Icc 2 b ×ˢ angles)) ≤ O :=
    le_annulus_norm (by norm_num) le_rfl hb' hp₀ u
  have hHardy : eLpNorm' U p μ ≤ ENNReal.ofReal (hardyConstant p) * (G + O) :=
    (radial_rect_norm hp ha.le (by linarith) hb hU hD (fun _ _ => norm_nonneg _) hUr).trans
      (mul_le_mul' le_rfl (add_le_add hWle hOle))
  have hSum : eLpNorm' (fun z => ‖V z‖ + H z) p μ ≤ 3 *
        (eLpNorm' U p μ + eLpNorm' W p μ) := by
    have hpoint : ∀ᵐ z ∂μ, ‖‖V z‖ + H z‖₊ ≤ (3 : ℝ≥0) * ‖‖U z‖ + W z‖₊ := by
      apply ae_restrict_of_forall_mem hS
      intro z hz
      apply NNReal.coe_le_coe.mp
      have hv : ‖V z‖ ≤ 2 * ‖U z‖ := by
        dsimp only [V]
        rw [norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr (ha.le.trans hz.1.1))]
        exact mul_le_mul_of_nonneg_right (by linarith [hz.1.2.trans hb'.le]) (norm_nonneg _)
      push_cast
      simp only [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (hH₀ z hz)),
        Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (hW₀ z hz))]
      dsimp only [H]
      linarith
    have h₁ := eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul hpoint hp₀
    have h₂ := eLpNorm'_add_le (hU.norm.aestronglyMeasurable (μ := volume) hS)
      (hW.aestronglyMeasurable hS) hp
    simp only [eLpNorm'_norm] at h₂
    exact (by simpa [ENNReal.smul_def] using h₁.trans (mul_le_mul' le_rfl h₂))
  change eLpNorm' ((fun x => phi x * u x) ∘ polar) (pStar p) μ ≤ _
  rw [hVeq]
  calc
    _ ≤ ENNReal.ofReal (p / (2 - p)) * eLpNorm' (fun z => ‖V z‖ + H z) p μ :=
      rect_sobolev hp hp' (by linarith) (by have := Real.pi_gt_three; linarith)
        hV hH hH₀ hVr hVθ
    _ ≤ ENNReal.ofReal (p / (2 - p)) *
        (3 * (ENNReal.ofReal (hardyConstant p) * (G + O) + G)) :=
      mul_le_mul' le_rfl (hSum.trans (mul_le_mul' le_rfl (add_le_add hHardy hWle)))
    _ ≤ _ := by
      rw [mul_assoc, mul_assoc (3 : ℝ≥0∞), add_mul, one_mul]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (add_le_add_right le_self_add _))

private theorem norm_open_strip_le {q : ℝ} (hq : 0 < q) (F : ℝ × ℝ → ℝ) (M : ℝ≥0∞)
    (h : ∀ a b : ℝ, 1 < a → a ≤ 3 / 2 → 5 / 2 ≤ b → b < 3 →
      eLpNorm' F q (volume.restrict (Icc a b ×ˢ angles)) ≤ M) :
    eLpNorm' F q (volume.restrict (Ioo 1 3 ×ˢ angles)) ≤ M := by
  let ε (n : ℕ) : ℝ := 1 / (n + 4)
  let K (n : ℕ) := Icc (1 + ε n) (3 - ε n) ×ˢ angles
  have hε₀ (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε (n : ℕ) : ε n ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hmono : Antitone ε := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact add_le_add_left (by exact_mod_cast hmn) _
  have hK : Monotone K :=
    fun m n hmn => prod_mono (Icc_subset_Icc (by linarith [hmono hmn])
      (by linarith [hmono hmn])) Subset.rfl
  -- The two sides of each compact strip stay inside the open annulus.
  have hcover : (⋃ n, K n) = Ioo 1 3 ×ˢ angles := by
    ext z
    constructor
    · rintro hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      exact ⟨⟨by linarith [hn.1.1, hε₀ n], by linarith [hn.1.2, hε₀ n]⟩, hn.2⟩
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt
        (lt_min (sub_pos.mpr hz.1.1) (sub_pos.mpr hz.1.2))
      have hlt : ε n < min (z.1 - 1) (3 - z.1) :=
        (one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) + 1) (by linarith)).trans_lt hn
      exact mem_iUnion.mpr ⟨n, ⟨⟨by linarith [hlt.trans_le (min_le_left _ _)],
        by linarith [hlt.trans_le (min_le_right _ _)]⟩, hz.2⟩⟩
  rw [eLpNorm'_eq_lintegral_eNorm, ← hcover, setLIntegral_iUnion_of_directed _ hK.directed_le,
    one_div, ENNReal.rpow_inv_le_iff hq]
  apply iSup_le
  intro n
  have hn := h (1 + ε n) (3 - ε n) (by linarith [hε₀ n]) (by linarith [hε n])
    (by linarith [hε n]) (by linarith [hε₀ n])
  rwa [eLpNorm'_eq_lintegral_eNorm, one_div, ENNReal.rpow_inv_le_iff hq] at hn

/-- **Critical weighted Sobolev inequality on an annulus.** For $r > 0$ let $B_r$ be the open disc
of radius $r$ about the origin in the Euclidean plane $\mathbb{R}^2$, let
$\Omega_1 = B_3 \setminus \overline{B}_1$ and $\Omega_2 = B_3 \setminus \overline{B}_2$, and let
$\phi(x) = \max\{|x| - 1, 0\}$, the distance from $x$ to the closed unit disc. Let $1 \le p < 2$
and $p^* = 2p/(2-p)$. Then there is a real number $C > 0$ such that every function
$u \colon \mathbb{R}^2 \to \mathbb{R}$ that is continuously differentiable on $\Omega_1$ and for
which $\|\phi \nabla u\|_{L^p(\Omega_1)}$ and $\|u\|_{L^p(\Omega_2)}$ are finite satisfies

$$\|\phi u\|_{L^{p^*}(\Omega_1)} \le C\|\phi \nabla u\|_{L^p(\Omega_1)} + C\|u\|_{L^p(\Omega_2)}.$$

Here the norms are taken with respect to Lebesgue measure, $\|\phi \nabla u\|_{L^p(\Omega_1)}$ is
the $L^p(\Omega_1)$ norm of $x \mapsto \phi(x)\,|\nabla u(x)|$, and $\nabla u(x)$ is the derivative
of $u$ at $x$ within $\Omega_1$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_65.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_eLpNorm_phi_mul_le_weighted_grad_add_outer_annulus
  (p : ℝ)
  (hp₁ : 1 ≤ p)
  (hp₂ : p < 2) :
  ∃ C : ℝ, 0 < C ∧
    ∀ u : R2 → ℝ,
      ContDiffOn ℝ 1 u Omega1 →
      eLpNorm (fun x : R2 => phi x * ‖fderivWithin ℝ u Omega1 x‖)
          (ENNReal.ofReal p) (volume.restrict Omega1) ≠ ⊤ →
      eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega2) ≠ ⊤ →
      eLpNorm (fun x : R2 => phi x * u x) (ENNReal.ofReal (pStar p))
          (volume.restrict Omega1) ≤
        ENNReal.ofReal C *
            eLpNorm (fun x : R2 => phi x * ‖fderivWithin ℝ u Omega1 x‖)
              (ENNReal.ofReal p) (volume.restrict Omega1) +
          ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega2) := by
  let γ := p / (2 - p)
  let C := 9 * γ * (hardyConstant p + 1)
  have hγ : 1 ≤ γ := (le_div_iff₀ (by linarith)).2 (by linarith)
  have hq : pStar p = 2 * γ := by unfold pStar γ; ring
  have hp₀ : 0 < p := by linarith
  have hq₀ : 0 < pStar p := by rw [hq]; linarith
  have hK : 0 ≤ hardyConstant p := by unfold hardyConstant; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u hu hg ho
  let F (x : R2) := phi x * u x
  let G (x : R2) := phi x * ‖fderivWithin ℝ u Omega1 x‖
  have hF : AEStronglyMeasurable F (volume.restrict Omega1) :=
    ((continuous_norm.sub continuous_const).max continuous_const).continuousOn.mul
      hu.continuousOn |>.aestronglyMeasurable isOpen_omega1.measurableSet
  change eLpNorm F (ENNReal.ofReal (pStar p)) (volume.restrict Omega1) ≤
    ENNReal.ofReal C * eLpNorm G (ENNReal.ofReal p) (volume.restrict Omega1) +
      ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal p) (volume.restrict Omega2)
  rw [eLpNorm'_ofReal hq₀ hF, eLpNorm'_ofReal hp₀ (aestronglyMeasurable_of_eLpNorm_ne_top hg),
    eLpNorm'_ofReal hp₀ (aestronglyMeasurable_of_eLpNorm_ne_top ho)]
  let E := eLpNorm' G p (volume.restrict Omega1) + eLpNorm' u p (volume.restrict Omega2)
  change eLpNorm' F (pStar p) (volume.restrict Omega1) ≤
    ENNReal.ofReal C * eLpNorm' G p (volume.restrict Omega1) +
      ENNReal.ofReal C * eLpNorm' u p (volume.restrict Omega2)
  rw [← mul_add]
  change eLpNorm' F (pStar p) (volume.restrict Omega1) ≤ ENNReal.ofReal C * E
  have hrect : eLpNorm' (F ∘ polar) (pStar p) (volume.restrict (Ioo 1 3 ×ˢ angles)) ≤
      ENNReal.ofReal γ * (3 * (ENNReal.ofReal (hardyConstant p) + 1)) * E :=
    norm_open_strip_le hq₀ _ _ fun _ _ ha ha' hb hb' =>
      rectangle_estimate ha ha' hb hb' hp₁ hp₂ hu
  have h3 : (3 : ℝ≥0∞) ^ (1 / pStar p) ≤ 3 := by
    calc
      _ ≤ (3 : ℝ≥0∞) ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
        ((div_le_iff₀ hq₀).mpr (by rw [hq, one_mul]; linarith))
      _ = _ := ENNReal.rpow_one _
  calc
    _ ≤ (3 : ℝ≥0∞) ^ (1 / pStar p) *
        eLpNorm' (F ∘ polar) (pStar p) (volume.restrict (Ioo 1 3 ×ˢ angles)) :=
      annulus_norm_le hq₀ F
    _ ≤ 3 * (ENNReal.ofReal γ * (3 * (ENNReal.ofReal (hardyConstant p) + 1)) * E) :=
      mul_le_mul' h3 hrect
    _ = ENNReal.ofReal C * E := by
      dsimp only [C]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 9 * γ),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9), ENNReal.ofReal_add hK zero_le_one]
      norm_num
      ring

end MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedSobolevCriticalWanted
