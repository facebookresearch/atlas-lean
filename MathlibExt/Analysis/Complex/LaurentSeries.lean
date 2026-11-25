/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Complex.MeanValue
import MathlibExt.Analysis.Fourier.AddCircle.C1FourierSummable

/-!
# Laurent expansion on an annulus

The theorem `laurentExpansion` represents a holomorphic function on an open annulus by a
single Laurent series. On each concentric circle the series is a Fourier series, and Cauchy's
theorem on annuli makes the normalized coefficients independent of the radius.
-/

open Complex Metric Real Set
open MathlibExt.Analysis.Fourier.AddCircle.C1FourierSummable

namespace MathlibExt.Analysis.Complex.LaurentSeriesWanted

private abbrev annulus (c : ℂ) (r R : ℝ) := {z : ℂ | r < ‖z - c‖ ∧ ‖z - c‖ < R}

private lemma isOpen_annulus (c : ℂ) (r R : ℝ) : IsOpen (annulus c r R) :=
  isOpen_Ioo.preimage (continuous_id.sub (continuous_const (y := c))).norm

private noncomputable def coeff (f : ℂ → ℂ) (c : ℂ) (s : ℝ) (n : ℤ) : ℂ :=
  circleAverage (fun w ↦ (w - c) ^ (-n) * f w) c s

private lemma coeff_eq {f : ℂ → ℂ} {c : ℂ} {r R s t : ℝ}
    (hf : DifferentiableOn ℂ f (annulus c r R))
    (hs : s ∈ Ioo (max r 0) R) (ht : t ∈ Ioo (max r 0) R) (n : ℤ) :
    coeff f c s n = coeff f c t n := by
  wlog hst : s ≤ t generalizing s t
  · exact (this ht hs (le_of_not_ge hst)).symm
  have hs₀ := (le_max_right r 0).trans_lt hs.1
  have ht₀ := hs₀.trans_le hst
  have hd (w : ℂ) (hw : w ∈ closedBall c t \ ball c s) :
      DifferentiableAt ℂ (fun w ↦ (w - c) ^ (-n) * f w) w := by
    have hsw : s ≤ ‖w - c‖ := by simpa [mem_ball, dist_eq_norm] using hw.2
    have hwt : ‖w - c‖ ≤ t := by simpa [mem_closedBall, dist_eq_norm] using hw.1
    have hwA : w ∈ annulus c r R :=
      ⟨((le_max_left r 0).trans_lt hs.1).trans_le hsw, hwt.trans_lt ht.2⟩
    exact ((differentiableAt_id.sub_const c).zpow
      (Or.inl (norm_pos_iff.mp (hs₀.trans_le hsw)))).mul
      (hf.differentiableAt ((isOpen_annulus c r R).mem_nhds hwA))
  rw [coeff, coeff, circleAverage_eq_circleIntegral hs₀.ne',
    circleAverage_eq_circleIntegral ht₀.ne']
  congr 1
  exact (circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
    hs₀ hst countable_empty (fun w hw ↦ (hd w hw).continuousAt.continuousWithinAt)
    fun w hw ↦ hd w ⟨ball_subset_closedBall hw.1.1,
      fun h ↦ hw.1.2 (ball_subset_closedBall h)⟩).symm

private lemma fourier_two_pi (n : ℤ) (θ : ℝ) :
    fourier n (θ : AddCircle (2 * π)) = exp (θ * I) ^ n := by
  rw [fourier_coe_apply, ← exp_int_mul, ofReal_mul, ofReal_ofNat]
  congr 1
  field_simp [Real.pi_ne_zero]

private lemma fourierCoeff_circle (f : ℂ → ℂ) (c : ℂ) {s : ℝ} (hs : 0 < s) (n : ℤ) :
    fourierCoeffOn two_pi_pos (f ∘ circleMap c s) n = (s : ℂ) ^ n * coeff f c s n := by
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  rw [fourierCoeffOn_eq_integral, sub_zero, coeff, circleAverage]
  simp only [one_div, smul_eq_mul, real_smul]
  rw [mul_left_comm ((s : ℂ) ^ n)]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only [Function.comp_apply]
  rw [fourier_two_pi, circleMap_sub_center, circleMap_zero, mul_zpow, zpow_neg (s : ℂ)]
  simp [← mul_assoc, zpow_ne_zero n hs']

private lemma hasSum_circle {f : ℂ → ℂ} {c : ℂ} {r R s : ℝ}
    (hf : DifferentiableOn ℂ f (annulus c r R)) (hs : s ∈ Ioo (max r 0) R)
    {z : ℂ} (hz : ‖z - c‖ = s) :
    HasSum (fun n : ℤ ↦ coeff f c s n * (z - c) ^ n) (f z) := by
  have hs₀ := (le_max_right r 0).trans_lt hs.1
  have hmem (θ : ℝ) : circleMap c s θ ∈ annulus c r R := by
    simpa [annulus, abs_of_pos hs₀] using And.intro ((le_max_left r 0).trans_lt hs.1) hs.2
  have himage : z ∈ circleMap c s '' Ioc 0 (2 * π) := by
    simpa [image_circleMap_Ioc, mem_sphere, dist_eq_norm, abs_of_pos hs₀] using hz
  obtain ⟨θ, hθ, rfl⟩ := himage
  have hopen := isOpen_annulus c r R
  have hd (x : ℝ) := (hf.differentiableAt (hopen.mem_nhds (hmem x))).hasDerivAt.scomp x
    (hasDerivAt_circleMap c s x)
  have hcont := (hf.deriv hopen).continuousOn.comp_continuous (continuous_circleMap c s) hmem
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  have hsum := hasSum_fourier_series_of_hasDerivAt_apply two_pi_pos
    ((periodic_circleMap c s).comp f)
    (hf.continuousOn.comp_continuous (continuous_circleMap c s) hmem) hd
    (((continuous_circleMap 0 s).mul continuous_const).smul hcont) hθ
  apply hsum.congr_fun
  intro n
  rw [fourierCoeff_circle _ _ hs₀, fourier_two_pi, circleMap_sub_center, circleMap_zero, mul_zpow]
  simp only [smul_eq_mul]
  ring

/--
**Laurent expansion on an annulus.** Let $c \in \mathbb{C}$, let $r$ and $R$ be real numbers, and
let $f : \mathbb{C} \to \mathbb{C}$ be holomorphic on the annulus
$A = \{z \in \mathbb{C} : r < |z - c| < R\}$. Then there are coefficients $a_n \in \mathbb{C}$
for $n \in \mathbb{Z}$ such that for every $z \in A$ the series
$\sum_{n \in \mathbb{Z}} a_n (z - c)^n$ is unconditionally summable with sum $f(z)$. Here
$0^n = 0$ for $n < 0$, which matters only at $z = c$ when $r < 0$.

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "Laurent series"; L. V. Ahlfors, Complex Analysis, 3rd ed.,
Ch. 5, §1.3 (the Laurent series).
-/
public theorem laurentExpansion
    {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | r < ‖z - c‖ ∧ ‖z - c‖ < R}) :
    ∃ a : ℤ → ℂ, ∀ z ∈ {z : ℂ | r < ‖z - c‖ ∧ ‖z - c‖ < R},
      HasSum (fun n : ℤ => a n * (z - c) ^ n) (f z) := by
  by_cases h : max r 0 < R
  · obtain ⟨s, hs⟩ := exists_between h
    refine ⟨coeff f c s, fun z hz ↦ ?_⟩
    by_cases hzc : z = c
    · subst z
      have hr : r < 0 := by simpa using hz.1
      have hs₀ := (le_max_right r 0).trans_lt hs.1
      have hball : closedBall c |s| ⊆ annulus c r R := by
        intro w hw
        refine ⟨hr.trans_le (norm_nonneg _), lt_of_le_of_lt ?_ hs.2⟩
        simpa [mem_closedBall, dist_eq_norm, abs_of_pos hs₀] using hw
      have hmean := ((hf.mono hball).mono closure_ball_subset_closedBall).diffContOnCl.circleAverage
      have hzero : coeff f c s 0 = f c := by simpa [coeff] using hmean
      simpa [hzero] using (hasSum_single (f := fun n : ℤ ↦ coeff f c s n * (c - c) ^ n) 0
        (fun n hn ↦ by simp [zero_zpow _ hn]))
    · have ht : ‖z - c‖ ∈ Ioo (max r 0) R :=
        ⟨max_lt hz.1 (norm_pos_iff.mpr (sub_ne_zero.mpr hzc)), hz.2⟩
      exact (hasSum_circle hf ht rfl).congr_fun fun n ↦ by rw [coeff_eq hf ht hs]
  · refine ⟨0, fun z hz ↦ (h ?_).elim⟩
    exact max_lt (hz.1.trans hz.2) ((norm_nonneg _).trans_lt hz.2)

end MathlibExt.Analysis.Complex.LaurentSeriesWanted
