/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Convolution
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Aperture jitter budget

## i. Overview

A sampled-data acquisition chain (aperture averaging, timing
jitter, and the saturating quantizer from
`MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp`, imported,
not copied) has an end-to-end error budget: aperture smoothing
and jitter blur a Lipschitz signal by `L (J + A / 2)`,
quantization adds `Delta / 2` on unclipped inputs, and a known
calibration scale divides through. Clipping can break the
budget (one clipped constant is refuted), and non-normalized
kernels are refuted as budget violations.

## ii. Key results

- `abs_quantize_sampled_sub_le`: the combined sampled error
  budget.
- `abs_quantize_div_calibration_sub_le`: the calibrated
  budget.
- `clipped_const_violates_budget`: clipping can break
  the budget (one clipped constant does).

## iii. Table of contents

- A. The aperture jitter budget

## iv. References

- W. Kester (ed.), *The Data Conversion Handbook*, Newnes,
  2005: aperture jitter and quantization error budgets.

## A. The aperture jitter budget
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution NNReal

namespace PhyslibExt.Instrumentation.ApertureJitterBudget

open MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp

/-- An aperture kernel of full width `A`: nonnegative, integrating to one, and supported in
the closed window `[-A/2, A/2]`. -/
structure IsApertureKernel (A : ℝ) (w : ℝ → ℝ) : Prop where
  nonneg : ∀ τ, 0 ≤ w τ
  integral_eq_one : ∫ τ, w τ = 1
  support_subset : Function.support w ⊆ Icc (-(A / 2)) (A / 2)

/-- An aperture kernel is integrable. -/
lemma IsApertureKernel.integrable {A : ℝ} {w : ℝ → ℝ} (hw : IsApertureKernel A w) :
    Integrable w := by
  exact integrable_of_integral_eq_one hw.integral_eq_one

/-- An aperture kernel forces a nonnegative half-width. -/
lemma IsApertureKernel.halfWidth_nonneg {A : ℝ} {w : ℝ → ℝ} (hw : IsApertureKernel A w) :
    0 ≤ A := by
  by_contra h
  rw [not_le] at h
  have hz : w = 0 := by
    funext τ
    by_contra hne
    have hmem := hw.support_subset (show τ ∈ Function.support w from hne)
    rw [Set.mem_Icc] at hmem
    linarith [hmem.1, hmem.2]
  have h1 := hw.integral_eq_one
  rw [hz] at h1
  simp at h1

/-- Lipschitz bound on a set, stated with absolute values. -/
private lemma abs_sub_le_of_lipschitzOnWith_aux {x : ℝ → ℝ} {L : ℝ≥0} {s : Set ℝ}
    (hx : LipschitzOnWith L x s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    |x a - x b| ≤ (L : ℝ) * |a - b| := by
  have h := hx.dist_le_mul a ha b hb
  rwa [Real.dist_eq, Real.dist_eq] at h

/-- **Jitter bound.** If `x` is `L`-Lipschitz on `[k Ts - J, k Ts + J]` and `|j| ≤ J`, the
jittered sample `x (k Ts + j)` differs from the nominal sample `x (k Ts)` by at most `L J`. -/
lemma abs_sub_le_of_abs_jitter_le {x : ℝ → ℝ} {L : ℝ≥0} {Ts J j : ℝ} (k : ℤ)
    (hx : LipschitzOnWith L x (Icc ((k : ℝ) * Ts - J) ((k : ℝ) * Ts + J))) (hj : |j| ≤ J) :
    |x ((k : ℝ) * Ts + j) - x ((k : ℝ) * Ts)| ≤ (L : ℝ) * J := by
  have h1 : (k : ℝ) * Ts + j ∈ Icc ((k : ℝ) * Ts - J) ((k : ℝ) * Ts + J) := by
    constructor <;> linarith [(abs_le.mp hj).1, (abs_le.mp hj).2]
  have h2 : (k : ℝ) * Ts ∈ Icc ((k : ℝ) * Ts - J) ((k : ℝ) * Ts + J) := by
    constructor <;> linarith [(abs_le.mp hj).1, (abs_le.mp hj).2]
  calc |x ((k : ℝ) * Ts + j) - x ((k : ℝ) * Ts)|
      ≤ (L : ℝ) * |(k : ℝ) * Ts + j - (k : ℝ) * Ts| := abs_sub_le_of_lipschitzOnWith_aux hx h1 h2
    _ = (L : ℝ) * |j| := by rw [show (k : ℝ) * Ts + j - (k : ℝ) * Ts = j by ring]
    _ ≤ (L : ℝ) * J := mul_le_mul_of_nonneg_left hj L.coe_nonneg

/-- **Aperture bound.** If `w` is an aperture kernel of width `A` and `x` is `L`-Lipschitz on
`[t - A/2, t + A/2]`, the aperture acquisition `(w ⋆ x) t` differs from `x t` by at most
`L A / 2`. -/
lemma abs_convolution_sub_le_of_isApertureKernel {x w : ℝ → ℝ} {L : ℝ≥0} {A t : ℝ}
    (hw : IsApertureKernel A w) (hx : LipschitzOnWith L x (Icc (t - A / 2) (t + A / 2))) :
    |(w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) t - x t| ≤ (L : ℝ) * (A / 2) := by
  have hA : 0 ≤ A := hw.halfWidth_nonneg
  have hzero : ∀ τ, τ ∉ Icc (-(A / 2)) (A / 2) → w τ = 0 := fun τ hτ => by
    by_contra hne
    exact hτ (hw.support_subset hne)
  have hmaps : ∀ τ ∈ Icc (-(A / 2)) (A / 2), t - τ ∈ Icc (t - A / 2) (t + A / 2) :=
    fun τ hτ => by constructor <;> linarith [hτ.1, hτ.2]
  have ht : t ∈ Icc (t - A / 2) (t + A / 2) := by constructor <;> linarith
  have hlip : ∀ τ ∈ Icc (-(A / 2)) (A / 2), |x (t - τ) - x t| ≤ (L : ℝ) * (A / 2) :=
    fun τ hτ => by
      calc |x (t - τ) - x t| ≤ (L : ℝ) * |t - τ - t| :=
            abs_sub_le_of_lipschitzOnWith_aux hx (hmaps τ hτ) ht
        _ ≤ (L : ℝ) * (A / 2) := by
          apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
          rw [show t - τ - t = -τ by ring, abs_neg, abs_le]
          exact ⟨hτ.1, hτ.2⟩
  set h : ℝ → ℝ := (Icc (-(A / 2)) (A / 2)).indicator (fun τ => x (t - τ)) with hh
  have hcont : ContinuousOn (fun τ => x (t - τ)) (Icc (-(A / 2)) (A / 2)) :=
    hx.continuousOn.comp (continuous_const.sub continuous_id).continuousOn hmaps
  have hmeas : AEStronglyMeasurable h volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr
      (hcont.aestronglyMeasurable measurableSet_Icc)
  have heq : ∀ τ, w τ * x (t - τ) = w τ * h τ := fun τ => by
    by_cases hτ : τ ∈ Icc (-(A / 2)) (A / 2)
    · rw [hh, Set.indicator_of_mem hτ]
    · rw [hzero τ hτ]
      simp
  have hbound : ∀ τ, |w τ * (h τ - x t)| ≤ w τ * ((L : ℝ) * (A / 2)) := fun τ => by
    by_cases hτ : τ ∈ Icc (-(A / 2)) (A / 2)
    · rw [hh, Set.indicator_of_mem hτ, abs_mul, abs_of_nonneg (hw.nonneg τ)]
      exact mul_le_mul_of_nonneg_left (hlip τ hτ) (hw.nonneg τ)
    · rw [hzero τ hτ]
      simp
  have hint_w := hw.integrable
  have hint_d : Integrable (fun τ => w τ * (h τ - x t)) :=
    (hint_w.mul_const ((L : ℝ) * (A / 2))).mono'
      (hint_w.aestronglyMeasurable.mul (hmeas.sub aestronglyMeasurable_const))
      (Filter.Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs]
        exact hbound τ)
  have hint_c : Integrable (fun τ => w τ * x t) := hint_w.mul_const _
  have hint_h : Integrable (fun τ => w τ * h τ) := by
    refine (hint_d.add hint_c).congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [Pi.add_apply]
    ring
  have hconv : (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) t = ∫ τ, w τ * h τ := by
    rw [convolution_lsmul]
    simp only [smul_eq_mul, heq]
  have hxt : x t = ∫ τ, w τ * x t := by
    rw [integral_mul_const, hw.integral_eq_one, one_mul]
  rw [hconv, hxt, ← integral_sub hint_h hint_c]
  calc |∫ τ, (w τ * h τ - w τ * x t)| = |∫ τ, w τ * (h τ - x t)| := by
        congr 1
        congr 1
        funext τ
        ring
    _ ≤ ∫ τ, w τ * ((L : ℝ) * (A / 2)) := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le (hint_w.mul_const _)
          (Filter.Eventually.of_forall fun τ => by
            rw [Real.norm_eq_abs]
            exact hbound τ)
    _ = (L : ℝ) * (A / 2) := by rw [integral_mul_const, hw.integral_eq_one, one_mul]

/-- **Jitter plus aperture.** With `|j| ≤ J`, an aperture kernel of width `A`, and `x`
`L`-Lipschitz on `[t₀ - (J + A/2), t₀ + (J + A/2)]`, the aperture acquisition at the jittered
time `t₀ + j` differs from `x t₀` by at most `L (J + A/2)`. -/
lemma abs_convolution_jitter_sub_le {x w : ℝ → ℝ} {L : ℝ≥0} {A J j t₀ : ℝ}
    (hw : IsApertureKernel A w) (hj : |j| ≤ J)
    (hx : LipschitzOnWith L x (Icc (t₀ - (J + A / 2)) (t₀ + (J + A / 2)))) :
    |(w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) (t₀ + j) - x t₀| ≤
      (L : ℝ) * (J + A / 2) := by
  have hA : 0 ≤ A := hw.halfWidth_nonneg
  have hJ : 0 ≤ J := (abs_nonneg j).trans hj
  obtain ⟨hj1, hj2⟩ := abs_le.mp hj
  have hsub : Icc (t₀ + j - A / 2) (t₀ + j + A / 2) ⊆
      Icc (t₀ - (J + A / 2)) (t₀ + (J + A / 2)) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have h1 := abs_convolution_sub_le_of_isApertureKernel hw (hx.mono hsub)
  have hm1 : t₀ + j ∈ Icc (t₀ - (J + A / 2)) (t₀ + (J + A / 2)) := by
    constructor <;> linarith
  have hm2 : t₀ ∈ Icc (t₀ - (J + A / 2)) (t₀ + (J + A / 2)) := by
    constructor <;> linarith
  have h2 : |x (t₀ + j) - x t₀| ≤ (L : ℝ) * J := by
    calc |x (t₀ + j) - x t₀| ≤ (L : ℝ) * |t₀ + j - t₀| :=
          abs_sub_le_of_lipschitzOnWith_aux hx hm1 hm2
      _ ≤ (L : ℝ) * J := by
        rw [show t₀ + j - t₀ = j by ring]
        exact mul_le_mul_of_nonneg_left hj L.coe_nonneg
  have h3 := abs_sub_le ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) (t₀ + j)) (x (t₀ + j))
    (x t₀)
  have h4 : (L : ℝ) * (J + A / 2) = (L : ℝ) * (A / 2) + (L : ℝ) * J := by ring
  rw [h4]
  linarith

/-- **One acquired sample through the ADC.** Jitter `|j| ≤ J`, an aperture kernel of width `A`,
`x` `L`-Lipschitz on the full perturbed interval, and no clipping of the perturbed analog input
`(w ⋆ x) (t₀ + j)`: the quantized acquisition differs from `x t₀` by at most
`L (J + A/2) + Δ / 2`. -/
lemma abs_quantize_convolution_jitter_sub_le {x w : ℝ → ℝ} {L : ℝ≥0} {A J j t₀ Δ : ℝ}
    {kmin kmax : ℤ} (hΔ : 0 < Δ) (hw : IsApertureKernel A w) (hj : |j| ≤ J)
    (hx : LipschitzOnWith L x (Icc (t₀ - (J + A / 2)) (t₀ + (J + A / 2))))
    (hclip : ¬ IsClipped Δ kmin kmax
      ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) (t₀ + j))) :
    |quantize Δ kmin kmax ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) (t₀ + j)) - x t₀| ≤
      (L : ℝ) * (J + A / 2) + Δ / 2 := by
  have h1 := abs_convolution_jitter_sub_le hw hj hx
  have h2 := abs_quantize_sub_le_of_not_isClipped hΔ hclip
  generalize (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) (t₀ + j) = v at h1 h2 ⊢
  linarith [abs_sub_le (quantize Δ kmin kmax v) v (x t₀)]

/-- **Acquisition error budget (headline).** For sample period `Ts`, jitter sequence `j` with
`|j k| ≤ J`, an aperture kernel of width `A`, a signal `x` that is `L`-Lipschitz on every
perturbed interval `[k Ts - (J + A/2), k Ts + (J + A/2)]`, and an ADC with step `Δ > 0` that
does not clip any perturbed analog input, every quantized sample differs from the nominal
sample `x (k Ts)` by at most `L J + L A / 2 + Δ / 2`. -/
lemma abs_quantize_sampled_sub_le {x w : ℝ → ℝ} {L : ℝ≥0} {Ts A J Δ : ℝ} {kmin kmax : ℤ}
    (j : ℤ → ℝ) (hΔ : 0 < Δ) (hw : IsApertureKernel A w) (hj : ∀ k, |j k| ≤ J)
    (hx : ∀ k : ℤ, LipschitzOnWith L x
      (Icc ((k : ℝ) * Ts - (J + A / 2)) ((k : ℝ) * Ts + (J + A / 2))))
    (hclip : ∀ k : ℤ, ¬ IsClipped Δ kmin kmax
      ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) ((k : ℝ) * Ts + j k))) (k : ℤ) :
    |quantize Δ kmin kmax ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) ((k : ℝ) * Ts + j k)) -
        x ((k : ℝ) * Ts)| ≤
      (L : ℝ) * J + (L : ℝ) * (A / 2) + Δ / 2 := by
  have h := abs_quantize_convolution_jitter_sub_le hΔ hw (hj k) (hx k) (hclip k)
  refine h.trans (le_of_eq ?_)
  ring

/-- **Acquisition error budget, full-scale form.** As `abs_quantize_sampled_sub_le`, with the
no-clipping condition replaced by membership of every perturbed analog input in the ADC
full-scale interval `[Δ kmin, Δ kmax]`. -/
lemma abs_quantize_sampled_sub_le_of_mem_Icc {x w : ℝ → ℝ} {L : ℝ≥0} {Ts A J Δ : ℝ}
    {kmin kmax : ℤ} (j : ℤ → ℝ) (hΔ : 0 < Δ) (hw : IsApertureKernel A w)
    (hj : ∀ k, |j k| ≤ J)
    (hx : ∀ k : ℤ, LipschitzOnWith L x
      (Icc ((k : ℝ) * Ts - (J + A / 2)) ((k : ℝ) * Ts + (J + A / 2))))
    (hfs : ∀ k : ℤ, (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) ((k : ℝ) * Ts + j k) ∈
      Icc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))) (k : ℤ) :
    |quantize Δ kmin kmax ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] x) ((k : ℝ) * Ts + j k)) -
        x ((k : ℝ) * Ts)| ≤
      (L : ℝ) * J + (L : ℝ) * (A / 2) + Δ / 2 := by
  exact abs_quantize_sampled_sub_le j hΔ hw hj hx
    (fun k => not_isClipped_of_mem_Icc hΔ (hfs k)) k

/-- **Point sampling through the ADC (no aperture).** Jitter `|j| ≤ J`, `x` `L`-Lipschitz on
`[k Ts - J, k Ts + J]`, and no clipping of the jittered sample: the quantized sample differs
from `x (k Ts)` by at most `L J + Δ / 2`. -/
lemma abs_quantize_jitter_sub_le {x : ℝ → ℝ} {L : ℝ≥0} {Ts J j Δ : ℝ} {kmin kmax : ℤ}
    (k : ℤ) (hΔ : 0 < Δ)
    (hx : LipschitzOnWith L x (Icc ((k : ℝ) * Ts - J) ((k : ℝ) * Ts + J))) (hj : |j| ≤ J)
    (hclip : ¬ IsClipped Δ kmin kmax (x ((k : ℝ) * Ts + j))) :
    |quantize Δ kmin kmax (x ((k : ℝ) * Ts + j)) - x ((k : ℝ) * Ts)| ≤ (L : ℝ) * J + Δ / 2 := by
  have h1 := abs_sub_le_of_abs_jitter_le k hx hj
  have h2 := abs_quantize_sub_le_of_not_isClipped hΔ hclip
  linarith [abs_sub_le (quantize Δ kmin kmax (x ((k : ℝ) * Ts + j))) (x ((k : ℝ) * Ts + j))
    (x ((k : ℝ) * Ts))]

/-- **Known calibration scale.** If the ADC sees `c * s` for a physical signal `s` that is
`Ls`-Lipschitz on the perturbed interval and a known nonzero scale `c`, then dividing the
quantized acquisition by `c` recovers `s t₀` within `Ls (J + A/2) + Δ / (2 |c|)`. -/
lemma abs_quantize_div_calibration_sub_le {s w : ℝ → ℝ} {Ls : ℝ≥0} {c A J j t₀ Δ : ℝ}
    {kmin kmax : ℤ} (hc : c ≠ 0) (hΔ : 0 < Δ) (hw : IsApertureKernel A w) (hj : |j| ≤ J)
    (hs : LipschitzOnWith Ls s (Icc (t₀ - (J + A / 2)) (t₀ + (J + A / 2))))
    (hclip : ¬ IsClipped Δ kmin kmax
      ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun t => c * s t) (t₀ + j))) :
    |quantize Δ kmin kmax
          ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun t => c * s t) (t₀ + j)) / c - s t₀| ≤
      (Ls : ℝ) * (J + A / 2) + Δ / (2 * |c|) := by
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have hKc : ((‖c‖₊ * Ls : ℝ≥0) : ℝ) = |c| * Ls := by
    rw [NNReal.coe_mul, coe_nnNorm, Real.norm_eq_abs]
  have hcs : LipschitzOnWith (‖c‖₊ * Ls) (fun t => c * s t)
      (Icc (t₀ - (J + A / 2)) (t₀ + (J + A / 2))) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [Real.dist_eq, hKc, ← mul_sub, abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    have := hs.dist_le_mul a ha b hb
    rwa [Real.dist_eq] at this
  have h := abs_quantize_convolution_jitter_sub_le hΔ hw hj hcs hclip
  rw [hKc] at h
  generalize quantize Δ kmin kmax
    ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun t => c * s t) (t₀ + j)) = q at h ⊢
  have hq : q / c - s t₀ = (q - c * s t₀) / c := by
    rw [sub_div, mul_div_cancel_left₀ _ hc]
  have hd : Δ / (2 * |c|) * |c| = Δ / 2 := by
    field_simp
  rw [hq, abs_div, div_le_iff₀ hcpos, add_mul, hd]
  linarith

/-- **Ts = 0 exclusion.** The nominal sample times `k Ts` are strictly increasing in `k` iff
`Ts > 0`; at `Ts = 0` every nominal time collapses to `0`. -/
lemma nominalTimes_strictMono_iff (Ts : ℝ) :
    StrictMono (fun k : ℤ => (k : ℝ) * Ts) ↔ 0 < Ts := by
  constructor
  · intro h
    have := h (show (0 : ℤ) < 1 by norm_num)
    simpa using this
  · intro h a b hab
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hab) h

/-! ### Validation fixtures -/

/-- A normalized kernel acquires a constant signal exactly. -/
lemma convolution_const_of_isApertureKernel {w : ℝ → ℝ} {A : ℝ} (hw : IsApertureKernel A w)
    (a t : ℝ) :
    (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun _ => a) t = a := by
  rw [convolution_lsmul]
  simp only [smul_eq_mul]
  rw [integral_mul_const, hw.integral_eq_one, one_mul]

/-- The ramp `t ↦ L t` is `L`-Lipschitz. -/
lemma ramp_lipschitzWith (L : ℝ≥0) : LipschitzWith L (fun t : ℝ => (L : ℝ) * t) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg L.coe_nonneg]

/-- The ramp `t ↦ L t` with jitter `j = J ≥ 0` realizes the jitter bound `L J` exactly. -/
lemma abs_ramp_jitter_sub (L : ℝ≥0) {J : ℝ} (hJ : 0 ≤ J) (t : ℝ) :
    |(L : ℝ) * (t + J) - (L : ℝ) * t| = (L : ℝ) * J := by
  rw [show (L : ℝ) * (t + J) - (L : ℝ) * t = (L : ℝ) * J by ring,
    abs_of_nonneg (mul_nonneg L.coe_nonneg hJ)]

/-- The box (moving-average) kernel of width `A`: `1 / A` on `[-A/2, A/2]`, zero elsewhere. -/
noncomputable def boxKernel (A : ℝ) : ℝ → ℝ :=
  Set.indicator (Icc (-(A / 2)) (A / 2)) fun _ => 1 / A

/-- For `A > 0` the box kernel is an aperture kernel of width `A`. -/
lemma boxKernel_isApertureKernel {A : ℝ} (hA : 0 < A) : IsApertureKernel A (boxKernel A) := by
  refine ⟨fun τ => ?_, ?_, ?_⟩
  · unfold boxKernel
    apply Set.indicator_nonneg
    intro _ _
    positivity
  · unfold boxKernel
    rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
      Real.volume_real_Icc_of_le (by linarith)]
    field_simp
    ring
  · unfold boxKernel
    exact Set.support_indicator_subset

/-- `∫ x in 0..a, x = a ^ 2 / 2`, by the reflection `x ↦ a - x`. -/
private lemma integral_id_zero_aux (a : ℝ) : ∫ x in (0 : ℝ)..a, x = a ^ 2 / 2 := by
  have h1 : ∫ x in (0 : ℝ)..a, (a - x) = ∫ x in (0 : ℝ)..a, x := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => x) a]
    simp
  have h2 : ∫ x in (0 : ℝ)..a, (x + (a - x)) =
      (∫ x in (0 : ℝ)..a, x) + ∫ x in (0 : ℝ)..a, (a - x) :=
    intervalIntegral.integral_add (continuous_id.intervalIntegrable _ _)
      ((continuous_const.sub continuous_id).intervalIntegrable _ _)
  have h3 : ∫ x in (0 : ℝ)..a, (x + (a - x)) = a * a := by
    simp
  rw [sq]
  linarith

/-- `∫ x in -a..a, |x| = a ^ 2` for `a ≥ 0`. -/
private lemma integral_abs_symm_aux {a : ℝ} (ha : 0 ≤ a) : ∫ x in (-a)..a, |x| = a ^ 2 := by
  have hc : Continuous fun x : ℝ => |x| := continuous_abs
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hneg : ∫ x in (-a)..0, |x| = ∫ x in (0 : ℝ)..a, |x| := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun x => |x|)
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  have hpos : ∫ x in (0 : ℝ)..a, |x| = ∫ x in (0 : ℝ)..a, x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le ha] at hx
    exact abs_of_nonneg hx.1
  rw [hneg, hpos, integral_id_zero_aux]
  ring

/-- **Nonzero aperture bias.** The box kernel acquires the `1`-Lipschitz signal `|t|` at
`t = 0` as `A / 4`, while the nominal value is `0`: for `A > 0` the aperture error is strictly
positive (and within the bound `1 * (A / 2)`). -/
lemma aperture_bias_abs_boxKernel {A : ℝ} (hA : 0 < A) :
    (boxKernel A ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun t => |t|) 0 = A / 4 ∧
      0 < abs ((boxKernel A ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun t => |t|) 0 -
        abs (0 : ℝ)) := by
  have hconv : (boxKernel A ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun t => |t|) 0 = A / 4 := by
    rw [convolution_lsmul]
    simp only [smul_eq_mul, zero_sub, abs_neg]
    have hfun : (fun τ => boxKernel A τ * |τ|) =
        (Icc (-(A / 2)) (A / 2)).indicator (fun τ => 1 / A * |τ|) := by
      funext τ
      unfold boxKernel
      by_cases h : τ ∈ Icc (-(A / 2)) (A / 2) <;> simp [h]
    rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
      integral_abs_symm_aux (by linarith)]
    field_simp
    ring
  refine ⟨hconv, ?_⟩
  rw [hconv, abs_zero, sub_zero, abs_of_pos (by positivity)]
  positivity

/-- **Non-normalized kernel (negative example).** The kernel `2 * boxKernel A` is nonnegative
and supported in `[-A/2, A/2]` but integrates to `2`; it is not an aperture kernel, and it
acquires the constant (`0`-Lipschitz) signal `1` as `2`, violating the bound `0 * (A / 2)`. -/
lemma nonnormalized_kernel_violates_bound {A : ℝ} (hA : 0 < A) :
    ¬ IsApertureKernel A (fun τ => 2 * boxKernel A τ) ∧
      ((fun τ => 2 * boxKernel A τ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun _ => (1 : ℝ)) 0 = 2 ∧
      ¬ |((fun τ => 2 * boxKernel A τ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun _ => (1 : ℝ)) 0 - 1| ≤ (0 : ℝ) * (A / 2) := by
  have hbox := boxKernel_isApertureKernel hA
  have hint : ∫ τ, 2 * boxKernel A τ = 2 := by
    rw [integral_const_mul, hbox.integral_eq_one, mul_one]
  have hconv : ((fun τ => 2 * boxKernel A τ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun _ => (1 : ℝ)) 0 = 2 := by
    rw [convolution_lsmul]
    simp only [smul_eq_mul, mul_one]
    exact hint
  refine ⟨fun h => ?_, hconv, ?_⟩
  · have := h.integral_eq_one
    rw [hint] at this
    norm_num at this
  · rw [hconv]
    norm_num

/-- **Clipping transition.** For step `1` and the singleton code range `[0, 0]`, the input
`2 / 5` is not clipped while `1 / 2` is clipped (round half up gives code `1`). -/
lemma isClipped_transition :
    ¬ IsClipped 1 0 0 (2 / 5) ∧ IsClipped 1 0 0 (1 / 2) := by
  have h1 : round ((2 / 5 : ℝ) / 1) = 0 := by
    rw [div_one, round_eq, Int.floor_eq_iff]
    norm_num
  have h2 : round ((1 / 2 : ℝ) / 1) = 1 := by
    rw [div_one, round_eq, Int.floor_eq_iff]
    norm_num
  unfold IsClipped
  rw [h1, h2]
  decide

/-- **Clipping violates the budget (negative example).** The constant signal `2` (Lipschitz
constant `0`, no jitter or aperture error) acquired through the box kernel is clipped by the
step-`1`, range-`[0, 0]` ADC, and its quantization error `2` exceeds the budget
`0 * (J + A/2) + 1 / 2`. -/
lemma clipped_const_violates_budget {A : ℝ} (hA : 0 < A) (J : ℝ) :
    IsClipped 1 0 0 ((boxKernel A ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun _ => 2) 0) ∧
      (0 : ℝ) * (J + A / 2) + 1 / 2 <
        |quantize 1 0 0 ((boxKernel A ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun _ => 2) 0) -
          2| := by
  have hconv := convolution_const_of_isApertureKernel (boxKernel_isApertureKernel hA) 2 0
  rw [hconv]
  have hr : round ((2 : ℝ) / 1) = 2 := by
    rw [div_one, round_eq, Int.floor_eq_iff]
    norm_num
  refine ⟨?_, ?_⟩
  · unfold IsClipped
    rw [hr]
    decide
  · unfold quantize MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp.code
    rw [hr]
    norm_num

end PhyslibExt.Instrumentation.ApertureJitterBudget
