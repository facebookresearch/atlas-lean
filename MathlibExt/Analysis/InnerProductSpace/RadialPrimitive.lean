/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Analysis.Complex.HartogsExtension

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.Analysis.InnerProductSpace.NormDerivative

/-!
# Radial primitives through their centre

Let `f : ℝ → ℝ` be continuous on `[0, ∞)` with `f 0 = 0`, and let
`G w = ∫ t in 0..‖w - z₀‖, f t` in a real inner product space. Away from `z₀`, the
chain rule and the derivative of the norm give the real Fréchet derivative
`(f r / r) • ⟪w - z₀, ·⟫` with `r = ‖w - z₀‖`. At `z₀` the derivative is `0`, by
the estimate `|∫ t in 0..‖h‖, f t| ≤ ‖h‖ · sup_{[0, ‖h‖]} |f|` and `f 0 = 0`; the
closed formula also evaluates to `0` there, but that value is not the proof. The
derivative is continuous, so `G` is `C¹` everywhere although `f` itself need not
be differentiable.

For a finite family of such real primitives, included in `ℂ`, the real
combination `∂ₓ + i ∂ᵧ` of the sum equals `2 * barDeriv` (`barDeriv` is half of
it) and equals the sum of the radial fields `f_α(r_α) (z - z_α) / r_α`. Each
field vanishes at its own centre; the sum need not vanish at any centre.

## Main declarations

* `hasFDerivAt_intervalIntegral_norm_sub`: the real Fréchet derivative at every
  point, the centre included.
* `contDiff_one_intervalIntegral_norm_sub`: the radial primitive is `C¹`.
* `two_mul_barDeriv_ofReal_sum_intervalIntegral_norm_sub`: twice the Wirtinger
  derivative of a finite sum of radial primitives is the sum of the radial fields.

Only `C¹` is proved; nothing here asserts higher regularity.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.RadialPrimitive

open MathlibExt.Analysis.InnerProductSpace.NormDerivative
open MathlibExt.Analysis.Complex.HartogsWanted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Fréchet derivative of a radial primitive through its centre.** Let `f` be continuous on
`[0, ∞)` with `f 0 = 0`. Then `w ↦ ∫ t in 0..‖w - z₀‖, f t` has real Fréchet derivative
`(f ‖z - z₀‖ / ‖z - z₀‖) • innerSL ℝ (z - z₀)` at every point `z`, including the centre
`z₀`, where this derivative is `0`. The hypothesis `f 0 = 0` is what makes the centre
case true. -/
theorem hasFDerivAt_intervalIntegral_norm_sub {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 0))
    (hf0 : f 0 = 0) (z₀ z : E) :
    HasFDerivAt (fun w : E => ∫ t in (0 : ℝ)..‖w - z₀‖, f t)
      ((f ‖z - z₀‖ / ‖z - z₀‖) • innerSL ℝ (z - z₀)) z := by
  by_cases hz : z = z₀
  · obtain rfl := hz
    simp only [sub_self, norm_zero, div_zero, zero_smul]
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    simp only [add_sub_cancel_left, sub_self, norm_zero, intervalIntegral.integral_same,
      sub_zero, zero_apply]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hcw : ContinuousWithinAt f (Set.Ici 0) 0 := hf 0 (Set.mem_Ici.mpr le_rfl)
    rw [Metric.continuousWithinAt_iff] at hcw
    obtain ⟨δ, hδ, hδf⟩ := hcw c hc
    filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
    have hb : ∀ t ∈ Set.uIoc 0 ‖h‖, ‖f t‖ ≤ c := by
      intro t ht
      rw [Set.uIoc_of_le (norm_nonneg _)] at ht
      have hlt : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        exact lt_of_le_of_lt ht.2 (by simpa using hh)
      have := hδf (x := t) (Set.mem_Ici.mpr (le_of_lt ht.1)) hlt
      rw [hf0, Real.dist_eq, sub_zero] at this
      exact this.le
    calc ‖∫ t in (0 : ℝ)..‖h‖, f t‖ ≤ c * |‖h‖ - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = c * ‖h‖ := by simp
  · have hne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hr : 0 < ‖z - z₀‖ := norm_pos_iff.mpr hne
    have hg : HasDerivAt (fun r => ∫ t in (0 : ℝ)..r, f t) (f ‖z - z₀‖) ‖z - z₀‖ := by
      apply intervalIntegral.integral_hasDerivAt_right
      · apply ContinuousOn.intervalIntegrable
        refine hf.mono fun t ht => ?_
        rw [Set.uIcc_of_le hr.le] at ht
        exact ht.1
      · exact (hf.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi _ hr
      · exact hf.continuousAt (Ici_mem_nhds hr)
    have hn : HasFDerivAt (fun w : E => ‖w - z₀‖)
        ((‖z - z₀‖⁻¹ : ℝ) • innerSL ℝ (z - z₀)) z := by
      have h1 := (hasStrictFDerivAt_norm_real hne).hasFDerivAt.comp z
        ((hasFDerivAt_id z).sub_const z₀)
      convert h1 using 1
      all_goals (try (ext v; simp))
    have h2 := hg.comp_hasFDerivAt z hn
    rw [smul_smul, ← div_eq_mul_inv] at h2
    exact h2

/-- **A radial primitive is continuously differentiable.** Let `f` be continuous on `[0, ∞)`
with `f 0 = 0`. Then the radial primitive `w ↦ ∫ t in 0..‖w - z₀‖, f t` is continuously
differentiable (`C¹`) on the whole real inner product space, including at the centre `z₀`;
`f` itself need not be differentiable. -/
theorem contDiff_one_intervalIntegral_norm_sub {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 0))
    (hf0 : f 0 = 0) (z₀ : E) :
    ContDiff ℝ 1 (fun w : E => ∫ t in (0 : ℝ)..‖w - z₀‖, f t) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun z => (hasFDerivAt_intervalIntegral_norm_sub hf hf0 z₀ z).differentiableAt, ?_⟩
  have hfd : fderiv ℝ (fun w : E => ∫ t in (0 : ℝ)..‖w - z₀‖, f t) =
      fun z => (f ‖z - z₀‖ / ‖z - z₀‖) • innerSL ℝ (z - z₀) :=
    funext fun z => (hasFDerivAt_intervalIntegral_norm_sub hf hf0 z₀ z).fderiv
  rw [hfd, continuous_iff_continuousAt]
  intro z
  by_cases hz : z = z₀
  · obtain rfl := hz
    rw [ContinuousAt, sub_self, norm_zero, div_zero, zero_smul,
      tendsto_zero_iff_norm_tendsto_zero]
    have hfc : Filter.Tendsto (fun w : E => f ‖w - z‖) (nhds z) (nhds 0) := by
      have h1 : Filter.Tendsto (fun w : E => ‖w - z‖) (nhds z) (nhdsWithin 0 (Set.Ici 0)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · simpa using ((continuous_id.sub (continuous_const (y := z))).norm.tendsto z)
        · exact Filter.Eventually.of_forall fun w => norm_nonneg _
      simpa [hf0, Function.comp_def] using (hf 0 (Set.mem_Ici.mpr le_rfl)).tendsto.comp h1
    refine squeeze_zero (fun _ => norm_nonneg _) (fun w => ?_)
      (tendsto_zero_iff_norm_tendsto_zero.mp hfc)
    rw [norm_smul, innerSL_apply_norm, norm_div, norm_norm]
    by_cases hw : ‖w - z‖ = 0
    · rw [hw]; simp
    · rw [div_mul_cancel₀ _ hw]
  · have hr : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
    have hnorm : ContinuousAt (fun w : E => ‖w - z₀‖) z :=
      (continuous_id.sub continuous_const).norm.continuousAt
    have ha : ContinuousAt (fun w : E => f ‖w - z₀‖ / ‖w - z₀‖) z :=
      ((hf.continuousAt (Ici_mem_nhds hr)).comp (f := fun w : E => ‖w - z₀‖) hnorm).div
        hnorm hr.ne'
    have hb : ContinuousAt (fun w : E => innerSL ℝ (w - z₀)) z :=
      ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous.comp
        (continuous_id.sub continuous_const)).continuousAt
    exact ha.smul hb

/-- **Twice the Wirtinger derivative of a sum of radial primitives.** For a finite family of
profiles `f α`, each continuous on `[0, ∞)` with `f α 0 = 0`, and centres `z₀ α` in `ℂ`,
include the real sum `W w = ∑ α ∈ s, ∫ t in 0..‖w - z₀ α‖, f α t` in `ℂ`. Then
`2 * barDeriv W z`, which is `∂ₓW + i ∂ᵧW` for the real derivatives, equals
`∑ α ∈ s, (f α ‖z - z₀ α‖ / ‖z - z₀ α‖) * (z - z₀ α)` at every `z`. Each summand is
`0` at its own centre `z₀ α`; the sum need not vanish there. -/
theorem two_mul_barDeriv_ofReal_sum_intervalIntegral_norm_sub {ι : Type*} (s : Finset ι)
    {f : ι → ℝ → ℝ} (hf : ∀ α ∈ s, ContinuousOn (f α) (Set.Ici 0))
    (hf0 : ∀ α ∈ s, f α 0 = 0) (z₀ : ι → ℂ) (z : ℂ) :
    2 * barDeriv (fun w : ℂ => ((∑ α ∈ s, ∫ t in (0 : ℝ)..‖w - z₀ α‖, f α t : ℝ) : ℂ)) z =
      ∑ α ∈ s, ((f α ‖z - z₀ α‖ / ‖z - z₀ α‖ : ℝ) : ℂ) * (z - z₀ α) := by
  have hS := HasFDerivAt.fun_sum fun α hα =>
    hasFDerivAt_intervalIntegral_norm_sub (hf α hα) (hf0 α hα) (z₀ α) z
  have hd := ((Complex.ofRealCLM.hasFDerivAt).comp z hS).fderiv
  simp only [Function.comp_def] at hd
  unfold barDeriv
  rw [show (fun w : ℂ => ((∑ α ∈ s, ∫ t in (0 : ℝ)..‖w - z₀ α‖, f α t : ℝ) : ℂ)) =
    fun w => Complex.ofRealCLM (∑ α ∈ s, ∫ t in (0 : ℝ)..‖w - z₀ α‖, f α t) from rfl, hd]
  apply Complex.ext <;>
    simp [innerSL_apply_apply, Complex.inner, Complex.mul_re, Complex.mul_im,
      Complex.re_sum, Complex.im_sum, Finset.mul_sum]

end MathlibExt.Analysis.InnerProductSpace.RadialPrimitive
