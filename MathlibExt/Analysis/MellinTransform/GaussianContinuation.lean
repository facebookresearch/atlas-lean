/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Analysis.Meromorphic.Complex
public import MathlibExt.Analysis.SpecialFunctions.ParabolicCylinder.IntegralRepresentation
public import MathlibExt.Analysis.SpecialFunctions.ParabolicCylinder.OrderAnalyticity

/-!
# Meromorphic continuation of Gaussian Laplace Mellin integrals

For complex z, set F_z(s) = exp(z²/4) Γ(s) U(s-1/2,z), where U has the
normalization U(a,z)=D_(-a-1/2)(z). Its canonical meromorphic normal-form
representative G_z agrees with F_z in every punctured germ. Removable
singularities take their analytic limiting values; genuine poles take
the normal-form point value zero.

For Re(s) > 0, G_z(s) is ∫₀∞ t^(s-1) exp(-t²/2-zt) dt.
The removable zero-tilt cancellation at s=-1 has value
G_0(-1)=2^(-3/2) Γ(-1/2).
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace Complex

private lemma analyticAt_shiftedU (z s : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => parabolicCylinderU (u - 1 / 2) z) s := by
  exact (analyticAt_parabolicCylinderU_order (s - 1 / 2) z).comp
    (f := fun u : ℂ => u - 1 / 2) (x := s) (by fun_prop)

private lemma raw_meromorphic (z : ℂ) :
    MeromorphicOn (fun s : ℂ => exp (z ^ 2 / 4) * Gamma s *
      parabolicCylinderU (s - 1 / 2) z) univ := by
  have hU : AnalyticOnNhd ℂ (fun s : ℂ => parabolicCylinderU (s - 1 / 2) z) univ :=
    fun s _ => analyticAt_shiftedU z s
  have hc : MeromorphicOn (fun _ : ℂ => exp (z ^ 2 / 4)) univ := MeromorphicOn.const _
  have hGamma : MeromorphicOn Gamma univ := MeromorphicOn.Gamma
  have h := (hc.mul hGamma).mul hU.meromorphicOn
  have hfunction : (fun _ : ℂ => exp (z ^ 2 / 4)) * Gamma *
      (fun s : ℂ => parabolicCylinderU (s - 1 / 2) z) =
      fun s : ℂ => exp (z ^ 2 / 4) * Gamma s * parabolicCylinderU (s - 1 / 2) z := by
    funext s
    simp only [Pi.mul_apply]
  rw [hfunction] at h
  exact h

private lemma analyticAt_raw_of_re_pos (z s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (fun u : ℂ => exp (z ^ 2 / 4) * Gamma u *
      parabolicCylinderU (u - 1 / 2) z) s := by
  have hNF : MeromorphicNFAt Gamma s := MeromorphicNFOn.Gamma (mem_univ s)
  have horder : meromorphicOrderAt Gamma s = 0 :=
    hNF.meromorphicOrderAt_eq_zero_iff.mpr (Gamma_ne_zero_of_re_pos hs)
  have hGamma : AnalyticAt ℂ Gamma s :=
    hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp (by simp [horder])
  exact (analyticAt_const.mul hGamma).mul (analyticAt_shiftedU z s)

/-- For complex z,s, gaussianLaplaceMellinContinuation z s is the canonical
meromorphic normal-form value of exp(z²/4) Γ(s) U(s-1/2,z).
Removable singularities take their analytic limits; genuine poles have
normal-form value zero. -/
def gaussianLaplaceMellinContinuation (z s : ℂ) : ℂ :=
  toMeromorphicNFOn (fun u : ℂ => exp (z ^ 2 / 4) * Gamma u *
    parabolicCylinderU (u - 1 / 2) z) univ s

/-- For every complex z, the function s ↦ gaussianLaplaceMellinContinuation z s
is in meromorphic normal form throughout ℂ. -/
theorem meromorphicNFOn_gaussianLaplaceMellinContinuation (z : ℂ) :
    MeromorphicNFOn (gaussianLaplaceMellinContinuation z) univ := by
  exact meromorphicNFOn_toMeromorphicNFOn _ _

/-- For every complex z,s, the continuation and
u ↦ exp(z²/4) Γ(u) U(u-1/2,z) agree in a sufficiently small punctured
neighborhood of s. -/
theorem gaussianLaplaceMellinContinuation_eventuallyEq_raw (z s : ℂ) :
    gaussianLaplaceMellinContinuation z =ᶠ[𝓝[≠] s]
      fun u : ℂ => exp (z ^ 2 / 4) * Gamma u * parabolicCylinderU (u - 1 / 2) z := by
  exact (raw_meromorphic z).toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- For complex z,s, if u ↦ exp(z²/4) Γ(u) U(u-1/2,z) is analytic at s,
its canonical continuation has the same value at s as that raw product. -/
theorem gaussianLaplaceMellinContinuation_eq_raw_of_analyticAt (z s : ℂ)
    (h : AnalyticAt ℂ (fun u : ℂ => exp (z ^ 2 / 4) * Gamma u *
      parabolicCylinderU (u - 1 / 2) z) s) :
    gaussianLaplaceMellinContinuation z s =
      exp (z ^ 2 / 4) * Gamma s * parabolicCylinderU (s - 1 / 2) z := by
  unfold gaussianLaplaceMellinContinuation
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (raw_meromorphic z) (mem_univ s),
    toMeromorphicNFAt_eq_self.mpr h.meromorphicNFAt]

/-- For complex z,s with Re(s) > 0, gaussianLaplaceMellinContinuation z s equals
the convergent integral ∫₀∞ t^(s-1) exp(-t²/2-zt) dt. -/
theorem gaussianLaplaceMellinContinuation_eq_mellin (z s : ℂ) (hs : 0 < s.re) :
    gaussianLaplaceMellinContinuation z s =
      mellin (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2 - z * (t : ℂ))) s := by
  exact (gaussianLaplaceMellinContinuation_eq_raw_of_analyticAt z s
    (analyticAt_raw_of_re_pos z s hs)).trans
      (mellin_gaussian_laplace_eq_parabolicCylinderU s z hs).symm

private lemma gamma_shift_half_ne_puncture :
    ∀ᶠ s : ℂ in 𝓝[≠] (-1), Gamma ((s + 1) / 2) ≠ 0 := by
  have hball : ∀ᶠ s : ℂ in 𝓝[≠] (-1), ‖s + 1‖ < 1 := by
    have h : ∀ᶠ s : ℂ in 𝓝 (-1), ‖s + 1‖ < 1 := by
      filter_upwards [Metric.ball_mem_nhds (-1 : ℂ) (by norm_num : (0 : ℝ) < 1)] with s hs
      have hd : dist s (-1 : ℂ) < 1 := Metric.mem_ball.mp hs
      simpa only [dist_eq_norm, sub_neg_eq_add] using hd
    exact h.filter_mono nhdsWithin_le_nhds
  filter_upwards [hball, self_mem_nhdsWithin] with s hsBound hsNe
  change s ≠ (-1 : ℂ) at hsNe
  apply Gamma_ne_zero
  intro n hn
  have hnorm : ‖(s + 1) / 2‖ < 1 / 2 := by
    have hnormEq : ‖(s + 1) / 2‖ = ‖s + 1‖ / 2 := by simp
    rw [hnormEq]
    exact div_lt_div_of_pos_right hsBound (by norm_num)
  by_cases hnzero : n = 0
  · have hzero : (s + 1) / 2 = 0 := by simpa only [hnzero, Nat.cast_zero, neg_zero] using hn
    have hsum : s + 1 = 0 := by
      have h := congrArg (fun u : ℂ => u * 2) hzero
      simpa only [div_mul_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0), zero_mul] using h
    apply hsNe
    calc
      s = (s + 1) - 1 := by ring
      _ = -1 := by rw [hsum]; ring
  · have hge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnzero)
    have hnormEq : ‖(s + 1) / 2‖ = (n : ℝ) := by rw [hn, norm_neg, Complex.norm_natCast]
    rw [hnormEq] at hnorm
    linarith

/-- The canonical zero-tilt continuation at the removable point s=-1 is
G_0(-1)=2^(-3/2) Γ(-1/2), with the positive-base complex-power convention. -/
theorem gaussianLaplaceMellinContinuation_zero_neg_one :
    gaussianLaplaceMellinContinuation 0 (-1) = (2 : ℂ) ^ (-3 / 2 : ℂ) * Gamma (-1 / 2) := by
  let g : ℂ → ℂ := fun s => (2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2)
  have hGamma : MeromorphicNFAt Gamma ((-1 : ℂ) / 2) :=
    MeromorphicNFOn.Gamma (mem_univ _)
  have hhalf : MeromorphicNFAt (fun s : ℂ => Gamma (s / 2)) (-1) := by
    simpa only [Function.comp_def] using
      hGamma.comp_analyticAt (g := fun s : ℂ => s / 2) (x := (-1 : ℂ))
        (by fun_prop : AnalyticAt ℂ (fun s : ℂ => s / 2) (-1))
  have hpower : AnalyticAt ℂ (fun s : ℂ => (2 : ℂ) ^ (s / 2 - 1)) (-1) := by
    simp_rw [cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    fun_prop
  have hpowerNe : (2 : ℂ) ^ ((-1 : ℂ) / 2 - 1) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hg : MeromorphicNFAt g (-1) := by
    have h := (meromorphicNFAt_mul_iff_right hpower hpowerNe).mpr hhalf
    have hfunction : (fun s : ℂ => (2 : ℂ) ^ (s / 2 - 1)) * (fun s : ℂ => Gamma (s / 2)) = g := by
      funext s
      simp only [Pi.mul_apply, g]
    rw [hfunction] at h
    exact h
  have hfg : (fun s : ℂ => exp ((0 : ℂ) ^ 2 / 4) * Gamma s *
      parabolicCylinderU (s - 1 / 2) 0) =ᶠ[𝓝[≠] (-1)] g := by
    filter_upwards [gamma_shift_half_ne_puncture] with s hGammaB
    simpa [g] using Gamma_mul_parabolicCylinderU_zero s hGammaB
  have hpoint := (toMeromorphicNFAt_eventuallyEq_nhds_congr hfg).eq_of_nhds
  rw [toMeromorphicNFAt_eq_self.mpr hg] at hpoint
  unfold gaussianLaplaceMellinContinuation
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (raw_meromorphic 0) (mem_univ _)]
  calc
    _ = g (-1) := hpoint
    _ = _ := by
      dsimp only [g]
      rw [show (-1 : ℂ) / 2 - 1 = -3 / 2 by ring]

end Complex
