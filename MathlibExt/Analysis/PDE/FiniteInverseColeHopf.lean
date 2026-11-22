/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.InitialInverseColeHopf
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Inverse normalization on a finite time domain

Continuity is required only on the closed strip, and the Burgers equation and
joint smoothness only in its interior. Clamping is used solely to transfer
continuity and growth; it is not assumed to preserve the PDE at the endpoints.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ContDiff Topology Interval

namespace ColeHopf

/-- The inverse profile depends only on velocity values between zero and its time. -/
theorem initialInverseProfile_congrOn {u v : ℝ → ℝ → ℝ} {T : ℝ}
    (h : EqOn (Function.uncurry u) (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (ν a : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    initialInverseProfile ν u a t x = initialInverseProfile ν v a t x := by
  have hs (s : ℝ) (hs : s ∈ Icc 0 T) : u s = v s :=
    funext (fun y => h (x := (s, y)) ⟨hs, mem_univ _⟩)
  have h0 := hs 0 ⟨le_rfl, ht.1.trans ht.2⟩
  have hi : (∫ s in 0..t, initialInverseRate ν u a s) =
      ∫ s in 0..t, initialInverseRate ν v a s := by
    apply intervalIntegral.integral_congr
    intro s hs'
    have hm : s ∈ Icc 0 T := ⟨(uIcc_of_le ht.1 ▸ hs').1,
      (uIcc_of_le ht.1 ▸ hs').2.trans ht.2⟩
    simp only [initialInverseRate, hs s hm]
  simp only [initialInverseProfile, initialInverseNormalization, initialInverseMoment,
    hs t ht, h0, hi]

private theorem finite_clamp_continuous {u : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ)) :
    Continuous (fun p : ℝ × ℝ => u (min (max p.1 0) T) p.2) :=
  hc.comp_continuous
    (((continuous_fst.max continuous_const).min continuous_const).prodMk continuous_snd)
    (fun _ => ⟨⟨le_min (le_max_right _ _) hT, min_le_right _ _⟩, mem_univ _⟩)

private theorem finite_clamp_eq {u : ℝ → ℝ → ℝ} {T : ℝ} :
    EqOn (Function.uncurry (fun t x => u (min (max t 0) T) x))
      (Function.uncurry u) (Icc 0 T ×ˢ univ) := by
  intro p hp
  simp only [Function.uncurry_def, max_eq_left hp.1.1, min_eq_left hp.1.2]

/-- Joint continuity of the inverse profile on a finite closed strip. -/
theorem initialInverseProfile_continuousOn_finite {u : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (ν a : ℝ) :
    ContinuousOn (Function.uncurry (initialInverseProfile ν u a)) (Icc 0 T ×ˢ univ) := by
  have hh := initialInverseProfile_continuousOn (u := fun t x => u (min (max t 0) T) x)
    (finite_clamp_continuous hT hc).continuousOn ν a
  exact (hh.mono (fun _ hp => ⟨hp.1.1, hp.2⟩)).congr
    (fun p hp => (initialInverseProfile_congrOn (u := fun t x => u (min (max t 0) T) x)
      (v := u) finite_clamp_eq ν a hp.1 p.2).symm)

/-- Finite-strip continuity and bounded velocity imply exponential profile growth. -/
theorem initialInverseProfile_hasExpGrowthOnStrip_finite {u : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M) (ν a : ℝ) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip (initialInverseProfile ν u a) T := by
  have hb' : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u (min (max t 0) T) x| ≤ M := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, fun t ht x => ?_⟩
    simpa only [max_eq_left ht.1, min_eq_left ht.2] using hM t ht x
  obtain ⟨M, c, hM, hc', h⟩ := initialInverseProfile_hasExpGrowthOnStrip
    (u := fun t x => u (min (max t 0) T) x)
    (finite_clamp_continuous hT hc).continuousOn hb' ν a
  refine ⟨M, c, hM, hc', fun t ht x => ?_⟩
  simpa only [initialInverseProfile_congrOn finite_clamp_eq ν a ht x] using h t ht x

private theorem rate_continuousOn_finite {u : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (ν a : ℝ) : ContinuousOn (initialInverseRate ν u a) (Icc 0 T) := by
  have hh := initialInverseRate_continuousOn (u := fun t x => u (min (max t 0) T) x)
    (finite_clamp_continuous hT hc).continuousOn ν a
  exact (hh.mono (fun _ ht => ht.1)).congr (fun t ht => by
    simp only [initialInverseRate, max_eq_left ht.1, min_eq_left ht.2])

/-- Interior derivative of the finite-time normalization; neither endpoint needs derivatives. -/
theorem initialInverseNormalization_hasDerivAt_finite {u : ℝ → ℝ → ℝ} {ν t T : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ)) (ht : t ∈ Ioo 0 T)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a : ℝ) :
    HasDerivAt (initialInverseNormalization ν u a) (normalizationRate ν u a t) t := by
  have hr := rate_continuousOn_finite (ht.1.trans ht.2).le hc ν a
  have hi : HasDerivAt (fun r => ∫ s in 0..r, initialInverseRate ν u a s)
      (initialInverseRate ν u a t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hr.mono (by
        rw [uIcc_of_le ht.1.le]
        exact fun _ hs => ⟨hs.1, hs.2.trans ht.2.le⟩)).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hr.mono Ioo_subset_Icc_self) t ht)
      (hr.continuousAt (Icc_mem_nhds ht.1 ht.2))
  convert (((initialInverseMoment_hasDerivAt isOpen_Ioo hu ht hb a).sub_const
    (initialInverseMoment u a 0)).div_const (2 * ν)).add hi using 1
  · rfl
  · unfold normalizationRate initialInverseRate
    field_simp
    ring

/-- Actual time differentiation at positive times; no derivative at zero is used. -/
theorem initialInverseProfile_hasDerivAt_t_finite {u : ℝ → ℝ → ℝ} {ν t T : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ)) (ht : t ∈ Ioo 0 T)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a x : ℝ) :
    HasDerivAt (fun s => initialInverseProfile ν u a s x)
      (normalizationRate ν u x t * initialInverseProfile ν u a t x) t := by
  have hA := initialInverseNormalization_hasDerivAt_finite hc hu ht hb hν a
  have hP := (OnInterval.integral_hasDerivAt_time isOpen_Ioo isOpen_univ ordConnected_univ
    hu a x t (mem_univ _) (mem_univ _) ht).div_const (2 * ν)
  have hi := OnInterval.integral_timeDeriv_of_forced_burgers isOpen_Ioo isOpen_univ
    ordConnected_univ ν u (fun _ _ => 0) hu contDiffOn_const t a x ht (mem_univ _)
    (mem_univ _) (by simpa using hb)
  simp only [mul_zero, sub_zero] at hi
  have hd := (hA.sub hP).exp
  rw [hi] at hd
  have he : normalizationRate ν u a t -
      ((ν * deriv (u t) x - u t x ^ 2 / 2) -
        (ν * deriv (u t) a - u t a ^ 2 / 2)) / (2 * ν) = normalizationRate ν u x t := by
    unfold normalizationRate
    field_simp
    ring
  rw [he] at hd
  simpa only [initialInverseProfile, Pi.sub_apply, mul_comm] using! hd

/-- The finite-time profile solves heat, with an actual derivative at every interior time. -/
theorem initialInverseProfile_hasDerivAt_heat_finite {u : ℝ → ℝ → ℝ} {ν t T : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ)) (ht : t ∈ Ioo 0 T)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a x : ℝ) :
    HasDerivAt (fun s => initialInverseProfile ν u a s x)
      (ν * iteratedDeriv 2 (initialInverseProfile ν u a t) x) t := by
  have hs : ContDiff ℝ 2 (u t) := by
    rw [← contDiffOn_univ]
    exact hu.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨ht, hx⟩)
  convert initialInverseProfile_hasDerivAt_t_finite hc hu ht hb hν a x using 1
  rw [initialInverseProfile_iteratedDeriv_two hs ν a x]
  unfold normalizationRate
  field_simp

end ColeHopf
