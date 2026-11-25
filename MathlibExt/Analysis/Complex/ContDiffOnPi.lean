/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Complex_contDiffOn_one_of_differentiableOn_pi.lean`,
`P2M/Sol/S_Complex_contDiffOn_one_of_differentiableOn_pi.lean`,
`Theorems/Thm_Complex_contDiffOn_infty_of_differentiableOn_pi.lean` and
`P2M/Sol/S_Complex_contDiffOn_infty_of_differentiableOn_pi.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Holomorphic functions of several complex variables are smooth

A function `f : (Fin n → ℂ) → E` that is complex differentiable on an open set `U` is
`C¹` on `U`, and in fact `C^∞` on `U`.

The `C¹` statement differentiates the Cauchy integral formula along each coordinate line,
which shows that every partial derivative `z ↦ fderiv ℂ f z (Pi.single i 1)` is continuous.
The `C^∞` statement then shows that `z ↦ fderiv ℂ f z v` is again complex differentiable,
by differentiating a Cauchy integral under the integral sign, and inducts on the order.
-/

@[expose] public section

open Metric Topology Filter Set MeasureTheory
open scoped ContDiff Real

namespace Complex

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}

/-- The `i`-th standard basis vector of `Fin n → ℂ`. -/
private def ev (n : ℕ) (i : Fin n) : Fin n → ℂ := Pi.single i 1

private theorem norm_smul_ev (t : ℂ) (i : Fin n) : ‖t • ev n i‖ = ‖t‖ := by
  rw [norm_smul, ev, Pi.norm_single, norm_one, mul_one]

private theorem add_smul_ev_mem_ball {z₀ z : Fin n → ℂ} {R r : ℝ} (hrR : 2 * r ≤ R)
    (hz : z ∈ ball z₀ r) {t : ℂ} (ht : ‖t‖ ≤ r) (i : Fin n) : z + t • ev n i ∈ ball z₀ R := by
  rw [mem_ball] at hz ⊢
  calc dist (z + t • ev n i) z₀ ≤ dist (z + t • ev n i) z + dist z z₀ := dist_triangle _ _ _
    _ = ‖t • ev n i‖ + dist z z₀ := by rw [dist_eq_norm, add_sub_cancel_left]
    _ = ‖t‖ + dist z z₀ := by rw [norm_smul_ev]
    _ < R := by linarith

omit [CompleteSpace E] in
private theorem differentiableOn_slice (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {z : Fin n → ℂ} (i : Fin n) {s : Set ℂ} (hs : ∀ t ∈ s, z + t • ev n i ∈ U) :
    DifferentiableOn ℂ (fun t : ℂ => f (z + t • ev n i)) s := by
  intro t ht
  have h1 : DifferentiableAt ℂ f (z + t • ev n i) := hf.differentiableAt (hU.mem_nhds (hs t ht))
  have h2 : DifferentiableAt ℂ (fun t : ℂ => z + t • ev n i) t :=
    (differentiableAt_const z).add (differentiableAt_id.smul_const (ev n i))
  exact (h1.comp t h2).differentiableWithinAt

omit [CompleteSpace E] in
private theorem deriv_slice (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {z : Fin n → ℂ}
    (hz : z ∈ U) (i : Fin n) :
    deriv (fun t : ℂ => f (z + t • ev n i)) 0 = fderiv ℂ f z (ev n i) := by
  have h1 : HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • ev n i) := by
    rw [zero_smul, add_zero]
    exact (hf.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℂ => z + t • ev n i) (ev n i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (ev n i)).const_add z
  exact (h1.comp_hasDerivAt (0 : ℂ) h2).deriv

private theorem fderiv_apply_ev_eq_circleIntegral (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {z₀ z : Fin n → ℂ} {R r : ℝ} (hr0 : 0 < r) (hRU : ball z₀ R ⊆ U) (hrR : 2 * r ≤ R)
    (hz : z ∈ ball z₀ r) (i : Fin n) :
    fderiv ℂ f z (ev n i) =
      (2 * Real.pi * I)⁻¹ • ∮ ζ in C(0, r), (1 / (ζ - 0) ^ 2) • f (z + ζ • ev n i) := by
  have hmaps : ∀ t ∈ closedBall (0 : ℂ) r, z + t • ev n i ∈ U := fun t ht =>
    hRU (add_smul_ev_mem_ball hrR hz (by simpa [mem_closedBall, dist_zero_right] using ht) i)
  have hzU : z ∈ U := by
    have := hmaps 0 (mem_closedBall_self hr0.le)
    rwa [zero_smul, add_zero] at this
  have key := (differentiableOn_slice hU hf i hmaps).deriv_eq_smul_circleIntegral hr0
  rw [deriv_slice hU hf hzU i] at key
  rw [key, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]

private theorem continuousOn_fderiv_apply_ev (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (i : Fin n) : ContinuousOn (fun z => fderiv ℂ f z (ev n i)) U := by
  intro z₀ hz₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨R, hR0, hRU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set r : ℝ := R / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hrR : 2 * r ≤ R := by rw [hr]; linarith
  have hF : Continuous (fun p : ↥(ball z₀ r) × ℝ => deriv (circleMap 0 r) p.2 •
      ((1 / (circleMap 0 r p.2 - 0) ^ 2) •
        f ((p.1 : Fin n → ℂ) + circleMap 0 r p.2 • ev n i))) := by
    have h1 : Continuous (fun p : ↥(ball z₀ r) × ℝ => deriv (circleMap 0 r) p.2) := by
      simp_rw [deriv_circleMap]
      exact ((continuous_circleMap 0 r).comp continuous_snd).mul continuous_const
    have h2 : Continuous (fun p : ↥(ball z₀ r) × ℝ => (1 / (circleMap 0 r p.2 - 0) ^ 2)) := by
      refine continuous_const.div
        ((((continuous_circleMap 0 r).comp continuous_snd).sub continuous_const).pow 2)
        (fun p => ?_)
      exact pow_ne_zero _ (sub_ne_zero.mpr (circleMap_ne_center hr0.ne'))
    have h3 : Continuous (fun p : ↥(ball z₀ r) × ℝ =>
        f ((p.1 : Fin n → ℂ) + circleMap 0 r p.2 • ev n i)) := by
      refine hf.continuousOn.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).add
          (((continuous_circleMap 0 r).comp continuous_snd).smul continuous_const)) (fun p => ?_)
      refine hRU (add_smul_ev_mem_ball hrR p.1.2 ?_ i)
      rw [norm_circleMap_zero]
      exact le_of_eq (abs_of_pos hr0)
    exact h1.smul (h2.smul h3)
  have hI : Continuous (fun x : ↥(ball z₀ r) => (2 * Real.pi * I)⁻¹ •
      ∮ ζ in C(0, r), (1 / (ζ - 0) ^ 2) • f ((x : Fin n → ℂ) + ζ • ev n i)) := by
    have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume)
      (f := fun (x : ↥(ball z₀ r)) (θ : ℝ) => deriv (circleMap 0 r) θ •
        ((1 / (circleMap 0 r θ - 0) ^ 2) • f ((x : Fin n → ℂ) + circleMap 0 r θ • ev n i)))
      hF 0 (2 * Real.pi)
    exact this.const_smul _
  have hcont : ContinuousOn (fun z : Fin n → ℂ => (2 * Real.pi * I)⁻¹ •
      ∮ ζ in C(0, r), (1 / (ζ - 0) ^ 2) • f (z + ζ • ev n i)) (ball z₀ r) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hI
  have heq : EqOn (fun z => fderiv ℂ f z (ev n i)) (fun z : Fin n → ℂ => (2 * Real.pi * I)⁻¹ •
      ∮ ζ in C(0, r), (1 / (ζ - 0) ^ 2) • f (z + ζ • ev n i)) (ball z₀ r) :=
    fun z hz => fderiv_apply_ev_eq_circleIntegral hU hf hr0 hRU hrR hz i
  exact (hcont.congr heq).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr0))

omit [CompleteSpace E] in
private theorem fderiv_eq_sum (z : Fin n → ℂ) :
    fderiv ℂ f z = ∑ i, ContinuousLinearMap.smulRightL ℂ (Fin n → ℂ) E
      (ContinuousLinearMap.proj i) (fderiv ℂ f z (ev n i)) := by
  ext v
  rw [sum_apply]
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ContinuousLinearMap.smulRight_apply, map_smul, ev]

/-- A function of several complex variables that is complex differentiable on an open set is
continuously differentiable there. -/
theorem contDiffOn_one_of_differentiableOn_pi (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ 1 f U := by
  have hcont : ContinuousOn (fderiv ℂ f) U := by
    have h : ContinuousOn (fun z => ∑ i, ContinuousLinearMap.smulRightL ℂ (Fin n → ℂ) E
        (ContinuousLinearMap.proj i) (fderiv ℂ f z (ev n i))) U :=
      continuousOn_finsetSum _ fun i _ =>
        (ContinuousLinearMap.smulRightL ℂ (Fin n → ℂ) E
          (ContinuousLinearMap.proj i)).continuous.comp_continuousOn
          (continuousOn_fderiv_apply_ev hU hf i)
    exact h.congr fun z _ => fderiv_eq_sum z
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm,
    contDiffOn_succ_iff_fderiv_of_isOpen hU]
  exact ⟨hf, fun h => absurd h (by simp), contDiffOn_zero.mpr hcont⟩

private theorem differentiableOn_fderiv_apply (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (v : Fin n → ℂ) : DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U := by
  intro z₀ hz₀
  have hC1 : ContDiffOn ℂ 1 f U := contDiffOn_one_of_differentiableOn_pi hU hf
  have hDc : ContinuousOn (fun z => fderiv ℂ f z) U :=
    hC1.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨ρ, hρ, hρU⟩ : ∃ ρ > 0, closedBall z₀ ρ ⊆ U :=
    nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hz₀)
  set r : ℝ := ρ / 3 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  set R : ℝ := r / (‖v‖ + 1) with hR
  have hv0 : 0 < ‖v‖ + 1 := by positivity
  have hR0 : 0 < R := by rw [hR]; positivity
  have hRv : R * ‖v‖ ≤ r := by
    rw [hR, div_mul_eq_mul_div, div_le_iff₀ hv0]; nlinarith [norm_nonneg v]
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ ρ).exists_bound_of_continuousOn (hDc.mono hρU)
  have hmem : ∀ z ∈ ball z₀ r, ∀ w : ℂ, ‖w‖ ≤ 2 * R → z + w • v ∈ closedBall z₀ ρ := by
    intro z hz w hw
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_ball, dist_eq_norm] at hz
    calc ‖z + w • v - z₀‖ = ‖(z - z₀) + w • v‖ := by congr 1; abel
      _ ≤ ‖z - z₀‖ + ‖w • v‖ := norm_add_le _ _
      _ ≤ r + 2 * R * ‖v‖ := by rw [norm_smul]; gcongr
      _ ≤ r + 2 * r := by nlinarith
      _ = ρ := by rw [hr]; ring
  have hmemU : ∀ z ∈ ball z₀ r, ∀ w : ℂ, ‖w‖ ≤ 2 * R → z + w • v ∈ U :=
    fun z hz w hw => hρU (hmem z hz w hw)
  have hdiffAt : ∀ z ∈ ball z₀ r, ∀ w : ℂ, ‖w‖ ≤ 2 * R →
      HasFDerivAt f (fderiv ℂ f (z + w • v)) (z + w • v) :=
    fun z hz w hw => (hf.differentiableAt (hU.mem_nhds (hmemU z hz w hw))).hasFDerivAt
  have hslice : ∀ z ∈ ball z₀ r, fderiv ℂ f z v = (2 * π * Complex.I : ℂ)⁻¹ •
      ∮ w in C(0, R), (1 / (w - 0)) ^ 1 • (w - 0)⁻¹ • f (z + w • v) := by
    intro z hz
    set φ : ℂ → E := fun w => f (z + w • v) with hφ
    have hline : ∀ w : ℂ, HasDerivAt (fun w : ℂ => z + w • v) v w := fun w => by
      simpa using ((hasDerivAt_id w).smul_const v).const_add z
    have hφd : DifferentiableOn ℂ φ (closedBall (0 : ℂ) R) := by
      intro w hw
      have hw' : ‖w‖ ≤ 2 * R := by rw [mem_closedBall, dist_zero_right] at hw; linarith
      exact ((hdiffAt z hz w hw').comp_hasDerivAt w
        (hline w)).differentiableAt.differentiableWithinAt
    have hps := hφd.hasFPowerSeriesOnBall (R := ⟨R, hR0.le⟩) (by exact_mod_cast hR0)
    have h1 : deriv φ 0 = cauchyPowerSeries φ 0 R 1 (fun _ => 1) := hps.hasFPowerSeriesAt.deriv
    have h2 : deriv φ 0 = fderiv ℂ f z v := by
      have h0 : HasFDerivAt f (fderiv ℂ f (z + (0 : ℂ) • v)) (z + (0 : ℂ) • v) :=
        hdiffAt z hz 0 (by rw [norm_zero]; positivity)
      have := (h0.comp_hasDerivAt (0 : ℂ) (hline 0)).deriv
      simp only [zero_smul, add_zero] at this
      exact this
    rw [← h2, h1, cauchyPowerSeries_apply]
  set K : ℝ → ℂ := fun θ => deriv (circleMap 0 R) θ *
    ((1 / (circleMap 0 R θ - 0)) ^ 1 * (circleMap 0 R θ - 0)⁻¹) with hK
  set F : (Fin n → ℂ) → ℝ → E := fun z θ => K θ • f (z + circleMap 0 R θ • v) with hF
  set F' : (Fin n → ℂ) → ℝ → ((Fin n → ℂ) →L[ℂ] E) :=
    fun z θ => K θ • fderiv ℂ f (z + circleMap 0 R θ • v) with hF'
  have hne : ∀ θ : ℝ, circleMap 0 R θ - 0 ≠ 0 := fun θ => by
    rw [sub_zero]; exact circleMap_ne_center hR0.ne'
  have hKc : Continuous K := by
    rw [hK]
    have hd : Continuous fun θ : ℝ => deriv (circleMap 0 R) θ := by
      have : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I :=
        funext (deriv_circleMap 0 R)
      rw [this]; exact (continuous_circleMap 0 R).mul continuous_const
    exact hd.mul
      (((continuous_const.div ((continuous_circleMap 0 R).sub continuous_const) hne).pow 1).mul
        (((continuous_circleMap 0 R).sub continuous_const).inv₀ hne))
  have hKn : ∀ θ, ‖K θ‖ = R⁻¹ := by
    intro θ
    rw [hK]
    simp only [norm_mul, deriv_circleMap, Complex.norm_I, mul_one, sub_zero, norm_pow, norm_div,
      norm_one, norm_inv, norm_circleMap_zero, abs_of_pos hR0]
    field_simp
  have hcR : ∀ θ : ℝ, ‖circleMap 0 R θ‖ ≤ 2 * R := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hR0]; linarith
  have hcirc : ∀ z, (∮ w in C(0, R), (1 / (w - 0)) ^ 1 • (w - 0)⁻¹ • f (z + w • v)) =
      ∫ θ in Ioc 0 (2 * π), F z θ := by
    intro z
    rw [circleIntegral, intervalIntegral.integral_of_le (by positivity)]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    simp only [hF, hK, smul_smul]
  have hFc : ∀ z ∈ ball z₀ r, Continuous (F z) := by
    intro z hz
    rw [hF]
    refine hKc.smul ?_
    exact hf.continuousOn.comp_continuous
      (continuous_const.add ((continuous_circleMap 0 R).smul continuous_const))
      fun θ => hmemU z hz _ (hcR θ)
  have hF'c : Continuous (F' z₀) := by
    rw [hF']
    refine hKc.smul ?_
    exact hDc.comp_continuous
      (continuous_const.add ((continuous_circleMap 0 R).smul continuous_const))
      fun θ => hmemU z₀ (mem_ball_self hr0) _ (hcR θ)
  have hG : HasFDerivAt (fun z => ∫ θ in Ioc 0 (2 * π), F z θ)
      (∫ θ in Ioc 0 (2 * π), F' z₀ θ) z₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume.restrict (Ioc 0 (2 * π))) (s := ball z₀ r)
      (bound := fun _ => R⁻¹ * M) (ball_mem_nhds z₀ hr0) ?_ ?_ ?_ ?_ ?_ ?_
    · exact eventually_of_mem (ball_mem_nhds z₀ hr0) fun z hz =>
        (hFc z hz).aestronglyMeasurable
    · exact (hFc z₀ (mem_ball_self hr0)).integrableOn_Ioc
    · exact hF'c.aestronglyMeasurable
    · refine ae_of_all _ fun θ z hz => ?_
      rw [hF', norm_smul, hKn θ]
      exact mul_le_mul_of_nonneg_left (hM _ (hmem z hz _ (hcR θ))) (by positivity)
    · exact continuous_const.integrableOn_Ioc
    · refine ae_of_all _ fun θ z hz => ?_
      have h1 := hdiffAt z hz (circleMap 0 R θ) (hcR θ)
      have h2 : HasFDerivAt (fun z : Fin n → ℂ => f (z + circleMap 0 R θ • v))
          (fderiv ℂ f (z + circleMap 0 R θ • v)) z := by
        have := h1.comp z ((hasFDerivAt_id z).add_const (circleMap 0 R θ • v))
        rwa [ContinuousLinearMap.comp_id] at this
      have h3 := h2.const_smul (K θ)
      simp only [hF, hF']
      exact h3
  have hev : ∀ᶠ z in 𝓝 z₀,
      fderiv ℂ f z v = (2 * π * Complex.I : ℂ)⁻¹ • ∫ θ in Ioc 0 (2 * π), F z θ :=
    eventually_of_mem (ball_mem_nhds z₀ hr0) fun z hz => by rw [hslice z hz, hcirc]
  exact ((hG.differentiableAt.const_smul ((2 * π * Complex.I : ℂ)⁻¹)).congr_of_eventuallyEq
    hev).differentiableWithinAt

private theorem differentiableOn_fderiv (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fun z => fderiv ℂ f z) U := by
  classical
  set Φ := ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := E) (Fin n) with hΦ
  have hcomp : (fun z => fderiv ℂ f z) =
      fun z => Φ.symm (fun i => fderiv ℂ f z (Pi.single i 1)) := by
    funext z
    apply Φ.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    funext i
    rfl
  rw [hcomp]
  exact Φ.symm.differentiable.comp_differentiableOn
    (differentiableOn_pi.2 fun i => differentiableOn_fderiv_apply hU hf _)

/-- A function of several complex variables that is complex differentiable on an open set is
smooth there. -/
theorem contDiffOn_infty_of_differentiableOn_pi (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ ∞ f U := by
  suffices h : ∀ (m : ℕ) (E' : Type _) [NormedAddCommGroup E'] [NormedSpace ℂ E']
      [CompleteSpace E'] (g : (Fin n → ℂ) → E'), DifferentiableOn ℂ g U → ContDiffOn ℂ m g U by
    exact contDiffOn_infty.2 fun m => h m E f hf
  intro m
  induction m with
  | zero =>
    intro E' _ _ _ g hg
    exact contDiffOn_zero.2 hg.continuousOn
  | succ m ih =>
    intro E' _ _ _ g hg
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hg, by simp, ih _ (fun y => fderiv ℂ g y) (differentiableOn_fderiv hU hg)⟩

end Complex
