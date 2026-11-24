/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.InitialInverseColeHopf
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Initial-time forced inverse Cole–Hopf normalization

The velocity-only initial normalization gains the time integral of the spatial
average of the potential. The plus sign cancels the average-potential term in
the weighted moment identity. Thus the inverse remains continuous through the
initial time without integrating a spatial velocity derivative there.

The finite-strip evolution argument uses classical spatial C2 regularity and
an actual, jointly continuous first time derivative. It requires neither a
mixed velocity derivative nor a second time derivative.

The forced transform identity is that of Gesztesy and Holden, *The Cole–Hopf and
Miura transformations revisited*, Theorem 3.3 and Remark 3.4,
https://arxiv.org/abs/solv-int/9812025. The normalization here is obtained by
weighted integration of that flux identity to include initial time.
-/

@[expose] public section

open MeasureTheory Set Filter Real
open scoped ContDiff Topology Interval

namespace ColeHopf

/-- Initial logarithmic normalization with the positive time integral of the
potential's spatial average on the anchored unit interval. -/
noncomputable def initialForcedInverseNormalization (ν : ℝ) (u q : ℝ → ℝ → ℝ)
    (a t : ℝ) : ℝ :=
  initialInverseNormalization ν u a t + ∫ s in 0..t, ∫ y in a..a+1, q s y

/-- Positive forced inverse profile normalized to the initial exponential primitive. -/
noncomputable def initialForcedInverseProfile (ν : ℝ) (u q : ℝ → ℝ → ℝ)
    (a t x : ℝ) : ℝ :=
  exp (initialForcedInverseNormalization ν u q a t - (∫ y in a..x, u t y) / (2*ν))

/-- The forced normalization vanishes at time zero without analytic assumptions. -/
@[simp] theorem initialForcedInverseNormalization_zero (ν : ℝ) (u q : ℝ → ℝ → ℝ) (a : ℝ) :
    initialForcedInverseNormalization ν u q a 0 = 0 := by
  simp [initialForcedInverseNormalization]

/-- The forced inverse has the prescribed initial exponential primitive. -/
@[simp] theorem initialForcedInverseProfile_zero (ν : ℝ) (u q : ℝ → ℝ → ℝ) (a x : ℝ) :
    initialForcedInverseProfile ν u q a 0 x = initialHeatProfile ν (u 0) a x := by
  simp [initialForcedInverseProfile,initialHeatProfile,neg_div]

/-- The forced inverse profile is positive for arbitrary parameters and fields. -/
theorem initialForcedInverseProfile_pos (ν : ℝ) (u q : ℝ → ℝ → ℝ) (a t x : ℝ) :
    0 < initialForcedInverseProfile ν u q a t x := exp_pos _

/-- The average-potential correction multiplies the unforced inverse by a positive
factor depending only on time. This algebraic identity needs no regularity. -/
theorem initialForcedInverseProfile_eq_exp_mul (ν : ℝ) (u q : ℝ → ℝ → ℝ) (a t x : ℝ) :
    initialForcedInverseProfile ν u q a t x =
      exp (∫ s in 0..t, ∫ y in a..a+1, q s y) * initialInverseProfile ν u a t x := by
  unfold initialForcedInverseProfile initialForcedInverseNormalization initialInverseProfile
  rw [show initialInverseNormalization ν u a t + (∫ s in 0..t, ∫ y in a..a+1, q s y) -
      (∫ y in a..x, u t y) / (2*ν) = (∫ s in 0..t, ∫ y in a..a+1, q s y) +
      (initialInverseNormalization ν u a t - (∫ y in a..x, u t y) / (2*ν)) by ring, exp_add]

/-- Zero potential gives the existing initial-time inverse profile. -/
@[simp] theorem initialForcedInverseProfile_zero_potential (ν : ℝ) (u : ℝ → ℝ → ℝ)
    (a t x : ℝ) :
    initialForcedInverseProfile ν u (fun _ _ => 0) a t x = initialInverseProfile ν u a t x := by
  simp [initialForcedInverseProfile_eq_exp_mul]

private theorem parameter_integral_hasDerivAt {u ut : ℝ → ℝ → ℝ} {I : Set ℝ} {a b t : ℝ}
    (hI : IsOpen I) (hu : ContinuousOn (Function.uncurry u) (I ×ˢ uIcc a b))
    (hut : ContinuousOn (Function.uncurry ut) (I ×ˢ uIcc a b))
    (hd : ∀ s ∈ I, ∀ y ∈ uIcc a b, HasDerivAt (fun r => u r y) (ut s y) s)
    (ht : t ∈ I) :
    HasDerivAt (fun s => ∫ y in a..b, u s y) (∫ y in a..b, ut t y) t := by
  have he (p : ℝ × ℝ) (hp : p ∈ I ×ˢ uIcc a b) :
      fderiv ℝ (fun r => u r p.2) p.1 = ContinuousLinearMap.toSpanSingleton ℝ (ut p.1 p.2) :=
    (hd p.1 hp.1 p.2 hp.2).hasFDerivAt.fderiv
  have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (fun r => u r p.2) p.1)
      (I ×ˢ uIcc a b) := by
    have hc := (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp_continuousOn hut
    exact hc.congr (fun p hp => he p hp)
  have hh := intervalIntegral.hasFDerivAt_integral_of_continuousOn_fderiv
    (μ := volume) (hI.mem_nhds ht) hu
    (fun y hy s hs => (hd s hs y hy).differentiableAt.differentiableWithinAt) hfd
  have hi : IntervalIntegrable (fun y => fderiv ℝ (fun s => u s y) t) volume a b :=
    (hfd.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨ht,hy⟩)).intervalIntegrable
  convert hh.hasDerivAt using 1
  rw [ContinuousLinearMap.intervalIntegral_apply hi]
  apply intervalIntegral.integral_congr
  intro y hy
  change ut t y = (fderiv ℝ (fun s => u s y) t) 1
  rw [(hd t ht y hy).hasFDerivAt.fderiv]
  simp

private theorem finite_clamp_continuous {u : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ)) :
    Continuous (fun p : ℝ × ℝ => u (min (max p.1 0) T) p.2) :=
  hc.comp_continuous
    (((continuous_fst.max continuous_const).min continuous_const).prodMk continuous_snd)
    (fun _ => ⟨⟨le_min (le_max_right _ _) hT, min_le_right _ _⟩, mem_univ _⟩)

private theorem finite_primitive_continuousOn {u : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ)) (a : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y in a..p.2, u p.1 y) (Icc 0 T ×ˢ univ) := by
  have hh : Continuous (fun p : (ℝ × ℝ) × ℝ => u (min (max p.1.1 0) T) p.2) :=
    (finite_clamp_continuous hT hc).comp (continuous_fst.fst.prodMk continuous_snd)
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (f := fun p y => u (min (max p.1 0) T) y) hh
    (a₀ := a) continuous_snd
  exact h.continuousOn.congr (fun p hp => by
    simp only [max_eq_left hp.1.1,min_eq_left hp.1.2])

private theorem finite_fixed_integral_continuousOn {u : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ)) (a b : ℝ) :
    ContinuousOn (fun t => ∫ y in a..b, u t y) (Icc 0 T) :=
  (finite_primitive_continuousOn hT hc a).comp (continuousOn_id.prodMk continuousOn_const)
    (fun _ ht => ⟨ht,mem_univ _⟩)

private theorem finite_time_integral_continuousOn {f : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun t => ∫ s in 0..t, f s) (Icc 0 T) := by
  have hh : Continuous (fun t => f (min (max t 0) T)) :=
    hc.comp_continuous ((continuous_id.max continuous_const).min continuous_const)
      (fun _ => ⟨le_min (le_max_right _ _) hT,min_le_right _ _⟩)
  refine (intervalIntegral.differentiable_integral_of_continuous (a := 0) hh).continuous
    |>.continuousOn.congr ?_
  intro t ht
  apply intervalIntegral.integral_congr
  intro s hs
  have hst : s ∈ Icc 0 t := uIcc_of_le ht.1 ▸ hs
  simp only [max_eq_left hst.1,min_eq_left (hst.2.trans ht.2)]

private theorem finite_slice_continuousOn {u : ℝ → ℝ → ℝ} {T : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ)) (x : ℝ) :
    ContinuousOn (fun t => u t x) (Icc 0 T) :=
  hc.comp (continuousOn_id.prodMk continuousOn_const) (fun _ ht => ⟨ht,mem_univ x⟩)

private theorem finite_rate_continuousOn {u : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ)) (ν a : ℝ) :
    ContinuousOn (initialInverseRate ν u a) (Icc 0 T) :=
  ((finite_fixed_integral_continuousOn (u := fun t y => u t y ^ 2) hT
    (by simpa only [Function.uncurry_def,Pi.pow_apply] using! hc.pow 2)
    a (a+1)).div_const (4*ν)).sub
    (((finite_slice_continuousOn hc (a+1)).sub (finite_slice_continuousOn hc a)).div_const 2)

/-- The forced normalization is continuous throughout a finite closed strip using
only joint continuity of the velocity and potential there. -/
theorem initialForcedInverseNormalization_continuousOn {u q : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ)) (ν a : ℝ) :
    ContinuousOn (initialForcedInverseNormalization ν u q a) (Icc 0 T) := by
  have hm : ContinuousOn (initialInverseMoment u a) (Icc 0 T) :=
    finite_fixed_integral_continuousOn (u := fun t y => (a+1-y)*u t y) hT
      (by simpa only [Function.uncurry_def,Pi.mul_apply,Pi.sub_apply] using!
        (continuousOn_const (c := a+1) |>.sub continuousOn_snd).mul hu) a (a+1)
  have hr := finite_time_integral_continuousOn hT (finite_rate_continuousOn hT hu ν a)
  have hqavg := finite_time_integral_continuousOn hT
    (finite_fixed_integral_continuousOn hT hq a (a+1))
  exact (((hm.sub continuousOn_const).div_const (2*ν)).add hr).add hqavg

/-- Joint continuity of the forced inverse profile includes both endpoints of a
finite time strip, without derivative assumptions at either endpoint. -/
theorem initialForcedInverseProfile_continuousOn {u q : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ)) (ν a : ℝ) :
    ContinuousOn (Function.uncurry (initialForcedInverseProfile ν u q a)) (Icc 0 T ×ˢ univ) :=
  (((initialForcedInverseNormalization_continuousOn hT hu hq ν a).comp continuousOn_fst
    (fun p (hp : p ∈ Icc (0 : ℝ) T ×ˢ (univ : Set ℝ)) => hp.1)).sub
      ((finite_primitive_continuousOn hT hu a).div_const (2*ν))).rexp

/-- Spatial differentiation needs only a continuous velocity slice; the potential
average contributes a spatially constant factor. -/
theorem initialForcedInverseProfile_hasDerivAt_x {u q : ℝ → ℝ → ℝ} {t : ℝ}
    (hu : Continuous (u t)) (ν a x : ℝ) :
    HasDerivAt (initialForcedInverseProfile ν u q a t)
      (-u t x / (2*ν) * initialForcedInverseProfile ν u q a t x) x := by
  have h := (((hu.integral_hasStrictDerivAt a x).hasDerivAt.div_const (2*ν)).const_sub
    (initialForcedInverseNormalization ν u q a t)).exp
  change HasDerivAt (fun y => exp (initialForcedInverseNormalization ν u q a t -
    (∫ z in a..y, u t z) / (2*ν))) _ x
  simpa only [initialForcedInverseProfile,neg_div,mul_comm] using! h

/-- The logarithmic transform recovers the velocity from the forced inverse. -/
theorem classicalTransform_initialForcedInverseProfile {u q : ℝ → ℝ → ℝ} {ν t : ℝ}
    (hu : Continuous (u t)) (hν : ν ≠ 0) (a x : ℝ) :
    classicalTransform ν (initialForcedInverseProfile ν u q a) t x = u t x := by
  unfold classicalTransform
  rw [(initialForcedInverseProfile_hasDerivAt_x hu ν a x).deriv]
  have hp := ne_of_gt (initialForcedInverseProfile_pos ν u q a t x)
  field_simp

/-- The forced inverse has the usual second spatial derivative formula. -/
theorem initialForcedInverseProfile_iteratedDeriv_two {u q : ℝ → ℝ → ℝ} {t : ℝ}
    (hu : ContDiff ℝ 2 (u t)) (ν a x : ℝ) :
    iteratedDeriv 2 (initialForcedInverseProfile ν u q a t) x =
      (u t x ^ 2 / (4*ν^2) - deriv (u t) x / (2*ν)) * initialForcedInverseProfile ν u q a t x := by
  have he : initialForcedInverseProfile ν u q a t =
      fun y => exp (∫ s in 0..t, ∫ z in a..a+1, q s z) * initialInverseProfile ν u a t y :=
    funext (initialForcedInverseProfile_eq_exp_mul ν u q a t)
  rw [he,iteratedDeriv_const_mul_field,initialInverseProfile_iteratedDeriv_two hu]
  ring

/-- Spatial C2 regularity of a velocity slice gives spatial C2 regularity of the
forced inverse profile, independently of temporal regularity. -/
theorem initialForcedInverseProfile_contDiff_space {u q : ℝ → ℝ → ℝ} {t : ℝ}
    (hu : ContDiff ℝ 2 (u t)) (ν a : ℝ) :
    ContDiff ℝ 2 (initialForcedInverseProfile ν u q a t) := by
  have he : initialForcedInverseProfile ν u q a t =
      fun y => exp (∫ s in 0..t, ∫ z in a..a+1, q s z) * initialInverseProfile ν u a t y :=
    funext (initialForcedInverseProfile_eq_exp_mul ν u q a t)
  rw [he]
  exact contDiff_const.mul (initialInverseProfile_contDiff_space hu ν a)

/-- Uniformly bounded velocity and continuous potential on a finite closed strip
give uniform exponential growth of the forced inverse profile. No PDE or velocity
derivatives are needed for this bound. -/
theorem initialForcedInverseProfile_hasExpGrowthOnStrip {u q : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M) (ν a : ℝ) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (initialForcedInverseProfile ν u q a) T := by
  obtain ⟨M,hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg (u 0 0)).trans (hM 0 ⟨le_rfl,hT⟩ 0)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (initialForcedInverseNormalization_continuousOn hT hu hq ν a)
  let c := M / |2*ν|
  have hc0 : 0 ≤ c := div_nonneg hM0 (abs_nonneg _)
  refine ⟨exp (C+c*|a|),c,(exp_pos _).le,hc0,fun t ht x => ?_⟩
  have hN : initialForcedInverseNormalization ν u q a t ≤ C :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC t ht)
  have hP : |∫ y in a..x, u t y| ≤ M*|x-a| := by
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a) (b := x) (fun y _ => (show ‖u t y‖ ≤ M by
          simpa only [Real.norm_eq_abs] using hM t ht y)))
  have hQ : -(∫ y in a..x, u t y) / (2*ν) ≤ c*(|x|+|a|) := by
    calc
      _ ≤ |(∫ y in a..x, u t y) / (2*ν)| := by rw [neg_div]; exact neg_le_abs _
      _ = |∫ y in a..x, u t y| / |2*ν| := abs_div _ _
      _ ≤ (M*|x-a|) / |2*ν| := div_le_div_of_nonneg_right hP (abs_nonneg _)
      _ = c*|x-a| := by dsimp [c]; ring
      _ ≤ c*(|x|+|a|) := mul_le_mul_of_nonneg_left (abs_sub x a) hc0
  rw [abs_of_pos (initialForcedInverseProfile_pos ν u q a t x)]
  change exp (_-_) ≤ _
  rw [← exp_add]
  apply exp_le_exp.mpr
  rw [neg_div] at hQ
  nlinarith

/-- The forced inverse has the anchored exponential primitive as its joint initial
trace inside the finite closed strip. -/
theorem initialForcedInverseProfile_tendsto_initial {u q : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ)) (ν a x : ℝ) :
    Tendsto (Function.uncurry (initialForcedInverseProfile ν u q a))
      (𝓝[Icc 0 T ×ˢ univ] (0,x)) (𝓝 (initialHeatProfile ν (u 0) a x)) := by
  have h := initialForcedInverseProfile_continuousOn hT hu hq ν a
    (0,x) ⟨⟨le_rfl,hT⟩,mem_univ x⟩
  simpa only [Function.uncurry_apply_pair,initialForcedInverseProfile_zero] using h.tendsto

private theorem forced_flux_hasDerivAt {u q : ℝ → ℝ → ℝ} {ν t : ℝ}
    (hus : ContDiff ℝ 2 (u t)) (hqx : Differentiable ℝ (q t))
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (q t) y) (y : ℝ) :
    HasDerivAt (fun z => ν*deriv (u t) z - u t z^2/2 - 2*ν*q t z)
      (deriv (fun s => u s y) t) y := by
  have h0 := (hus.differentiable (by norm_num) y).hasDerivAt
  have h1 := (hus.differentiable_deriv_two y).hasDerivAt
  convert ((h1.const_mul ν).sub ((h0.pow 2).div_const 2)).sub
    ((hqx y).hasDerivAt.const_mul (2*ν)) using 1
  have he := hb y
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at he
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
  linarith

private theorem forced_moment_hasDerivAt {u q : ℝ → ℝ → ℝ} {I : Set ℝ} {ν t : ℝ}
    (hI : IsOpen I) (hu : ContinuousOn (Function.uncurry u) (I ×ˢ univ))
    (hut : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => u s p.2) p.1) (I ×ˢ univ))
    (htime : ∀ s ∈ I, ∀ y, DifferentiableAt ℝ (fun r => u r y) s)
    (hus : ContDiff ℝ 2 (u t)) (hqx : Differentiable ℝ (q t)) (ht : t ∈ I)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (q t) y) (a : ℝ) :
    HasDerivAt (initialInverseMoment u a)
      (ν*(u t (a+1)-u t a) - (∫ y in a..a+1, u t y^2)/2 -
        (ν*deriv (u t) a - u t a^2/2) +
        2*ν*(q t a - ∫ y in a..a+1, q t y)) t := by
  have htc : Continuous (fun y => deriv (fun s => u s y) t) := by
    rw [← continuousOn_univ]
    exact hut.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hy => ⟨ht,hy⟩)
  have hxc : Continuous (deriv (u t)) := hus.continuous_deriv (by norm_num)
  let F := fun y => ν*deriv (u t) y - u t y^2/2 - 2*ν*q t y
  have hFc : Continuous F := ((hxc.const_mul ν).sub
    ((hus.continuous.pow 2).div_const 2)).sub (hqx.continuous.const_mul (2*ν))
  have hFd (y : ℝ) : HasDerivAt F (deriv (fun s => u s y) t) y :=
    forced_flux_hasDerivAt hus hqx hb y
  have hw : ContinuousOn (Function.uncurry (fun s y => (a+1-y)*u s y)) (I ×ˢ univ) := by
    simpa only [Function.uncurry_def,Pi.mul_apply,Pi.sub_apply] using!
      (continuousOn_const (c := a+1) |>.sub continuousOn_snd).mul hu
  have hwt : ContinuousOn
      (Function.uncurry (fun s y => (a+1-y)*deriv (fun r => u r y) s)) (I ×ˢ univ) := by
    simpa only [Function.uncurry_def,Pi.mul_apply,Pi.sub_apply] using!
      (continuousOn_const (c := a+1) |>.sub continuousOn_snd).mul hut
  have hm := parameter_integral_hasDerivAt (a := a) (b := a+1) hI
    (hw.mono (fun p hp => ⟨hp.1,mem_univ _⟩))
    (hwt.mono (fun p hp => ⟨hp.1,mem_univ _⟩))
    (fun s hs y _ => (htime s hs y).hasDerivAt.const_mul (a+1-y)) ht
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun y : ℝ => a+1-y) (u' := fun _ => -1)
    (v := F) (v' := fun y => deriv (fun s => u s y) t)
    (by fun_prop) hFc.continuousOn
    (fun y _ => (hasDerivAt_id' y).const_sub (a+1)) (fun y _ => hFd y)
    (continuous_const.intervalIntegrable a (a+1)) (htc.intervalIntegrable a (a+1))
  have hint : (∫ y in a..a+1, F y) =
      ν*(u t (a+1)-u t a) - (∫ y in a..a+1, u t y^2)/2 - 2*ν*(∫ y in a..a+1, q t y) := by
    dsimp [F]
    have hp : Continuous (fun y => u t y^2/2) := by
      simpa only [Pi.pow_apply] using! (hus.continuous.pow 2).div_const 2
    have hF0 : Continuous (fun y => ν*deriv (u t) y - u t y^2/2) := by
      simpa only [Pi.sub_apply] using! (hxc.const_mul ν).sub hp
    rw [intervalIntegral.integral_sub (hF0.intervalIntegrable _ _)
      ((hqx.continuous.const_mul (2*ν)).intervalIntegrable _ _),
      intervalIntegral.integral_sub ((hxc.const_mul ν).intervalIntegrable _ _)
        (hp.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_div,intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => (hus.differentiable (by norm_num) y).hasDerivAt)
      (hxc.intervalIntegrable _ _)]
  convert hm using 1
  · rfl
  · rw [hip,intervalIntegral.integral_const_mul,hint]
    dsimp [F]
    ring

private theorem finite_time_integral_hasDerivAt {f : ℝ → ℝ} {T t : ℝ}
    (hc : ContinuousOn f (Icc 0 T)) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => ∫ s in 0..r, f s) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (hc.mono (by
      rw [uIcc_of_le ht.1.le]
      exact fun _ hs => ⟨hs.1,hs.2.trans ht.2.le⟩)).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hc.mono Ioo_subset_Icc_self) t ht)
    (hc.continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- The derivative-free forced normalization has derivative equal to the usual
inverse rate plus the potential at the anchor. Only actual first time derivatives
and spatial C2 velocity regularity are used, at interior times. -/
theorem initialForcedInverseNormalization_hasDerivAt
    {u q : ℝ → ℝ → ℝ} {ν T t : ℝ}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hut : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => u s p.2) p.1) (Ioo 0 T ×ˢ univ))
    (htime : ∀ s ∈ Ioo 0 T, ∀ y, DifferentiableAt ℝ (fun r => u r y) s)
    (hus : ContDiff ℝ 2 (u t)) (hqx : Differentiable ℝ (q t))
    (ht : t ∈ Ioo 0 T)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (q t) y)
    (hν : ν ≠ 0) (a : ℝ) :
    HasDerivAt (initialForcedInverseNormalization ν u q a)
      (normalizationRate ν u a t + q t a) t := by
  have hT : 0 ≤ T := (ht.1.trans ht.2).le
  have hi := finite_time_integral_hasDerivAt (finite_rate_continuousOn hT hu ν a) ht
  have hqi := finite_time_integral_hasDerivAt
    (finite_fixed_integral_continuousOn hT hq a (a+1)) ht
  have hm := forced_moment_hasDerivAt isOpen_Ioo
    (hu.mono (fun p hp => ⟨⟨hp.1.1.le,hp.1.2.le⟩,hp.2⟩)) hut htime hus hqx ht hb a
  convert ((((hm.sub_const (initialInverseMoment u a 0)).div_const (2*ν)).add hi).add hqi) using 1
  · rfl
  · unfold normalizationRate initialInverseRate
    field_simp
    ring

/-- Actual time derivative of the initial-time forced inverse profile. The velocity
need not have mixed derivatives or a second time derivative. -/
theorem initialForcedInverseProfile_hasDerivAt_t
    {u q : ℝ → ℝ → ℝ} {ν T t : ℝ}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hut : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => u s p.2) p.1) (Ioo 0 T ×ˢ univ))
    (htime : ∀ s ∈ Ioo 0 T, ∀ y, DifferentiableAt ℝ (fun r => u r y) s)
    (hus : ContDiff ℝ 2 (u t)) (hqx : Differentiable ℝ (q t))
    (ht : t ∈ Ioo 0 T)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (q t) y)
    (hν : ν ≠ 0) (a x : ℝ) :
    HasDerivAt (fun s => initialForcedInverseProfile ν u q a s x)
      ((normalizationRate ν u x t + q t x) * initialForcedInverseProfile ν u q a t x) t := by
  have hN := initialForcedInverseNormalization_hasDerivAt hu hq hut htime hus hqx ht hb hν a
  have hP := parameter_integral_hasDerivAt (a := a) (b := x) (I := Ioo 0 T)
    (ut := fun s y => deriv (fun r => u r y) s) isOpen_Ioo
    (hu.mono (fun p hp => ⟨⟨hp.1.1.le,hp.1.2.le⟩,mem_univ _⟩))
    (hut.mono (fun p (hp : p ∈ Ioo 0 T ×ˢ uIcc a x) => ⟨hp.1,mem_univ _⟩))
    (fun s hs y _ => (htime s hs y).hasDerivAt) ht
  have htc : Continuous (fun y => deriv (fun s => u s y) t) := by
    rw [← continuousOn_univ]
    exact hut.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hy => ⟨ht,hy⟩)
  have hflux : (∫ y in a..x, deriv (fun s => u s y) t) =
      (ν*deriv (u t) x - u t x^2/2 - 2*ν*q t x) -
      (ν*deriv (u t) a - u t a^2/2 - 2*ν*q t a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => forced_flux_hasDerivAt hus hqx hb y) (htc.intervalIntegrable a x)
  have hd := (hN.sub (hP.div_const (2*ν))).exp
  rw [hflux] at hd
  have he : normalizationRate ν u a t + q t a -
      ((ν*deriv (u t) x - u t x^2/2 - 2*ν*q t x) -
        (ν*deriv (u t) a - u t a^2/2 - 2*ν*q t a)) / (2*ν) =
      normalizationRate ν u x t + q t x := by
    unfold normalizationRate
    field_simp
    ring
  rw [he] at hd
  simpa only [initialForcedInverseProfile,Pi.sub_apply,mul_comm] using! hd

/-- The forced inverse solves the actual potential-heat equation at every interior
time. Temporal regularity is C1 only; spatial C2 suffices for the velocity slice. -/
theorem initialForcedInverseProfile_hasDerivAt_potential
    {u q : ℝ → ℝ → ℝ} {ν T t : ℝ}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hut : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => u s p.2) p.1) (Ioo 0 T ×ˢ univ))
    (htime : ∀ s ∈ Ioo 0 T, ∀ y, DifferentiableAt ℝ (fun r => u r y) s)
    (hus : ContDiff ℝ 2 (u t)) (hqx : Differentiable ℝ (q t))
    (ht : t ∈ Ioo 0 T)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (q t) y)
    (hν : ν ≠ 0) (a x : ℝ) :
    HasDerivAt (fun s => initialForcedInverseProfile ν u q a s x)
      (ν*iteratedDeriv 2 (initialForcedInverseProfile ν u q a t) x +
        q t x * initialForcedInverseProfile ν u q a t x) t := by
  convert initialForcedInverseProfile_hasDerivAt_t hu hq hut htime hus hqx ht hb hν a x using 1
  rw [initialForcedInverseProfile_iteratedDeriv_two hus]
  unfold normalizationRate
  field_simp

end ColeHopf
