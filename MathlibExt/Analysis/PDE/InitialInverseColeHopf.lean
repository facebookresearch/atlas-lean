/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.LocalInverseColeHopf
public import MathlibExt.Analysis.PDE.BurgersInitialValue
public import MathlibExt.Analysis.PDE.HeatWholeLine
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Inverse Cole–Hopf normalization at initial time

A spatial average removes the pointwise spatial derivative from the definition
of the time normalization. With anchor `a`, write
`R(t) = ∫ a..a+1, (a+1-y) u(t,y)` and
`b(t) = (∫ a..a+1, u(t,y)^2)/(4ν) - (u(t,a+1)-u(t,a))/2`.
The logarithmic factor is `A(t) = (R(t)-R(0))/(2ν) + ∫ 0..t, b`.
Integration by parts in Burgers gives `A'(t) = normalizationRate ν u a t`
for positive times. Thus `exp(A(t) - (∫ a..x, u(t,y))/(2ν))` solves heat,
assuming `ν ≠ 0`, joint continuity on `[0,∞) × ℝ`, joint `C²` regularity on
`(0,∞) × ℝ`, and Burgers on that positive-time domain. These are half-line
hypotheses; solutions defined only up to a finite lifespan are not covered here.

Only continuity is required at time zero. No derivative at zero, integrability
of the pointwise normalization rate there, or bound on spatial derivatives is
assumed. Bounded velocity on each finite strip gives uniform exponential
spatial growth of this positive heat profile on that strip.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ContDiff Topology Interval

namespace ColeHopf

/-- Weighted velocity integral on a unit interval starting at the spatial anchor. -/
noncomputable def initialInverseMoment (u : ℝ → ℝ → ℝ) (a t : ℝ) : ℝ :=
  ∫ y in a..a + 1, (a + 1 - y) * u t y

/-- Averaged flux rate, involving only velocities and no derivatives. -/
noncomputable def initialInverseRate (ν : ℝ) (u : ℝ → ℝ → ℝ) (a t : ℝ) : ℝ :=
  (∫ y in a..a + 1, u t y ^ 2) / (4 * ν) - (u t (a + 1) - u t a) / 2

/-- Initial-time logarithmic normalization; the initial correction fixes the scale. -/
noncomputable def initialInverseNormalization (ν : ℝ) (u : ℝ → ℝ → ℝ) (a t : ℝ) : ℝ :=
  (initialInverseMoment u a t - initialInverseMoment u a 0) / (2 * ν) +
    ∫ s in 0..t, initialInverseRate ν u a s

/-- Positive inverse profile whose initial value is the anchored exponential. -/
noncomputable def initialInverseProfile (ν : ℝ) (u : ℝ → ℝ → ℝ) (a t x : ℝ) : ℝ :=
  Real.exp (initialInverseNormalization ν u a t - (∫ y in a..x, u t y) / (2 * ν))

/-- The normalization vanishes at initial time, without regularity assumptions. -/
@[simp] theorem initialInverseNormalization_zero (ν : ℝ) (u : ℝ → ℝ → ℝ) (a : ℝ) :
    initialInverseNormalization ν u a 0 = 0 := by simp [initialInverseNormalization]

/-- The profile is positive for all arguments. -/
theorem initialInverseProfile_pos (ν : ℝ) (u : ℝ → ℝ → ℝ) (a t x : ℝ) :
    0 < initialInverseProfile ν u a t x := Real.exp_pos _

/-- The initial heat profile is exactly the prescribed anchored exponential. -/
@[simp] theorem initialInverseProfile_zero (ν : ℝ) (u : ℝ → ℝ → ℝ) (a x : ℝ) :
    initialInverseProfile ν u a 0 x = initialHeatProfile ν (u 0) a x := by
  simp [initialInverseProfile, initialHeatProfile, neg_div]

private theorem continuous_clamp {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ)) :
    Continuous (fun p : ℝ × ℝ => u (max p.1 0) p.2) :=
  hc.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
    (fun _ => ⟨le_max_right _ _, mem_univ _⟩)

private theorem primitive_continuousOn {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ)) (a : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y in a..p.2, u p.1 y) (Ici 0 ×ˢ univ) := by
  have hh : Continuous (fun p : (ℝ × ℝ) × ℝ => u (max p.1.1 0) p.2) :=
    (continuous_clamp hc).comp (continuous_fst.fst.prodMk continuous_snd)
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (f := fun p y => u (max p.1 0) y) hh
    (a₀ := a) continuous_snd
  exact h.continuousOn.congr (fun p hp => by simp only [max_eq_left hp.1])

private theorem fixed_integral_continuousOn {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ)) (a b : ℝ) :
    ContinuousOn (fun t => ∫ y in a..b, u t y) (Ici 0) :=
  (primitive_continuousOn hc a).comp (continuousOn_id.prodMk continuousOn_const)
    (fun _ ht => ⟨ht, mem_univ _⟩)

private theorem slice_continuousOn {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ)) (x : ℝ) :
    ContinuousOn (fun t => u t x) (Ici 0) :=
  hc.comp (continuousOn_id.prodMk continuousOn_const) (fun _ ht => ⟨ht, mem_univ _⟩)

/-- Continuity of the averaged flux through time zero needs only continuity of velocity. -/
theorem initialInverseRate_continuousOn {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ)) (ν a : ℝ) :
    ContinuousOn (initialInverseRate ν u a) (Ici 0) :=
  ((fixed_integral_continuousOn (u := fun t y => u t y ^ 2)
    (by simpa only [Function.uncurry_def, Pi.pow_apply] using! hc.pow 2)
    a (a + 1)).div_const (4 * ν)).sub
    (((slice_continuousOn hc (a + 1)).sub (slice_continuousOn hc a)).div_const 2)

/-- The logarithmic normalization extends continuously through time zero. -/
theorem initialInverseNormalization_continuousOn {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ)) (ν a : ℝ) :
    ContinuousOn (initialInverseNormalization ν u a) (Ici 0) := by
  have hm : ContinuousOn (initialInverseMoment u a) (Ici 0) :=
    fixed_integral_continuousOn (u := fun t y => (a + 1 - y) * u t y)
      (by simpa only [Function.uncurry_def, Pi.mul_apply, Pi.sub_apply] using!
        (continuousOn_const (c := a + 1) |>.sub continuousOn_snd).mul hc) a (a + 1)
  have hr := initialInverseRate_continuousOn hc ν a
  have hh : Continuous (fun t => initialInverseRate ν u a (max t 0)) :=
    hr.comp_continuous (continuous_id.max continuous_const) (fun _ => le_max_right _ _)
  have hi : ContinuousOn (fun t => ∫ s in 0..t, initialInverseRate ν u a s) (Ici 0) := by
    refine (intervalIntegral.differentiable_integral_of_continuous (a := 0) hh).continuous
      |>.continuousOn.congr ?_
    intro t ht
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [max_eq_left (show 0 ≤ s from (uIcc_of_le ht ▸ hs).1)]
  exact ((hm.sub continuousOn_const).div_const (2 * ν)).add hi

/-- Joint continuity of the positive profile, including initial time. -/
theorem initialInverseProfile_continuousOn {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ)) (ν a : ℝ) :
    ContinuousOn (Function.uncurry (initialInverseProfile ν u a)) (Ici 0 ×ˢ univ) :=
  (((initialInverseNormalization_continuousOn hc ν a).comp continuousOn_fst
    (fun p (hp : p ∈ Ici (0 : ℝ) ×ˢ (univ : Set ℝ)) => hp.1)).sub
      ((primitive_continuousOn hc a).div_const (2 * ν))).rexp


private theorem positive_slice {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ)) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 2 (u t) := by
  rw [← contDiffOn_univ]
  exact hu.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨ht, hx⟩)

private theorem moment_hasDerivAt {u : ℝ → ℝ → ℝ} {ν t : ℝ}
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ)) (ht : 0 < t)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (a : ℝ) :
    HasDerivAt (initialInverseMoment u a)
      (ν * (u t (a + 1) - u t a) - (∫ y in a..a + 1, u t y ^ 2) / 2 -
        (ν * deriv (u t) a - u t a ^ 2 / 2)) t := by
  have hs := positive_slice hu ht
  have hd := OnInterval.contDiffOn_spaceDeriv isOpen_Ioi isOpen_univ hu
    (by norm_num) (m := 1) (by norm_num)
  have hdt := OnInterval.contDiffOn_timeDeriv isOpen_Ioi isOpen_univ hu
    (by norm_num) (m := 1) (by norm_num)
  have htc : Continuous (fun y => deriv (fun s => u s y) t) := by
    rw [← continuousOn_univ]
    exact hdt.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hx => ⟨ht, hx⟩)
  have hxc : Continuous (deriv (u t)) := hs.continuous_deriv (by norm_num)
  let q : ℝ → ℝ := fun y => ν * deriv (u t) y - u t y ^ 2 / 2
  have hq : Continuous q := (hxc.const_mul ν).sub ((hs.continuous.pow 2).div_const 2)
  have hq' (y : ℝ) : HasDerivAt q (deriv (fun s => u s y) t) y := by
    have h0 := OnInterval.space_derivative isOpen_Ioi isOpen_univ hu (by norm_num)
      t y ht (mem_univ _)
    have h1 := OnInterval.space_derivative isOpen_Ioi isOpen_univ hd (by norm_num)
      t y ht (mem_univ _)
    convert (h1.const_mul ν).sub ((h0.pow 2).div_const 2) using 1
    have he := hb y
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at he
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    linarith
  have hw : ContDiffOn ℝ 2
      (Function.uncurry (fun s y => (a + 1 - y) * u s y)) (Ioi 0 ×ˢ univ) := by
    simpa only [Function.uncurry_def, Pi.mul_apply, Pi.sub_apply] using!
      (contDiffOn_const (c := a + 1) |>.sub contDiffOn_snd).mul hu
  have hm := OnInterval.integral_hasDerivAt_time isOpen_Ioi isOpen_univ ordConnected_univ
    hw a (a + 1) t (mem_univ _) (mem_univ _) ht
  have he : (∫ y in a..a + 1, deriv (fun s => (a + 1 - y) * u s y) t) =
      ∫ y in a..a + 1, (a + 1 - y) * deriv (fun s => u s y) t := by
    apply intervalIntegral.integral_congr
    intro y _
    exact ((OnInterval.time_derivative isOpen_Ioi isOpen_univ hu (by norm_num)
      t y ht (mem_univ _)).const_mul (a + 1 - y)).deriv
  rw [he] at hm
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun y : ℝ => a + 1 - y) (u' := fun _ => -1)
    (v := q) (v' := fun y => deriv (fun s => u s y) t)
    (by fun_prop) hq.continuousOn
    (fun y _ => (hasDerivAt_id' y).const_sub (a + 1)) (fun y _ => hq' y)
    (continuous_const.intervalIntegrable a (a + 1)) (htc.intervalIntegrable a (a + 1))
  have hint : (∫ y in a..a + 1, q y) =
      ν * (u t (a + 1) - u t a) - (∫ y in a..a + 1, u t y ^ 2) / 2 := by
    dsimp [q]
    have hpow : Continuous (fun y => u t y ^ 2 / 2) := by
      simpa only [Pi.pow_apply] using! (hs.continuous.pow 2).div_const 2
    rw [intervalIntegral.integral_sub ((hxc.const_mul ν).intervalIntegrable _ _)
      (hpow.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => (hs.differentiable (by norm_num) y).hasDerivAt)
      (hxc.intervalIntegrable _ _)]
  have hcoeff : (∫ y in a..a + 1, (a + 1 - y) * deriv (fun s => u s y) t) =
      ν * (u t (a + 1) - u t a) - (∫ y in a..a + 1, u t y ^ 2) / 2 - q a := by
    rw [hip, intervalIntegral.integral_const_mul, hint]
    ring
  rw [hcoeff] at hm
  exact hm

/-- The derivative-free normalization has the classical inverse rate at positive times. -/
theorem initialInverseNormalization_hasDerivAt {u : ℝ → ℝ → ℝ} {ν t : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ)) (ht : 0 < t)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a : ℝ) :
    HasDerivAt (initialInverseNormalization ν u a) (normalizationRate ν u a t) t := by
  have hr := initialInverseRate_continuousOn hc ν a
  have hi : HasDerivAt (fun r => ∫ s in 0..r, initialInverseRate ν u a s)
      (initialInverseRate ν u a t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hr.mono (by rw [uIcc_of_le ht.le]; exact fun _ hs => hs.1)).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (hr.mono Ioi_subset_Ici_self) t ht)
      (hr.continuousAt (Ici_mem_nhds ht))
  convert (((moment_hasDerivAt hu ht hb a).sub_const (initialInverseMoment u a 0)).div_const
    (2 * ν)).add hi using 1
  · rfl
  · unfold normalizationRate initialInverseRate
    field_simp
    ring


/-- Spatial differentiation needs only continuity of the velocity slice. -/
theorem initialInverseProfile_hasDerivAt_x {u : ℝ → ℝ → ℝ} {t : ℝ}
    (hc : Continuous (u t)) (ν a x : ℝ) :
    HasDerivAt (initialInverseProfile ν u a t)
      (-u t x / (2 * ν) * initialInverseProfile ν u a t x) x := by
  have h := (((hc.integral_hasStrictDerivAt a x).hasDerivAt.div_const (2 * ν)).const_sub
    (initialInverseNormalization ν u a t)).exp
  change HasDerivAt (fun y => Real.exp (initialInverseNormalization ν u a t -
    (∫ z in a..y, u t z) / (2 * ν))) _ x
  simpa only [initialInverseProfile, neg_div, mul_comm] using! h

/-- The classical transform recovers the velocity, including a continuous initial slice. -/
theorem classicalTransform_initialInverseProfile {u : ℝ → ℝ → ℝ} {ν t : ℝ}
    (hc : Continuous (u t)) (hν : ν ≠ 0) (a x : ℝ) :
    classicalTransform ν (initialInverseProfile ν u a) t x = u t x := by
  unfold classicalTransform
  rw [(initialInverseProfile_hasDerivAt_x hc ν a x).deriv]
  have hp := ne_of_gt (initialInverseProfile_pos ν u a t x)
  field_simp

/-- Actual time differentiation at positive times; no derivative at zero is used. -/
theorem initialInverseProfile_hasDerivAt_t {u : ℝ → ℝ → ℝ} {ν t : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ)) (ht : 0 < t)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a x : ℝ) :
    HasDerivAt (fun s => initialInverseProfile ν u a s x)
      (normalizationRate ν u x t * initialInverseProfile ν u a t x) t := by
  have hA := initialInverseNormalization_hasDerivAt hc hu ht hb hν a
  have hP := (OnInterval.integral_hasDerivAt_time isOpen_Ioi isOpen_univ ordConnected_univ
    hu a x t (mem_univ _) (mem_univ _) ht).div_const (2 * ν)
  have hi := OnInterval.integral_timeDeriv_of_forced_burgers isOpen_Ioi isOpen_univ
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

/-- Second spatial derivative of the initial-time inverse profile. -/
theorem initialInverseProfile_iteratedDeriv_two {u : ℝ → ℝ → ℝ} {t : ℝ}
    (hu : ContDiff ℝ 2 (u t)) (ν a x : ℝ) :
    iteratedDeriv 2 (initialInverseProfile ν u a t) x =
      (u t x ^ 2 / (4 * ν ^ 2) - deriv (u t) x / (2 * ν)) *
        initialInverseProfile ν u a t x := by
  have h0 := (hu.differentiable (by norm_num) x).hasDerivAt
  have h1 := initialInverseProfile_hasDerivAt_x hu.continuous ν a x
  have he : deriv (initialInverseProfile ν u a t) =
      fun y => -u t y / (2 * ν) * initialInverseProfile ν u a t y :=
    funext (fun y => (initialInverseProfile_hasDerivAt_x hu.continuous ν a y).deriv)
  have hd : HasDerivAt (fun y => -u t y / (2 * ν) * initialInverseProfile ν u a t y)
      ((-deriv (u t) x / (2 * ν)) * initialInverseProfile ν u a t x +
        (-u t x / (2 * ν)) * (-u t x / (2 * ν) * initialInverseProfile ν u a t x)) x :=
    (h0.neg.div_const (2 * ν)).mul h1
  rw [iteratedDeriv_succ, iteratedDeriv_one, he, hd.deriv]
  ring

/-- The constructed positive profile solves the actual heat equation for positive time. -/
theorem initialInverseProfile_heat {u : ℝ → ℝ → ℝ} {ν t : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ)) (ht : 0 < t)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a x : ℝ) :
    deriv (fun s => initialInverseProfile ν u a s x) t =
      ν * iteratedDeriv 2 (initialInverseProfile ν u a t) x := by
  rw [(initialInverseProfile_hasDerivAt_t hc hu ht hb hν a x).deriv,
    initialInverseProfile_iteratedDeriv_two (positive_slice hu ht) ν a x]
  unfold normalizationRate
  field_simp

/-- Heat evolution with derivative existence, ready for a classical heat uniqueness theorem. -/
theorem initialInverseProfile_hasDerivAt_heat {u : ℝ → ℝ → ℝ} {ν t : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ)) (ht : 0 < t)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a x : ℝ) :
    HasDerivAt (fun s => initialInverseProfile ν u a s x)
      (ν * iteratedDeriv 2 (initialInverseProfile ν u a t) x) t := by
  have h := initialInverseProfile_hasDerivAt_t hc hu ht hb hν a x
  rw [← initialInverseProfile_heat hc hu ht hb hν a x, h.deriv]
  exact h

/-- Positive-time spatial regularity required by whole-line heat uniqueness. -/
theorem initialInverseProfile_contDiff_space {u : ℝ → ℝ → ℝ} {t : ℝ}
    (hu : ContDiff ℝ 2 (u t)) (ν a : ℝ) :
    ContDiff ℝ 2 (initialInverseProfile ν u a t) := by
  have hd : Differentiable ℝ (initialInverseProfile ν u a t) :=
    fun x => (initialInverseProfile_hasDerivAt_x hu.continuous ν a x).differentiableAt
  have he : deriv (initialInverseProfile ν u a t) =
      fun x => -u t x / (2 * ν) * initialInverseProfile ν u a t x :=
    funext (fun x => (initialInverseProfile_hasDerivAt_x hu.continuous ν a x).deriv)
  have h1 : ContDiff ℝ 1 (initialInverseProfile ν u a t) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨hd, ?_⟩
    rw [he]
    exact (hu.continuous.neg.div_const (2 * ν)).mul hd.continuous
  change ContDiff ℝ (1 + 1 : ℕ∞ω) _
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨hd, by simp, ?_⟩
  rw [he]
  exact ((hu.of_le (by norm_num)).neg.div_const (2 * ν)).mul h1


/-- Bounded velocity on a finite strip gives one exponential spatial bound valid
uniformly on that entire strip, including both endpoints. No PDE is needed. -/
theorem initialInverseProfile_hasExpGrowthOnStrip {u : ℝ → ℝ → ℝ} {T : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M) (ν a : ℝ) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip (initialInverseProfile ν u a) T := by
  by_cases hT : 0 ≤ T
  · obtain ⟨M, hM⟩ := hb
    have hM0 : 0 ≤ M := (abs_nonneg (u 0 0)).trans (hM 0 ⟨le_rfl, hT⟩ 0)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((initialInverseNormalization_continuousOn hc ν a).mono
        (show Icc 0 T ⊆ Ici 0 from fun _ ht => ht.1))
    let c := M / |2 * ν|
    have hc0 : 0 ≤ c := div_nonneg hM0 (abs_nonneg _)
    refine ⟨Real.exp (C + c * |a|), c, (Real.exp_pos _).le, hc0, fun t ht x => ?_⟩
    have hA : initialInverseNormalization ν u a t ≤ C :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC t ht)
    have hP : |∫ y in a..x, u t y| ≤ M * |x - a| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_of_norm_le_const
          (a := a) (b := x) (fun y _ => (show ‖u t y‖ ≤ M by
            simpa only [Real.norm_eq_abs] using hM t ht y)))
    have hQ : -(∫ y in a..x, u t y) / (2 * ν) ≤ c * (|x| + |a|) := by
      calc
        _ ≤ |(∫ y in a..x, u t y) / (2 * ν)| := by
          rw [neg_div]; exact neg_le_abs _
        _ = |∫ y in a..x, u t y| / |2 * ν| := abs_div _ _
        _ ≤ (M * |x - a|) / |2 * ν| := div_le_div_of_nonneg_right hP (abs_nonneg _)
        _ = c * |x - a| := by dsimp [c]; ring
        _ ≤ c * (|x| + |a|) := mul_le_mul_of_nonneg_left (abs_sub x a) hc0
    rw [abs_of_pos (initialInverseProfile_pos ν u a t x)]
    change Real.exp (_ - _) ≤ _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [neg_div] at hQ
    nlinarith
  · refine ⟨0, 0, le_rfl, le_rfl, fun t ht _ => ?_⟩
    exact (hT (ht.1.trans ht.2)).elim

/-- Joint initial trace, with time approaching zero through the nonnegative half-line. -/
theorem initialInverseProfile_tendsto_initial {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ)) (ν a x : ℝ) :
    Tendsto (Function.uncurry (initialInverseProfile ν u a))
      (𝓝[Ici 0 ×ˢ univ] (0, x)) (𝓝 (initialHeatProfile ν (u 0) a x)) := by
  simpa only [Function.uncurry_apply_pair, initialInverseProfile_zero] using
    (initialInverseProfile_continuousOn hc ν a (0, x) ⟨le_rfl, mem_univ _⟩).tendsto

end ColeHopf
