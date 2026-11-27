/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.InverseColeHopf
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Forced inverse Cole–Hopf and normalization uniqueness

For `u_t + u u_x = ν u_xx - 2ν F_x`, add `F(t,x₀)` to the logarithmic
normalization rate. The resulting positive, base-point-normalized profile solves
`φ_t = ν φ_xx + F φ`, and its classical transform recovers `u`.

The inverse PDE theorem assumes global joint `C²` regularity for `u`, joint `C¹`
regularity for `F`, and nonzero viscosity. Positive jointly `C³` potential heat
profiles have an exact normalized round trip. Consequently, profiles solving the
same potential equation and having the same transform differ by a unique positive
constant. Equal base-point values make them equal. This is uniqueness within a
fixed transform, not uniqueness for an arbitrary initial-value problem.

Adding a time-only term to the potential changes the reconstructed profile by an
explicit time-only exponential factor. It leaves the Burgers forcing unchanged.

## References

Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*,
Theorem 3.3 and Remark 3.4, https://arxiv.org/abs/solv-int/9812025.
Normalization uniqueness follows directly from the normalized round trip.
We use stronger joint smoothness assumptions on the full real plane; no local-
domain or minimal-regularity result is asserted. Positive viscosity is the usual
physical case; the identities hold for any nonzero real viscosity.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ContDiff Topology Interval

namespace ColeHopf

private theorem slice_x {u : ℝ → ℝ → ℝ} {n : ℕ∞ω}
    (hu : ContDiff ℝ n (Function.uncurry u)) (hn : n ≠ 0) (t x : ℝ) :
    HasDerivAt (u t) (deriv (u t) x) x := by
  exact ((hu.differentiable hn).comp
    ((differentiable_const t).prodMk differentiable_id) x).hasDerivAt

private theorem slice_t {u : ℝ → ℝ → ℝ} {n : ℕ∞ω}
    (hu : ContDiff ℝ n (Function.uncurry u)) (hn : n ≠ 0) (t x : ℝ) :
    HasDerivAt (fun s => u s x) (deriv (fun s => u s x) t) t := by
  exact ((hu.differentiable hn).comp
    (differentiable_id.prodMk (differentiable_const x)) t).hasDerivAt

private theorem contDiff_dx {u : ℝ → ℝ → ℝ} {m n : ℕ∞ω}
    (hu : ContDiff ℝ n (Function.uncurry u)) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    ContDiff ℝ m (Function.uncurry (fun t x => deriv (u t) x)) := by
  have heq : Function.uncurry (fun t x => deriv (u t) x) =
      (fun p => fderiv ℝ (Function.uncurry u) p (0, 1)) := by
    funext p
    have h := (hu.differentiable hn p).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2))
    exact h.deriv
  rw [heq]
  exact (hu.fderiv_right hm).clm_apply contDiff_const

private theorem contDiff_dt {u : ℝ → ℝ → ℝ} {m n : ℕ∞ω}
    (hu : ContDiff ℝ n (Function.uncurry u)) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    ContDiff ℝ m (Function.uncurry (fun t x => deriv (fun s => u s x) t)) := by
  have heq : Function.uncurry (fun t x => deriv (fun s => u s x) t) =
      (fun p => fderiv ℝ (Function.uncurry u) p (1, 0)) := by
    funext p
    have h := (hu.differentiable hn p).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2))
    exact h.deriv
  rw [heq]
  exact (hu.fderiv_right hm).clm_apply contDiff_const

private theorem integral_hasDerivAt_time {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (a b t : ℝ) :
    HasDerivAt (fun s => ∫ y in a..b, u s y)
      (∫ y in a..b, deriv (fun s => u s y) t) t := by
  have hdt := (contDiff_dt hu (by norm_num) (m := 1) (by norm_num)).continuous
  have hK : IsCompact (Metric.closedBall t 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall t 1).prod isCompact_uIcc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hdt.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := u) (F' := fun s y => deriv (fun r => u r y) s)
    (bound := fun _ => M) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t (by norm_num)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with s
    exact (hu.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hu.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hdt.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with y hy s hs
    exact hM (s, y) ⟨Metric.ball_subset_closedBall hs, uIoc_subset_uIcc hy⟩
  · exact continuous_const.intervalIntegrable a b
  · filter_upwards with y _ s _
    exact slice_t hu (by norm_num) s y

/-- Logarithmic normalization rate for the potential heat equation. -/
noncomputable def forcedNormalizationRate (ν : ℝ) (u F : ℝ → ℝ → ℝ) (x₀ t : ℝ) : ℝ :=
  normalizationRate ν u x₀ t + F t x₀

/-- The forced normalized inverse Cole–Hopf potential with potential `F` and base point
`(t₀, x₀)`:
`forcedInversePotential ν u F t₀ x₀ t x = (∫ s in t₀..t, r s) - (∫ y in x₀..x, u t y) / (2 * ν)`,
where `r s = u s x₀ ^ 2 / (4 * ν) - deriv (u s) x₀ / 2 + F s x₀`, with oriented interval
integrals and real division. -/
noncomputable def forcedInversePotential (ν : ℝ) (u F : ℝ → ℝ → ℝ)
    (t₀ x₀ t x : ℝ) : ℝ :=
  (∫ s in t₀..t, forcedNormalizationRate ν u F x₀ s) - (∫ y in x₀..x, u t y) / (2 * ν)

/-- Positive forced inverse profile normalized at the chosen time-space point. -/
noncomputable def forcedInverseProfile (ν : ℝ) (u F : ℝ → ℝ → ℝ)
    (t₀ x₀ t x : ℝ) : ℝ := Real.exp (forcedInversePotential ν u F t₀ x₀ t x)

/-- Zero potential recovers the unforced construction exactly. -/
@[simp] theorem forcedInverseProfile_zero (ν : ℝ) (u : ℝ → ℝ → ℝ) (t₀ x₀ t x : ℝ) :
    forcedInverseProfile ν u (fun _ _ => 0) t₀ x₀ t x = inverseProfile ν u t₀ x₀ t x := by
  simp [forcedInverseProfile, forcedInversePotential, forcedNormalizationRate,
    inverseProfile, inversePotential]

/-- Positivity follows from the exponential, independently of PDE assumptions. -/
theorem forcedInverseProfile_pos (ν : ℝ) (u F : ℝ → ℝ → ℝ) (t₀ x₀ t x : ℝ) :
    0 < forcedInverseProfile ν u F t₀ x₀ t x := Real.exp_pos _

/-- The anchored profile takes value one at the base point. -/
@[simp] theorem forcedInverseProfile_base (ν : ℝ) (u F : ℝ → ℝ → ℝ) (t₀ x₀ : ℝ) :
    forcedInverseProfile ν u F t₀ x₀ t₀ x₀ = 1 := by
  simp [forcedInverseProfile, forcedInversePotential]

/-- For every potential `F`, at the initial time `t₀` the forced inverse Cole–Hopf profile is
`forcedInverseProfile ν u F t₀ x₀ t₀ x = exp (-(∫ y in x₀..x, u t₀ y) / (2 * ν))` for
every `x`. -/
theorem forcedInverseProfile_initial (ν : ℝ) (u F : ℝ → ℝ → ℝ) (t₀ x₀ x : ℝ) :
    forcedInverseProfile ν u F t₀ x₀ t₀ x =
      Real.exp (-(∫ y in x₀..x, u t₀ y) / (2 * ν)) := by
  simp [forcedInverseProfile, forcedInversePotential, neg_div]

/-- The forced normalization rate is continuous under the stated regularity. -/
theorem forcedNormalizationRate_continuous (ν : ℝ) (u F : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hF : Continuous (Function.uncurry F)) (x₀ : ℝ) :
    Continuous (forcedNormalizationRate ν u F x₀) :=
  (normalizationRate_continuous ν u hu x₀).add
    (hF.comp (continuous_id.prodMk continuous_const))

/-- Spatial differentiation is independent of the potential equation. -/
theorem forcedInverseProfile_hasDerivAt_x (ν : ℝ) (u F : ℝ → ℝ → ℝ)
    (t₀ x₀ t x : ℝ) (hu : Continuous (u t)) :
    HasDerivAt (forcedInverseProfile ν u F t₀ x₀ t)
      (-u t x / (2 * ν) * forcedInverseProfile ν u F t₀ x₀ t x) x := by
  have hd := ((hu.integral_hasStrictDerivAt x₀ x).hasDerivAt.div_const (2 * ν)).const_sub
    (∫ s in t₀..t, forcedNormalizationRate ν u F x₀ s)
  change HasDerivAt (fun y => Real.exp (forcedInversePotential ν u F t₀ x₀ t y)) _ x
  simpa only [forcedInverseProfile, forcedInversePotential, neg_div, mul_comm] using! hd.exp

/-- The forward transform of the forced inverse recovers the field. -/
theorem classicalTransform_forcedInverseProfile (ν : ℝ) (hν : ν ≠ 0)
    (u F : ℝ → ℝ → ℝ) (t₀ x₀ t x : ℝ) (hu : Continuous (u t)) :
    classicalTransform ν (forcedInverseProfile ν u F t₀ x₀) t x = u t x := by
  unfold classicalTransform
  rw [(forcedInverseProfile_hasDerivAt_x ν u F t₀ x₀ t x hu).deriv]
  have hp := ne_of_gt (forcedInverseProfile_pos ν u F t₀ x₀ t x)
  field_simp

/-- Integrated forced Burgers equation, including the potential in the flux. -/
theorem integral_timeDeriv_of_forced_burgers (ν : ℝ) (u F : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (hF : ContDiff ℝ 1 (Function.uncurry F))
    (t a b : ℝ)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (F t) y) :
    (∫ y in a..b, deriv (fun s => u s y) t) =
      (ν * deriv (u t) b - u t b ^ 2 / 2 - 2 * ν * F t b) -
      (ν * deriv (u t) a - u t a ^ 2 / 2 - 2 * ν * F t a) := by
  have hx := contDiff_dx hu (by norm_num) (m := 1) (by norm_num)
  have hdt := (contDiff_dt hu (by norm_num) (m := 1) (by norm_num)).continuous
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _
    have h0 := slice_x hu (by norm_num) t y
    have h1 := slice_x hx (by norm_num) t y
    have h2 := slice_x hF (by norm_num) t y
    convert ((h1.const_mul ν).sub ((h0.pow 2).div_const 2)).sub
      (h2.const_mul (2 * ν)) using 1
    have he := hb y
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at he
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    linarith
  · exact (hdt.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b

/-- The forced normalization gives the actual time derivative of the inverse. -/
theorem forcedInverseProfile_hasDerivAt_t (ν : ℝ) (hν : ν ≠ 0)
    (u F : ℝ → ℝ → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (t₀ x₀ t x : ℝ)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (F t) y) :
    HasDerivAt (fun s => forcedInverseProfile ν u F t₀ x₀ s x)
      (forcedNormalizationRate ν u F x t * forcedInverseProfile ν u F t₀ x₀ t x) t := by
  have hc := forcedNormalizationRate_continuous ν u F hu hF.continuous x₀
  have hA := (hc.integral_hasStrictDerivAt t₀ t).hasDerivAt
  have hP := (integral_hasDerivAt_time hu x₀ x t).div_const (2 * ν)
  have hd := (hA.sub hP).exp
  rw [integral_timeDeriv_of_forced_burgers ν u F hu hF t x₀ x hb] at hd
  have hcoeff : forcedNormalizationRate ν u F x₀ t -
      ((ν * deriv (u t) x - u t x ^ 2 / 2 - 2 * ν * F t x) -
        (ν * deriv (u t) x₀ - u t x₀ ^ 2 / 2 - 2 * ν * F t x₀)) / (2 * ν) =
      forcedNormalizationRate ν u F x t := by
    unfold forcedNormalizationRate normalizationRate
    field_simp
    ring
  rw [hcoeff] at hd
  simpa only [forcedInverseProfile, forcedInversePotential, Pi.sub_apply, mul_comm] using! hd

/-- Second spatial derivative of the forced inverse. -/
theorem forcedInverseProfile_iteratedDeriv_two (ν : ℝ) (u F : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (t₀ x₀ t x : ℝ) :
    iteratedDeriv 2 (forcedInverseProfile ν u F t₀ x₀ t) x =
      (u t x ^ 2 / (4 * ν ^ 2) - deriv (u t) x / (2 * ν)) *
        forcedInverseProfile ν u F t₀ x₀ t x := by
  have hc : Continuous (u t) := hu.continuous.comp (continuous_const.prodMk continuous_id)
  have h0 := slice_x hu (by norm_num) t x
  have h1 := forcedInverseProfile_hasDerivAt_x ν u F t₀ x₀ t x hc
  have he : deriv (forcedInverseProfile ν u F t₀ x₀ t) =
      (fun y => -u t y / (2 * ν) * forcedInverseProfile ν u F t₀ x₀ t y) :=
    funext fun y => (forcedInverseProfile_hasDerivAt_x ν u F t₀ x₀ t y hc).deriv
  have hd : HasDerivAt
      (fun y => -u t y / (2 * ν) * forcedInverseProfile ν u F t₀ x₀ t y)
      ((-deriv (u t) x / (2 * ν)) * forcedInverseProfile ν u F t₀ x₀ t x +
        (-u t x / (2 * ν)) * (-u t x / (2 * ν) * forcedInverseProfile ν u F t₀ x₀ t x)) x :=
    (h0.neg.div_const (2 * ν)).mul h1
  rw [iteratedDeriv_succ, iteratedDeriv_one, he, hd.deriv]
  ring

/-- A regular forced Burgers field reconstructs a positive potential heat profile. -/
theorem forcedInverseProfile_heat (ν : ℝ) (hν : ν ≠ 0) (u F : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (hF : ContDiff ℝ 1 (Function.uncurry F))
    (t₀ x₀ t x : ℝ)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (F t) y) :
    deriv (fun s => forcedInverseProfile ν u F t₀ x₀ s x) t =
      ν * iteratedDeriv 2 (forcedInverseProfile ν u F t₀ x₀ t) x +
        F t x * forcedInverseProfile ν u F t₀ x₀ t x := by
  rw [(forcedInverseProfile_hasDerivAt_t ν hν u F hu hF t₀ x₀ t x hb).deriv,
    forcedInverseProfile_iteratedDeriv_two ν u F hu t₀ x₀ t x]
  unfold forcedNormalizationRate normalizationRate
  field_simp

private theorem integral_logarithmic_derivative (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hp : ∀ x, 0 < f x) (a b : ℝ) :
    (∫ y in a..b, deriv f y / f y) = Real.log (f b) - Real.log (f a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _
    exact (hf.differentiable (by norm_num) y).hasDerivAt.log (ne_of_gt (hp y))
  · exact ((hf.continuous_deriv (by norm_num)).div hf.continuous
      (fun y => ne_of_gt (hp y))).intervalIntegrable a b

/-- For a potential heat profile the normalization rate is its time logarithmic
derivative at the spatial base point. -/
theorem forcedNormalizationRate_classicalTransform (ν : ℝ)
    (φ F : ℝ → ℝ → ℝ) (hφ : ContDiff ℝ 3 (Function.uncurry φ)) (t x : ℝ)
    (hp : φ t x ≠ 0)
    (hh : deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x + F t x * φ t x) :
    forcedNormalizationRate ν (classicalTransform ν φ) F x t =
      deriv (fun s => φ s x) t / φ t x := by
  unfold forcedNormalizationRate normalizationRate
  rw [(classicalTransform_hasDerivAt_x ν φ hφ t x hp).deriv, hh]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  unfold classicalTransform
  field_simp
  ring

/-- The positive potential heat-profile round trip recovers precisely its base-point
normalization. This identifies the multiplicative scale lost by Cole–Hopf. -/
theorem forcedInverseProfile_classicalTransform (ν : ℝ) (hν : ν ≠ 0)
    (φ F : ℝ → ℝ → ℝ) (hφ : ContDiff ℝ 3 (Function.uncurry φ))
    (hp : ∀ t x, 0 < φ t x)
    (hh : ∀ t x, deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x + F t x * φ t x)
    (t₀ x₀ t x : ℝ) :
    forcedInverseProfile ν (classicalTransform ν φ) F t₀ x₀ t x = φ t x / φ t₀ x₀ := by
  have hx : (∫ y in x₀..x, classicalTransform ν φ t y) =
      (-2 * ν) * (Real.log (φ t x) - Real.log (φ t x₀)) := by
    unfold classicalTransform
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact integral_logarithmic_derivative (φ t)
      ((hφ.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)) (hp t) x₀ x
  have ht : (∫ s in t₀..t, forcedNormalizationRate ν (classicalTransform ν φ) F x₀ s) =
      Real.log (φ t x₀) - Real.log (φ t₀ x₀) := by
    have he : forcedNormalizationRate ν (classicalTransform ν φ) F x₀ =
        (fun s => deriv (fun r => φ r x₀) s / φ s x₀) := by
      funext s
      exact forcedNormalizationRate_classicalTransform ν φ F hφ s x₀
        (ne_of_gt (hp s x₀)) (hh s x₀)
    rw [he]
    exact integral_logarithmic_derivative (fun s => φ s x₀)
      ((hφ.comp (contDiff_id.prodMk contDiff_const)).of_le (by norm_num))
      (fun s => hp s x₀) t₀ t
  have he : forcedInversePotential ν (classicalTransform ν φ) F t₀ x₀ t x =
      Real.log (φ t x) - Real.log (φ t₀ x₀) := by
    unfold forcedInversePotential
    rw [ht, hx]
    field_simp
    ring
  rw [forcedInverseProfile, he, Real.exp_sub, Real.exp_log (hp t x), Real.exp_log (hp t₀ x₀)]

/-- Adding a time-only potential rescales the inverse by its anchored exponential.
The reconstructed Burgers field is unchanged. -/
theorem forcedInverseProfile_add_timePotential (ν : ℝ) (u F : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (hF : Continuous (Function.uncurry F))
    (hg : Continuous g) (t₀ x₀ t x : ℝ) :
    forcedInverseProfile ν u (fun s y => F s y + g s) t₀ x₀ t x =
      Real.exp (∫ s in t₀..t, g s) * forcedInverseProfile ν u F t₀ x₀ t x := by
  have hr : forcedNormalizationRate ν u (fun s y => F s y + g s) x₀ =
      (fun s => forcedNormalizationRate ν u F x₀ s + g s) := by
    funext s
    simp [forcedNormalizationRate, add_assoc]
  have he : forcedInversePotential ν u (fun s y => F s y + g s) t₀ x₀ t x =
      forcedInversePotential ν u F t₀ x₀ t x + (∫ s in t₀..t, g s) := by
    unfold forcedInversePotential
    rw [hr, intervalIntegral.integral_add
      ((forcedNormalizationRate_continuous ν u F hu hF x₀).intervalIntegrable t₀ t)
      (hg.intervalIntegrable t₀ t)]
    ring
  simp only [forcedInverseProfile, he, Real.exp_add, mul_comm]

/-- Nonzero constant scaling leaves the classical transform unchanged. -/
theorem classicalTransform_const_mul (ν c : ℝ) (hc : c ≠ 0) (φ : ℝ → ℝ → ℝ) :
    classicalTransform ν (fun t x => c * φ t x) = classicalTransform ν φ := by
  funext t x
  unfold classicalTransform
  rw [deriv_const_mul_field]
  rw [mul_div_mul_left _ _ hc]

/-- Equal transforms for positive profiles solving the same potential equation
imply equal base-point-normalized profiles. -/
theorem potentialProfiles_normalized_eq (ν : ℝ) (hν : ν ≠ 0)
    (φ ψ F : ℝ → ℝ → ℝ) (hφ : ContDiff ℝ 3 (Function.uncurry φ))
    (hψ : ContDiff ℝ 3 (Function.uncurry ψ))
    (hpφ : ∀ t x, 0 < φ t x) (hpψ : ∀ t x, 0 < ψ t x)
    (hhφ : ∀ t x, deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x + F t x * φ t x)
    (hhψ : ∀ t x, deriv (fun s => ψ s x) t = ν * iteratedDeriv 2 (ψ t) x + F t x * ψ t x)
    (he : classicalTransform ν φ = classicalTransform ν ψ) (t₀ x₀ t x : ℝ) :
    φ t x / φ t₀ x₀ = ψ t x / ψ t₀ x₀ := by
  rw [← forcedInverseProfile_classicalTransform ν hν φ F hφ hpφ hhφ t₀ x₀ t x,
    ← forcedInverseProfile_classicalTransform ν hν ψ F hψ hpψ hhψ t₀ x₀ t x, he]

/-- The remaining ambiguity is a unique positive constant, independent of time
and space. Both profiles must solve the same potential equation. -/
theorem potentialProfiles_existsUnique_scale (ν : ℝ) (hν : ν ≠ 0)
    (φ ψ F : ℝ → ℝ → ℝ) (hφ : ContDiff ℝ 3 (Function.uncurry φ))
    (hψ : ContDiff ℝ 3 (Function.uncurry ψ))
    (hpφ : ∀ t x, 0 < φ t x) (hpψ : ∀ t x, 0 < ψ t x)
    (hhφ : ∀ t x, deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x + F t x * φ t x)
    (hhψ : ∀ t x, deriv (fun s => ψ s x) t = ν * iteratedDeriv 2 (ψ t) x + F t x * ψ t x)
    (he : classicalTransform ν φ = classicalTransform ν ψ) :
    ∃! c : ℝ, 0 < c ∧ ∀ t x, φ t x = c * ψ t x := by
  refine ⟨φ 0 0 / ψ 0 0, ⟨div_pos (hpφ 0 0) (hpψ 0 0), ?_⟩, ?_⟩
  · intro t x
    have h := potentialProfiles_normalized_eq ν hν φ ψ F hφ hψ hpφ hpψ hhφ hhψ he 0 0 t x
    have ha := ne_of_gt (hpφ 0 0)
    have hb := ne_of_gt (hpψ 0 0)
    field_simp at h ⊢
    nlinarith
  · intro c hc
    exact (eq_div_iff (ne_of_gt (hpψ 0 0))).mpr (hc.2 0 0).symm

/-- Fixing one common positive base-point value removes the scale ambiguity. -/
theorem potentialProfiles_eq_of_base_eq (ν : ℝ) (hν : ν ≠ 0)
    (φ ψ F : ℝ → ℝ → ℝ) (hφ : ContDiff ℝ 3 (Function.uncurry φ))
    (hψ : ContDiff ℝ 3 (Function.uncurry ψ))
    (hpφ : ∀ t x, 0 < φ t x) (hpψ : ∀ t x, 0 < ψ t x)
    (hhφ : ∀ t x, deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x + F t x * φ t x)
    (hhψ : ∀ t x, deriv (fun s => ψ s x) t = ν * iteratedDeriv 2 (ψ t) x + F t x * ψ t x)
    (he : classicalTransform ν φ = classicalTransform ν ψ) (t₀ x₀ : ℝ)
    (hbase : φ t₀ x₀ = ψ t₀ x₀) : φ = ψ := by
  funext t x
  have h := potentialProfiles_normalized_eq ν hν φ ψ F hφ hψ hpφ hpψ hhφ hhψ he t₀ x₀ t x
  rw [hbase] at h
  exact (div_left_inj' (ne_of_gt (hpψ t₀ x₀))).mp h

end ColeHopf
