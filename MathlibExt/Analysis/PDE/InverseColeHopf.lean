/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.ClassicalColeHopf
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
# Normalized inverse classical Cole–Hopf transformation

For a Burgers field `u` and base point `(t₀,x₀)`, construct
`φ(t,x) = exp(∫ t₀..t, [u(s,x₀)²/(4ν) - uₓ(s,x₀)/2]
  - (∫ x₀..x, u(t,y))/(2ν))`.
The time integral is essential: the spatial exponential alone generally has a
nonzero heat residual. The construction is positive and normalized to one at
the base point. Under the stated regularity and Burgers equation it solves heat
and its classical Cole–Hopf transform recovers `u`.

Global joint `C²` regularity of `u` is a sufficient assumption on the real plane;
no initial-value existence or growth-at-infinity theorem is asserted. All
integrals are finite oriented interval integrals. Inversion requires `ν ≠ 0`;
positive viscosity is the standard viscous case.

## References

Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*,
Theorem 3.3(i) and Remark 3.4, https://arxiv.org/abs/solv-int/9812025.
The explicit rate above is the negative normalized heat residual of the
uncorrected spatial exponential at `x₀`.
The source's positive-time, positive-viscosity result is specialized to zero
potential here; the algebra also applies at negative nonzero viscosity.
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

/-- Logarithmic time-normalization rate at a fixed spatial base point. -/
noncomputable def normalizationRate (ν : ℝ) (u : ℝ → ℝ → ℝ) (x₀ t : ℝ) : ℝ :=
  u t x₀ ^ 2 / (4 * ν) - deriv (u t) x₀ / 2

/-- Normalized logarithmic inverse profile, using finite oriented integrals. -/
noncomputable def inversePotential (ν : ℝ) (u : ℝ → ℝ → ℝ) (t₀ x₀ t x : ℝ) : ℝ :=
  (∫ s in t₀..t, normalizationRate ν u x₀ s) - (∫ y in x₀..x, u t y) / (2 * ν)

/-- Positive inverse Cole–Hopf profile normalized at a chosen time-space point. -/
noncomputable def inverseProfile (ν : ℝ) (u : ℝ → ℝ → ℝ) (t₀ x₀ t x : ℝ) : ℝ :=
  Real.exp (inversePotential ν u t₀ x₀ t x)

/-- Positivity is built into the exponential construction. -/
theorem inverseProfile_pos (ν : ℝ) (u : ℝ → ℝ → ℝ) (t₀ x₀ t x : ℝ) :
    0 < inverseProfile ν u t₀ x₀ t x := Real.exp_pos _

/-- The two anchored integrals give value one at the base point. -/
@[simp] theorem inverseProfile_base (ν : ℝ) (u : ℝ → ℝ → ℝ) (t₀ x₀ : ℝ) :
    inverseProfile ν u t₀ x₀ t₀ x₀ = 1 := by
  simp [inverseProfile, inversePotential]

/-- At the initial time the profile is the anchored spatial exponential. -/
theorem inverseProfile_initial (ν : ℝ) (u : ℝ → ℝ → ℝ) (t₀ x₀ x : ℝ) :
    inverseProfile ν u t₀ x₀ t₀ x = Real.exp (-(∫ y in x₀..x, u t₀ y) / (2 * ν)) := by
  simp [inverseProfile, inversePotential, neg_div]

/-- The normalization rate is continuous for a jointly `C²` field. -/
theorem normalizationRate_continuous (ν : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (x₀ : ℝ) :
    Continuous (normalizationRate ν u x₀) := by
  have hx := (contDiff_dx hu (by norm_num) (m := 1) (by norm_num)).continuous
  exact ((hu.continuous.comp (continuous_id.prodMk continuous_const)).pow 2 |>.div_const
    (4 * ν)).sub ((hx.comp (continuous_id.prodMk continuous_const)).div_const 2)

/-- Spatial derivative of the constructed profile; no PDE premise is needed. -/
theorem inverseProfile_hasDerivAt_x (ν : ℝ) (u : ℝ → ℝ → ℝ)
    (t₀ x₀ t x : ℝ) (hu : Continuous (u t)) :
    HasDerivAt (inverseProfile ν u t₀ x₀ t)
      (-u t x / (2 * ν) * inverseProfile ν u t₀ x₀ t x) x := by
  have hd := ((hu.integral_hasStrictDerivAt x₀ x).hasDerivAt.div_const (2 * ν)).const_sub
    (∫ s in t₀..t, normalizationRate ν u x₀ s)
  change HasDerivAt (fun y => Real.exp (inversePotential ν u t₀ x₀ t y)) _ x
  simpa only [inverseProfile, inversePotential, neg_div, mul_comm] using! hd.exp

/-- Applying classical Cole–Hopf to the inverse recovers the original field. -/
theorem classicalTransform_inverseProfile (ν : ℝ) (hν : ν ≠ 0) (u : ℝ → ℝ → ℝ)
    (t₀ x₀ t x : ℝ) (hu : Continuous (u t)) :
    classicalTransform ν (inverseProfile ν u t₀ x₀) t x = u t x := by
  unfold classicalTransform
  rw [(inverseProfile_hasDerivAt_x ν u t₀ x₀ t x hu).deriv]
  have hp := ne_of_gt (inverseProfile_pos ν u t₀ x₀ t x)
  field_simp

/-- Integrated Burgers conservation law, used to determine the time correction. -/
theorem integral_timeDeriv_of_burgers (ν : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (t a b : ℝ)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y) :
    (∫ y in a..b, deriv (fun s => u s y) t) =
      (ν * deriv (u t) b - u t b ^ 2 / 2) -
      (ν * deriv (u t) a - u t a ^ 2 / 2) := by
  have hx := contDiff_dx hu (by norm_num) (m := 1) (by norm_num)
  have hdt := (contDiff_dt hu (by norm_num) (m := 1) (by norm_num)).continuous
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _
    have h0 := slice_x hu (by norm_num) t y
    have h1 := slice_x hx (by norm_num) t y
    convert (h1.const_mul ν).sub ((h0.pow 2).div_const 2) using 1
    have he := hb y
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at he
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    linarith
  · exact (hdt.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b

/-- The time normalization turns the integrated Burgers equation into the
logarithmic heat evolution of the positive profile. -/
theorem inverseProfile_hasDerivAt_t (ν : ℝ) (hν : ν ≠ 0) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (t₀ x₀ t x : ℝ)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y) :
    HasDerivAt (fun s => inverseProfile ν u t₀ x₀ s x)
      (normalizationRate ν u x t * inverseProfile ν u t₀ x₀ t x) t := by
  have hA := ((normalizationRate_continuous ν u hu x₀).integral_hasStrictDerivAt t₀ t).hasDerivAt
  have hP := (integral_hasDerivAt_time hu x₀ x t).div_const (2 * ν)
  have hd := (hA.sub hP).exp
  rw [integral_timeDeriv_of_burgers ν u hu t x₀ x hb] at hd
  have hcoeff : normalizationRate ν u x₀ t -
      ((ν * deriv (u t) x - u t x ^ 2 / 2) -
        (ν * deriv (u t) x₀ - u t x₀ ^ 2 / 2)) / (2 * ν) =
      normalizationRate ν u x t := by
    unfold normalizationRate
    field_simp
    ring
  rw [hcoeff] at hd
  simpa only [inverseProfile, inversePotential, Pi.sub_apply, mul_comm] using! hd

/-- Second spatial derivative of the inverse profile. -/
theorem inverseProfile_iteratedDeriv_two (ν : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (t₀ x₀ t x : ℝ) :
    iteratedDeriv 2 (inverseProfile ν u t₀ x₀ t) x =
      (u t x ^ 2 / (4 * ν ^ 2) - deriv (u t) x / (2 * ν)) *
        inverseProfile ν u t₀ x₀ t x := by
  have hc : Continuous (u t) := hu.continuous.comp (continuous_const.prodMk continuous_id)
  have h0 := slice_x hu (by norm_num) t x
  have h1 := inverseProfile_hasDerivAt_x ν u t₀ x₀ t x hc
  have he : deriv (inverseProfile ν u t₀ x₀ t) =
      (fun y => -u t y / (2 * ν) * inverseProfile ν u t₀ x₀ t y) :=
    funext fun y => (inverseProfile_hasDerivAt_x ν u t₀ x₀ t y hc).deriv
  have hd : HasDerivAt
      (fun y => -u t y / (2 * ν) * inverseProfile ν u t₀ x₀ t y)
      ((-deriv (u t) x / (2 * ν)) * inverseProfile ν u t₀ x₀ t x +
        (-u t x / (2 * ν)) * (-u t x / (2 * ν) * inverseProfile ν u t₀ x₀ t x)) x :=
    (h0.neg.div_const (2 * ν)).mul h1
  rw [iteratedDeriv_succ, iteratedDeriv_one, he, hd.deriv]
  ring

/-- A jointly `C²` Burgers field gives an actual positive classical heat solution.
The Burgers equation is needed at the given time throughout space. -/
theorem inverseProfile_heat (ν : ℝ) (hν : ν ≠ 0) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (t₀ x₀ t x : ℝ)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y) :
    deriv (fun s => inverseProfile ν u t₀ x₀ s x) t =
      ν * iteratedDeriv 2 (inverseProfile ν u t₀ x₀ t) x := by
  rw [(inverseProfile_hasDerivAt_t ν hν u hu t₀ x₀ t x hb).deriv,
    inverseProfile_iteratedDeriv_two ν u hu t₀ x₀ t x]
  unfold normalizationRate
  field_simp

private theorem integral_logarithmic_derivative (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hp : ∀ x, 0 < f x) (a b : ℝ) :
    (∫ y in a..b, deriv f y / f y) = Real.log (f b) - Real.log (f a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _
    exact (hf.differentiable (by norm_num) y).hasDerivAt.log (ne_of_gt (hp y))
  · exact ((hf.continuous_deriv (by norm_num)).div hf.continuous
      (fun y => ne_of_gt (hp y))).intervalIntegrable a b

/-- For a positive heat profile the normalization rate is its time logarithmic
derivative at the spatial base point. -/
theorem normalizationRate_classicalTransform (ν : ℝ) (hν : ν ≠ 0)
    (φ : ℝ → ℝ → ℝ) (hφ : ContDiff ℝ 3 (Function.uncurry φ)) (t x : ℝ)
    (hp : φ t x ≠ 0)
    (hh : deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x) :
    normalizationRate ν (classicalTransform ν φ) x t =
      deriv (fun s => φ s x) t / φ t x := by
  unfold normalizationRate
  rw [(classicalTransform_hasDerivAt_x ν φ hφ t x hp).deriv, hh]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  unfold classicalTransform
  field_simp
  ring

/-- The positive heat-profile round trip recovers precisely its base-point
normalization. This identifies the multiplicative scale lost by Cole–Hopf. -/
theorem inverseProfile_classicalTransform (ν : ℝ) (hν : ν ≠ 0)
    (φ : ℝ → ℝ → ℝ) (hφ : ContDiff ℝ 3 (Function.uncurry φ))
    (hp : ∀ t x, 0 < φ t x)
    (hh : ∀ t x, deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x)
    (t₀ x₀ t x : ℝ) :
    inverseProfile ν (classicalTransform ν φ) t₀ x₀ t x = φ t x / φ t₀ x₀ := by
  have hx : (∫ y in x₀..x, classicalTransform ν φ t y) =
      (-2 * ν) * (Real.log (φ t x) - Real.log (φ t x₀)) := by
    unfold classicalTransform
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact integral_logarithmic_derivative (φ t)
      ((hφ.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)) (hp t) x₀ x
  have ht : (∫ s in t₀..t, normalizationRate ν (classicalTransform ν φ) x₀ s) =
      Real.log (φ t x₀) - Real.log (φ t₀ x₀) := by
    have he : normalizationRate ν (classicalTransform ν φ) x₀ =
        (fun s => deriv (fun r => φ r x₀) s / φ s x₀) := by
      funext s
      exact normalizationRate_classicalTransform ν hν φ hφ s x₀
        (ne_of_gt (hp s x₀)) (hh s x₀)
    rw [he]
    exact integral_logarithmic_derivative (fun s => φ s x₀)
      ((hφ.comp (contDiff_id.prodMk contDiff_const)).of_le (by norm_num))
      (fun s => hp s x₀) t₀ t
  have he : inversePotential ν (classicalTransform ν φ) t₀ x₀ t x =
      Real.log (φ t x) - Real.log (φ t₀ x₀) := by
    unfold inversePotential
    rw [ht, hx]
    field_simp
    ring
  rw [inverseProfile, he, Real.exp_sub, Real.exp_log (hp t x), Real.exp_log (hp t₀ x₀)]

end ColeHopf
