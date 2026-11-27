/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.LocalColeHopf
public import MathlibExt.Analysis.PDE.ForcedInverseColeHopf
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Inverse Cole–Hopf on open intervals

On a product of open, order-connected real sets, the anchored forced inverse
constructs a positive potential heat profile from a jointly `C²` forced Burgers
field and jointly `C¹` potential. Both integration anchors lie inside the domain.
The forward transform recovers the field, and the inverse of a positive `C³`
potential heat profile recovers its base-point normalization. Equal transforms
for the same potential determine profiles up to one positive constant on the
product. Values outside the product need not agree or have any regularity.

The formulas are those of Gesztesy and Holden, *The Cole–Hopf and Miura
transformations revisited*, Theorem 3.3 and Remark 3.4,
https://arxiv.org/abs/solv-int/9812025. The proofs localize their construction to
open intervals. Joint regularity is a sufficient, stronger assumption than the
anisotropic regularity in the reference. No limit at an excluded time endpoint,
initial-value existence theorem or boundary condition is asserted.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ContDiff Topology Interval

namespace ColeHopf.OnInterval

variable {I J : Set ℝ}

private theorem continuousOn_slice_x {u : ℝ → ℝ → ℝ}
    (hu : ContinuousOn (Function.uncurry u) (I ×ˢ J)) {t : ℝ} (ht : t ∈ I) :
    ContinuousOn (u t) J :=
  hu.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hy => ⟨ht, hy⟩)

private theorem continuousOn_slice_t {u : ℝ → ℝ → ℝ}
    (hu : ContinuousOn (Function.uncurry u) (I ×ˢ J)) {x : ℝ} (hx : x ∈ J) :
    ContinuousOn (fun t => u t x) I :=
  hu.comp (continuousOn_id.prodMk continuousOn_const) (fun _ ht => ⟨ht, hx⟩)

private theorem integral_hasDerivAt {f : ℝ → ℝ}
    (hJ : IsOpen J) (hc : OrdConnected J) (hf : ContinuousOn f J)
    {a b : ℝ} (ha : a ∈ J) (hb : b ∈ J) :
    HasDerivAt (fun x => ∫ y in a..x, f y) (f b) b :=
  intervalIntegral.integral_hasDerivAt_right
    (hf.mono (hc.uIcc_subset ha hb)).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter hJ hf b hb)
    (hf.continuousAt (hJ.mem_nhds hb))

/-- Differentiation under a finite spatial integral inside an open product. -/
theorem integral_hasDerivAt_time (hI : IsOpen I) (hJ : IsOpen J)
    (hJc : OrdConnected J) {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (I ×ˢ J))
    (a b t : ℝ) (ha : a ∈ J) (hb : b ∈ J) (ht : t ∈ I) :
    HasDerivAt (fun s => ∫ y in a..b, u s y)
      (∫ y in a..b, deriv (fun s => u s y) t) t := by
  have hdt := (contDiffOn_timeDeriv hI hJ hu (by norm_num) (m := 1)
    (by norm_num)).continuousOn
  obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  have hK : IsCompact (Metric.closedBall t ε ×ˢ uIcc a b) :=
    (isCompact_closedBall t ε).prod isCompact_uIcc
  have hseg := hJc.uIcc_subset ha hb
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hdt.mono (fun _ hp => ⟨hsub hp.1, hseg hp.2⟩))
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := u) (F' := fun s y => deriv (fun r => u r y) s)
    (bound := fun _ => M) (s := Metric.ball t ε)
    (Metric.ball_mem_nhds t hε) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hI.mem_nhds ht] with s hs
    exact ((continuousOn_slice_x hu.continuousOn hs).mono
      (uIoc_subset_uIcc.trans hseg)).aestronglyMeasurable measurableSet_uIoc
  · exact ((continuousOn_slice_x hu.continuousOn ht).mono hseg).intervalIntegrable
  · exact ((continuousOn_slice_x hdt ht).mono
      (uIoc_subset_uIcc.trans hseg)).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards with y hy s hs
    exact hM (s, y) ⟨Metric.ball_subset_closedBall hs, uIoc_subset_uIcc hy⟩
  · exact continuous_const.intervalIntegrable a b
  · filter_upwards with y hy s hs
    exact time_derivative hI hJ hu (by norm_num) s y
      (hsub (Metric.ball_subset_closedBall hs)) (hseg (uIoc_subset_uIcc hy))

/-- Continuity of the normalization rate only requires regularity inside the domain. -/
theorem forcedNormalizationRate_continuousOn (hI : IsOpen I) (hJ : IsOpen J)
    (ν : ℝ) (u F : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (I ×ˢ J))
    (hF : ContinuousOn (Function.uncurry F) (I ×ˢ J)) (x₀ : ℝ) (hx₀ : x₀ ∈ J) :
    ContinuousOn (forcedNormalizationRate ν u F x₀) I := by
  have hx := continuousOn_slice_t
    (contDiffOn_spaceDeriv hI hJ hu (by norm_num) (m := 1) (by norm_num)).continuousOn hx₀
  have hc := continuousOn_slice_t hu.continuousOn hx₀
  exact (((hc.pow 2).div_const (4 * ν)).sub (hx.div_const 2)).add
    (continuousOn_slice_t hF hx₀)

/-- Spatial differentiation uses continuity only on the spatial interval. -/
theorem forcedInverseProfile_hasDerivAt_x (hJ : IsOpen J) (hJc : OrdConnected J)
    (ν : ℝ) (u F : ℝ → ℝ → ℝ) (t₀ x₀ t x : ℝ)
    (hx₀ : x₀ ∈ J) (hx : x ∈ J) (hu : ContinuousOn (u t) J) :
    HasDerivAt (forcedInverseProfile ν u F t₀ x₀ t)
      (-u t x / (2 * ν) * forcedInverseProfile ν u F t₀ x₀ t x) x := by
  have hd := ((integral_hasDerivAt hJ hJc hu hx₀ hx).div_const (2 * ν)).const_sub
    (∫ s in t₀..t, forcedNormalizationRate ν u F x₀ s)
  change HasDerivAt (fun y => Real.exp (forcedInversePotential ν u F t₀ x₀ t y)) _ x
  simpa only [forcedInverseProfile, forcedInversePotential, neg_div, mul_comm] using! hd.exp

/-- The forward transform recovers the field at each interior spatial point. -/
theorem classicalTransform_forcedInverseProfile (hJ : IsOpen J) (hJc : OrdConnected J)
    (ν : ℝ) (hν : ν ≠ 0) (u F : ℝ → ℝ → ℝ) (t₀ x₀ t x : ℝ)
    (hx₀ : x₀ ∈ J) (hx : x ∈ J) (hu : ContinuousOn (u t) J) :
    classicalTransform ν (forcedInverseProfile ν u F t₀ x₀) t x = u t x := by
  unfold classicalTransform
  rw [(forcedInverseProfile_hasDerivAt_x hJ hJc ν u F t₀ x₀ t x hx₀ hx hu).deriv]
  have hp := ne_of_gt (forcedInverseProfile_pos ν u F t₀ x₀ t x)
  field_simp

/-- Integrated forced Burgers equation, including the potential in the flux. -/
theorem integral_timeDeriv_of_forced_burgers (hI : IsOpen I) (hJ : IsOpen J)
    (hJc : OrdConnected J) (ν : ℝ) (u F : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (I ×ˢ J))
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) (I ×ˢ J))
    (t a b : ℝ) (ht : t ∈ I) (ha : a ∈ J) (hbJ : b ∈ J)
    (hb : ∀ y ∈ J, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (F t) y) :
    (∫ y in a..b, deriv (fun s => u s y) t) =
      (ν * deriv (u t) b - u t b ^ 2 / 2 - 2 * ν * F t b) -
      (ν * deriv (u t) a - u t a ^ 2 / 2 - 2 * ν * F t a) := by
  have hx := contDiffOn_spaceDeriv hI hJ hu (by norm_num) (m := 1) (by norm_num)
  have hdt := (contDiffOn_timeDeriv hI hJ hu (by norm_num) (m := 1) (by norm_num)).continuousOn
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    have hyJ := hJc.uIcc_subset ha hbJ hy
    have h0 := space_derivative hI hJ hu (by norm_num) t y ht hyJ
    have h1 := space_derivative hI hJ hx (by norm_num) t y ht hyJ
    have h2 := space_derivative hI hJ hF (by norm_num) t y ht hyJ
    convert ((h1.const_mul ν).sub ((h0.pow 2).div_const 2)).sub
      (h2.const_mul (2 * ν)) using 1
    have he := hb y hyJ
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at he
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    linarith
  · exact ((continuousOn_slice_x hdt ht).mono (hJc.uIcc_subset ha hbJ)).intervalIntegrable

/-- The forced normalization gives the actual time derivative of the inverse. -/
theorem forcedInverseProfile_hasDerivAt_t (hI : IsOpen I) (hJ : IsOpen J)
    (hIc : OrdConnected I) (hJc : OrdConnected J) (ν : ℝ) (hν : ν ≠ 0)
    (u F : ℝ → ℝ → ℝ) (hu : ContDiffOn ℝ 2 (Function.uncurry u) (I ×ˢ J))
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) (I ×ˢ J)) (t₀ x₀ t x : ℝ)
    (ht₀ : t₀ ∈ I) (hx₀ : x₀ ∈ J) (ht : t ∈ I) (hxJ : x ∈ J)
    (hb : ∀ y ∈ J, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (F t) y) :
    HasDerivAt (fun s => forcedInverseProfile ν u F t₀ x₀ s x)
      (forcedNormalizationRate ν u F x t * forcedInverseProfile ν u F t₀ x₀ t x) t := by
  have hc := forcedNormalizationRate_continuousOn hI hJ ν u F hu hF.continuousOn x₀ hx₀
  have hA := integral_hasDerivAt hI hIc hc ht₀ ht
  have hP := (integral_hasDerivAt_time hI hJ hJc hu x₀ x t hx₀ hxJ ht).div_const (2 * ν)
  have hd := (hA.sub hP).exp
  rw [integral_timeDeriv_of_forced_burgers hI hJ hJc ν u F hu hF t x₀ x ht hx₀ hxJ hb] at hd
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
theorem forcedInverseProfile_iteratedDeriv_two (hI : IsOpen I) (hJ : IsOpen J)
    (hJc : OrdConnected J) (ν : ℝ) (u F : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (I ×ˢ J)) (t₀ x₀ t x : ℝ)
    (hx₀ : x₀ ∈ J) (ht : t ∈ I) (hxJ : x ∈ J) :
    iteratedDeriv 2 (forcedInverseProfile ν u F t₀ x₀ t) x =
      (u t x ^ 2 / (4 * ν ^ 2) - deriv (u t) x / (2 * ν)) *
        forcedInverseProfile ν u F t₀ x₀ t x := by
  have hc : ContinuousOn (u t) J := continuousOn_slice_x hu.continuousOn ht
  have h0 := space_derivative hI hJ hu (by norm_num) t x ht hxJ
  have h1 := forcedInverseProfile_hasDerivAt_x hJ hJc ν u F t₀ x₀ t x hx₀ hxJ hc
  have he : deriv (forcedInverseProfile ν u F t₀ x₀ t) =ᶠ[𝓝 x]
      (fun y => -u t y / (2 * ν) * forcedInverseProfile ν u F t₀ x₀ t y) := by
    filter_upwards [hJ.mem_nhds hxJ] with y hy
    exact (forcedInverseProfile_hasDerivAt_x hJ hJc ν u F t₀ x₀ t y hx₀ hy hc).deriv
  have hd : HasDerivAt
      (fun y => -u t y / (2 * ν) * forcedInverseProfile ν u F t₀ x₀ t y)
      ((-deriv (u t) x / (2 * ν)) * forcedInverseProfile ν u F t₀ x₀ t x +
        (-u t x / (2 * ν)) * (-u t x / (2 * ν) * forcedInverseProfile ν u F t₀ x₀ t x)) x :=
    (h0.neg.div_const (2 * ν)).mul h1
  rw [iteratedDeriv_succ, iteratedDeriv_one, (hd.congr_of_eventuallyEq he).deriv]
  ring

/-- A regular forced Burgers field reconstructs a positive potential heat profile. -/
theorem forcedInverseProfile_heat (hI : IsOpen I) (hJ : IsOpen J)
    (hIc : OrdConnected I) (hJc : OrdConnected J) (ν : ℝ) (hν : ν ≠ 0) (u F : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (I ×ˢ J))
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) (I ×ˢ J))
    (t₀ x₀ t x : ℝ)
    (ht₀ : t₀ ∈ I) (hx₀ : x₀ ∈ J) (ht : t ∈ I) (hxJ : x ∈ J)
    (hb : ∀ y ∈ J, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (F t) y) :
    deriv (fun s => forcedInverseProfile ν u F t₀ x₀ s x) t =
      ν * iteratedDeriv 2 (forcedInverseProfile ν u F t₀ x₀ t) x +
        F t x * forcedInverseProfile ν u F t₀ x₀ t x := by
  rw [(forcedInverseProfile_hasDerivAt_t hI hJ hIc hJc ν hν u F hu hF t₀ x₀ t x
      ht₀ hx₀ ht hxJ hb).deriv,
    forcedInverseProfile_iteratedDeriv_two hI hJ hJc ν u F hu t₀ x₀ t x hx₀ ht hxJ]
  unfold forcedNormalizationRate normalizationRate
  field_simp

private theorem integral_logarithmic_derivative (hJ : IsOpen J) (hJc : OrdConnected J)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f J) (hp : ∀ x ∈ J, 0 < f x)
    (a b : ℝ) (ha : a ∈ J) (hb : b ∈ J) :
    (∫ y in a..b, deriv f y / f y) = Real.log (f b) - Real.log (f a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    have hyJ := hJc.uIcc_subset ha hb hy
    exact ((hf.contDiffAt (hJ.mem_nhds hyJ)).differentiableAt (by norm_num)).hasDerivAt.log
      (ne_of_gt (hp y hyJ))
  · exact (((hf.continuousOn_deriv_of_isOpen hJ (by norm_num)).div hf.continuousOn
      (fun y hy => ne_of_gt (hp y hy))).mono (hJc.uIcc_subset ha hb)).intervalIntegrable

/-- The potential heat equation identifies the normalization rate pointwise. -/
theorem forcedNormalizationRate_classicalTransform (hI : IsOpen I) (hJ : IsOpen J)
    (ν : ℝ) (φ F : ℝ → ℝ → ℝ) (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (t x : ℝ) (ht : t ∈ I) (hx : x ∈ J) (hp : φ t x ≠ 0)
    (hh : deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x + F t x * φ t x) :
    forcedNormalizationRate ν (classicalTransform ν φ) F x t =
      deriv (fun s => φ s x) t / φ t x := by
  unfold forcedNormalizationRate normalizationRate
  rw [(classicalTransform_hasDerivAt_x hI hJ ν φ hφ t x ht hx hp).deriv, hh]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  unfold classicalTransform
  field_simp
  ring

/-- The inverse of a positive potential heat profile recovers its normalization
throughout the connected product, with no assumptions at excluded endpoints. -/
theorem forcedInverseProfile_classicalTransform (hI : IsOpen I) (hJ : IsOpen J)
    (hIc : OrdConnected I) (hJc : OrdConnected J) (ν : ℝ) (hν : ν ≠ 0)
    (φ F : ℝ → ℝ → ℝ) (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (hp : ∀ t ∈ I, ∀ x ∈ J, 0 < φ t x)
    (hh : ∀ t ∈ I, ∀ x ∈ J,
      deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x + F t x * φ t x)
    (t₀ x₀ t x : ℝ) (ht₀ : t₀ ∈ I) (hx₀ : x₀ ∈ J) (ht : t ∈ I) (hx : x ∈ J) :
    forcedInverseProfile ν (classicalTransform ν φ) F t₀ x₀ t x = φ t x / φ t₀ x₀ := by
  have hspace : (∫ y in x₀..x, classicalTransform ν φ t y) =
      (-2 * ν) * (Real.log (φ t x) - Real.log (φ t x₀)) := by
    unfold classicalTransform
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact integral_logarithmic_derivative hJ hJc (φ t)
      ((hφ.comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun _ hy => ⟨ht, hy⟩)).of_le (by norm_num)) (hp t ht) x₀ x hx₀ hx
  have htime : (∫ s in t₀..t, forcedNormalizationRate ν (classicalTransform ν φ) F x₀ s) =
      Real.log (φ t x₀) - Real.log (φ t₀ x₀) := by
    calc
      _ = ∫ s in t₀..t, deriv (fun r => φ r x₀) s / φ s x₀ := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hsI := hIc.uIcc_subset ht₀ ht hs
        exact forcedNormalizationRate_classicalTransform hI hJ ν φ F hφ s x₀ hsI hx₀
          (ne_of_gt (hp s hsI x₀ hx₀)) (hh s hsI x₀ hx₀)
      _ = _ := integral_logarithmic_derivative hI hIc (fun s => φ s x₀)
        ((hφ.comp (contDiffOn_id.prodMk contDiffOn_const)
          (fun _ hs => ⟨hs, hx₀⟩)).of_le (by norm_num))
        (fun s hs => hp s hs x₀ hx₀) t₀ t ht₀ ht
  have he : forcedInversePotential ν (classicalTransform ν φ) F t₀ x₀ t x =
      Real.log (φ t x) - Real.log (φ t₀ x₀) := by
    unfold forcedInversePotential
    rw [htime, hspace]
    field_simp
    ring
  rw [forcedInverseProfile, he, Real.exp_sub, Real.exp_log (hp t ht x hx),
    Real.exp_log (hp t₀ ht₀ x₀ hx₀)]

/-- Changing the field or potential outside the interval product has no effect on
its anchored inverse inside the product. No regularity is needed for this identity. -/
theorem forcedInverseProfile_congr (hJ : IsOpen J)
    (hIc : OrdConnected I) (hJc : OrdConnected J) (ν : ℝ) (u v F G : ℝ → ℝ → ℝ)
    (hu : EqOn (Function.uncurry u) (Function.uncurry v) (I ×ˢ J))
    (hF : EqOn (Function.uncurry F) (Function.uncurry G) (I ×ˢ J))
    (t₀ x₀ t x : ℝ) (ht₀ : t₀ ∈ I) (hx₀ : x₀ ∈ J) (ht : t ∈ I) (hx : x ∈ J) :
    forcedInverseProfile ν u F t₀ x₀ t x = forcedInverseProfile ν v G t₀ x₀ t x := by
  have hr : (∫ s in t₀..t, forcedNormalizationRate ν u F x₀ s) =
      ∫ s in t₀..t, forcedNormalizationRate ν v G x₀ s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI := hIc.uIcc_subset ht₀ ht hs
    have he : u s =ᶠ[𝓝 x₀] v s := by
      filter_upwards [hJ.mem_nhds hx₀] with y hy
      exact hu (x := (s, y)) ⟨hsI, hy⟩
    unfold forcedNormalizationRate normalizationRate
    rw [he.deriv_eq, show u s x₀ = v s x₀ from hu (x := (s, x₀)) ⟨hsI, hx₀⟩,
      show F s x₀ = G s x₀ from hF (x := (s, x₀)) ⟨hsI, hx₀⟩]
  have hs : (∫ y in x₀..x, u t y) = ∫ y in x₀..x, v t y :=
    intervalIntegral.integral_congr (fun y hy => hu (x := (t, y)) ⟨ht, hJc.uIcc_subset hx₀ hx hy⟩)
  simp only [forcedInverseProfile, forcedInversePotential, hr, hs]

/-- Equal transforms for the same potential identify the normalized profiles on
this connected domain, even if the transforms differ elsewhere. -/
theorem potentialProfiles_normalized_eq (hI : IsOpen I) (hJ : IsOpen J)
    (hIc : OrdConnected I) (hJc : OrdConnected J) (ν : ℝ) (hν : ν ≠ 0)
    (φ ψ F : ℝ → ℝ → ℝ) (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (hψ : ContDiffOn ℝ 3 (Function.uncurry ψ) (I ×ˢ J))
    (hpφ : ∀ t ∈ I, ∀ x ∈ J, 0 < φ t x) (hpψ : ∀ t ∈ I, ∀ x ∈ J, 0 < ψ t x)
    (hhφ : ∀ t ∈ I, ∀ x ∈ J,
      deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x + F t x * φ t x)
    (hhψ : ∀ t ∈ I, ∀ x ∈ J,
      deriv (fun s => ψ s x) t = ν * iteratedDeriv 2 (ψ t) x + F t x * ψ t x)
    (he : EqOn (Function.uncurry (classicalTransform ν φ))
      (Function.uncurry (classicalTransform ν ψ)) (I ×ˢ J))
    (t₀ x₀ t x : ℝ) (ht₀ : t₀ ∈ I) (hx₀ : x₀ ∈ J) (ht : t ∈ I) (hx : x ∈ J) :
    φ t x / φ t₀ x₀ = ψ t x / ψ t₀ x₀ := by
  rw [← forcedInverseProfile_classicalTransform hI hJ hIc hJc ν hν φ F hφ hpφ hhφ
      t₀ x₀ t x ht₀ hx₀ ht hx,
    ← forcedInverseProfile_classicalTransform hI hJ hIc hJc ν hν ψ F hψ hpψ hhψ
      t₀ x₀ t x ht₀ hx₀ ht hx]
  exact forcedInverseProfile_congr hJ hIc hJc ν _ _ F F he (fun _ _ => rfl)
    t₀ x₀ t x ht₀ hx₀ ht hx

/-- On the connected product, the remaining ambiguity is one unique positive
constant. The interior anchor supplies the required nonemptiness. -/
theorem potentialProfiles_existsUnique_scale (hI : IsOpen I) (hJ : IsOpen J)
    (hIc : OrdConnected I) (hJc : OrdConnected J) (ν : ℝ) (hν : ν ≠ 0)
    (φ ψ F : ℝ → ℝ → ℝ) (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (hψ : ContDiffOn ℝ 3 (Function.uncurry ψ) (I ×ˢ J))
    (hpφ : ∀ t ∈ I, ∀ x ∈ J, 0 < φ t x) (hpψ : ∀ t ∈ I, ∀ x ∈ J, 0 < ψ t x)
    (hhφ : ∀ t ∈ I, ∀ x ∈ J,
      deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x + F t x * φ t x)
    (hhψ : ∀ t ∈ I, ∀ x ∈ J,
      deriv (fun s => ψ s x) t = ν * iteratedDeriv 2 (ψ t) x + F t x * ψ t x)
    (he : EqOn (Function.uncurry (classicalTransform ν φ))
      (Function.uncurry (classicalTransform ν ψ)) (I ×ˢ J))
    (t₀ x₀ : ℝ) (ht₀ : t₀ ∈ I) (hx₀ : x₀ ∈ J) :
    ∃! c : ℝ, 0 < c ∧ ∀ t ∈ I, ∀ x ∈ J, φ t x = c * ψ t x := by
  refine ⟨φ t₀ x₀ / ψ t₀ x₀, ⟨div_pos (hpφ t₀ ht₀ x₀ hx₀) (hpψ t₀ ht₀ x₀ hx₀), ?_⟩, ?_⟩
  · intro t ht x hx
    have h := potentialProfiles_normalized_eq hI hJ hIc hJc ν hν φ ψ F
      hφ hψ hpφ hpψ hhφ hhψ he t₀ x₀ t x ht₀ hx₀ ht hx
    have ha := ne_of_gt (hpφ t₀ ht₀ x₀ hx₀)
    have hb := ne_of_gt (hpψ t₀ ht₀ x₀ hx₀)
    field_simp at h ⊢
    nlinarith
  · intro c hc
    exact (eq_div_iff (ne_of_gt (hpψ t₀ ht₀ x₀ hx₀))).mpr (hc.2 t₀ ht₀ x₀ hx₀).symm

/-- A common base value fixes the profile on the domain, without asserting equality
outside it. -/
theorem potentialProfiles_eqOn_of_base_eq (hI : IsOpen I) (hJ : IsOpen J)
    (hIc : OrdConnected I) (hJc : OrdConnected J) (ν : ℝ) (hν : ν ≠ 0)
    (φ ψ F : ℝ → ℝ → ℝ) (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (hψ : ContDiffOn ℝ 3 (Function.uncurry ψ) (I ×ˢ J))
    (hpφ : ∀ t ∈ I, ∀ x ∈ J, 0 < φ t x) (hpψ : ∀ t ∈ I, ∀ x ∈ J, 0 < ψ t x)
    (hhφ : ∀ t ∈ I, ∀ x ∈ J,
      deriv (fun s => φ s x) t = ν * iteratedDeriv 2 (φ t) x + F t x * φ t x)
    (hhψ : ∀ t ∈ I, ∀ x ∈ J,
      deriv (fun s => ψ s x) t = ν * iteratedDeriv 2 (ψ t) x + F t x * ψ t x)
    (he : EqOn (Function.uncurry (classicalTransform ν φ))
      (Function.uncurry (classicalTransform ν ψ)) (I ×ˢ J))
    (t₀ x₀ : ℝ) (ht₀ : t₀ ∈ I) (hx₀ : x₀ ∈ J) (hbase : φ t₀ x₀ = ψ t₀ x₀) :
    EqOn (Function.uncurry φ) (Function.uncurry ψ) (I ×ˢ J) := by
  intro p hp
  have h := potentialProfiles_normalized_eq hI hJ hIc hJc ν hν φ ψ F
    hφ hψ hpφ hpψ hhφ hhψ he t₀ x₀ p.1 p.2 ht₀ hx₀ hp.1 hp.2
  rw [hbase] at h
  exact (div_left_inj' (ne_of_gt (hpψ t₀ ht₀ x₀ hx₀))).mp h

end ColeHopf.OnInterval
