/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
open MeasureTheory Complex Set Filter Metric
open scoped Topology

namespace MathlibExt.Analysis.Complex.FatouRadialWanted

/-!
# Fatou radial limit theorem for `H∞` on the disc
-/

/-- N1: bounded holomorphic on disc has Lipschitz primitive (Morera + extension). -/
private theorem exists_lipschitz_primitive_on_unit_disc
    (f : ℂ → ℂ) {M : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ M) :
    ∃ G : ℂ → ℂ, ∃ K : NNReal, LipschitzWith K G ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt G (f z)
        z := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  have hconv : Convex ℝ (Metric.ball (0 : ℂ) 1) := convex_ball _ _
  have hderiv : ∀ x ∈ Metric.ball (0 : ℂ) 1,
      HasDerivWithinAt F (f x) (Metric.ball (0 : ℂ) 1) x :=
    fun x hx => (hF x hx).hasDerivWithinAt
  have hbound : ∀ x ∈ Metric.ball (0 : ℂ) 1, ‖f x‖₊ ≤ Real.toNNReal M := by
    intro x hx
    exact NNReal.le_toNNReal_of_coe_le (hM x hx)
  have hlip : LipschitzOnWith (Real.toNNReal M) F (Metric.ball (0 : ℂ) 1) :=
    hconv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le hderiv hbound
  obtain ⟨G, hGlip, hGeq⟩ := hlip.extend_finite_dimension
  refine ⟨G, _, hGlip, ?_⟩
  intro z hz
  have hmem : Metric.ball (0 : ℂ) 1 ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  have hev : G =ᶠ[𝓝 z] F := Filter.eventuallyEq_of_mem hmem (fun w hw => (hGeq hw).symm)
  exact (hF z hz).congr_of_eventuallyEq hev

/-- N2: boundary trace of Lipschitz map is a.e. differentiable (1-D Rademacher). -/
private theorem ae_differentiableAt_circle_comp {K : NNReal} {G : ℂ → ℂ} (hG : LipschitzWith K G) :
    ∀ᵐ θ : ℝ, DifferentiableAt ℝ (fun t : ℝ => G (Complex.exp ((t : ℂ) * Complex.I))) θ := by
  have he : (fun t : ℝ => G (Complex.exp ((t : ℂ) * Complex.I))) = G ∘ (circleMap 0 1) := by
    funext t
    simp [circleMap_zero]
  rw [he]
  exact (hG.comp (lipschitzWith_circleMap 0 1)).ae_differentiableAt_real

/-- N8: Lorentzian mass bound on [-π, π]. -/
private theorem integral_lorentzian_le_pi {a : ℝ} (ha : 0 < a) :
    ∫ t in (-Real.pi)..Real.pi, a / (a ^ 2 + t ^ 2) ≤ Real.pi := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hderiv : ∀ x : ℝ, HasDerivAt (fun t => Real.arctan (t / a)) (a / (a ^ 2 + x ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t / a) (1 / a) x :=
      (hasDerivAt_id x).div_const a
    have h2 := (Real.hasDerivAt_arctan (x / a)).comp x h1
    have heq : (1 / (1 + (x / a) ^ 2)) * (1 / a) = a / (a ^ 2 + x ^ 2) := by
      field_simp
    rwa [heq] at h2
  have hcont : Continuous (fun t : ℝ => a / (a ^ 2 + t ^ 2)) := by
    apply Continuous.div continuous_const
    · fun_prop
    · intro t; positivity
  have hint : IntervalIntegrable (fun t : ℝ => a / (a ^ 2 + t ^ 2)) volume (-Real.pi) Real.pi :=
    hcont.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) hint
  rw [hFTC]
  have h1 := Real.arctan_lt_pi_div_two (Real.pi / a)
  have h2 := Real.neg_pi_div_two_lt_arctan ((-Real.pi) / a)
  linarith [Real.pi_pos]

/-- N7a: quadratic lower bound for Poisson denominator. -/
private theorem fatou_kernel_denom_bound {r t : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1)
    (ht : |t| ≤ Real.pi) :
    1 - 2 * r * Real.cos t + r ^ 2 ≥ (2 / Real.pi ^ 2) * ((1 - r) ^ 2 + t ^ 2) := by
  have hcos : Real.cos t ≤ 1 - 2 / Real.pi ^ 2 * t ^ 2 :=
    Real.cos_le_one_sub_mul_cos_sq ht
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hr_nn : 0 ≤ r := by linarith
  have h2 : (1 - r) ^ 2 + 2 * r * (1 - Real.cos t) = 1 - 2 * r * Real.cos t + r ^ 2 := by ring
  rw [← h2]
  have h1 : 2 * r * (1 - Real.cos t) ≥ 2 * r * (2 / Real.pi ^ 2 * t ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hr2' : 2 * r * (2 / Real.pi ^ 2 * t ^ 2) ≥ (2 / Real.pi ^ 2) * t ^ 2 := by
    have : 2 * r * (2 / Real.pi ^ 2 * t ^ 2) = (2 * r) * ((2 / Real.pi ^ 2) * t ^ 2) := by ring
    rw [this]
    have hr : (1 : ℝ) ≤ 2 * r := by linarith
    have hnn : 0 ≤ (2 / Real.pi ^ 2) * t ^ 2 := by positivity
    calc (2 / Real.pi ^ 2) * t ^ 2 = 1 * ((2 / Real.pi ^ 2) * t ^ 2) := by ring
      _ ≤ (2 * r) * ((2 / Real.pi ^ 2) * t ^ 2) := by
          apply mul_le_mul_of_nonneg_right hr hnn
  have hle : (2 / Real.pi ^ 2) * ((1 - r) ^ 2 + t ^ 2)
      ≤ (1 - r) ^ 2 + (2 / Real.pi ^ 2) * t ^ 2 := by
    have hfrac : 2 / Real.pi ^ 2 ≤ 1 := by
      rw [div_le_one hpi2]
      nlinarith [hpi, Real.pi_pos]
    nlinarith [sq_nonneg ((1 - r)), sq_nonneg t, hfrac]
  linarith

private theorem poly_ident {u r : ℂ} (hu : u ≠ 0) :
    u * (u⁻¹ - r) ^ 2 - u⁻¹ * (u - r) ^ 2 = (r ^ 2 - 1) * (u - u⁻¹) := by
  field_simp
  ring

private theorem rat_ident {u r : ℂ} (hr : r ≠ 0) (h1 : u - r ≠ 0) (h2 : u - r⁻¹ ≠ 0) (hu : u ≠ 0) :
    u * (((u - r) ^ 2)⁻¹ - (r ^ 2)⁻¹ * ((u - r⁻¹) ^ 2)⁻¹)
      = (r ^ 2 - 1) * (u - u⁻¹) / ((u - r) * (u⁻¹ - r)) ^ 2 := by
  have h3 : u⁻¹ - r ≠ 0 := by
    intro h
    apply h2
    have hr2 : u⁻¹ = r := sub_eq_zero.mp h
    have hu2 : u = r⁻¹ := by rw [← hr2, inv_inv]
    rw [hu2, sub_self]
  have hD : (u - r) * (u⁻¹ - r) ≠ 0 := mul_ne_zero h1 h3
  have hD2 : ((u - r) * (u⁻¹ - r)) ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hA2 : ((u - r) ^ 2) ≠ 0 := pow_ne_zero 2 h1
  have hB2 : ((u⁻¹ - r) ^ 2) ≠ 0 := pow_ne_zero 2 h3
  have hr2 : (r : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have erel : (u - r⁻¹) = -(u / r) * (u⁻¹ - r) := by
    field_simp
    ring
  have step1 : (-(u / r) * (u⁻¹ - r)) ^ 2 = (u ^ 2 / r ^ 2) * (u⁻¹ - r) ^ 2 := by ring
  have step2 : ((u ^ 2 / r ^ 2) * (u⁻¹ - r) ^ 2)⁻¹
      = (r ^ 2 / u ^ 2) * (((u⁻¹ - r) ^ 2)⁻¹) := by
    rw [mul_inv, inv_div]
  have step3 : (r ^ 2)⁻¹ * (r ^ 2 / u ^ 2) = ((u ^ 2)⁻¹ : ℂ) := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hr2, one_mul]
  have inner : (r ^ 2)⁻¹ * (r ^ 2 / u ^ 2 * (((u⁻¹ - r) ^ 2)⁻¹ : ℂ))
      = (u ^ 2)⁻¹ * (((u⁻¹ - r) ^ 2)⁻¹ : ℂ) := by
    rw [← mul_assoc, step3]
  have cu : (u : ℂ) * ((u ^ 2)⁻¹) = u⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  rw [eq_div_iff hD2, erel, step1, step2, inner, mul_pow]
  have expand : (u : ℂ) * (((u - r) ^ 2)⁻¹ - (u ^ 2)⁻¹ * (((u⁻¹ - r) ^ 2)⁻¹))
      * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
      = u * ((u⁻¹ - r) ^ 2) - u⁻¹ * ((u - r) ^ 2) := by
    have eA : (u : ℂ) * (((u - r) ^ 2)⁻¹) * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
        = u * ((u⁻¹ - r) ^ 2) := by
      rw [show u * ((u - r) ^ 2)⁻¹ * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
        = u * (((u - r) ^ 2)⁻¹ * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)) by ring,
        show ((u - r) ^ 2)⁻¹ * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
          = ((u - r) ^ 2)⁻¹ * ((u - r) ^ 2) * ((u⁻¹ - r) ^ 2) by ring,
        inv_mul_cancel₀ hA2, one_mul]
    have eB : (u : ℂ) * ((u ^ 2)⁻¹ * (((u⁻¹ - r) ^ 2)⁻¹))
        * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
        = u⁻¹ * ((u - r) ^ 2) := by
      rw [show u * ((u ^ 2)⁻¹ * ((u⁻¹ - r) ^ 2)⁻¹) * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
        = (u * (u ^ 2)⁻¹) * ((((u⁻¹ - r) ^ 2)⁻¹) * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)) by ring,
        cu,
        show ((u⁻¹ - r) ^ 2)⁻¹ * ((u - r) ^ 2 * (u⁻¹ - r) ^ 2)
          = ((u⁻¹ - r) ^ 2)⁻¹ * ((u⁻¹ - r) ^ 2) * ((u - r) ^ 2) by ring,
        inv_mul_cancel₀ hB2, one_mul]
    linear_combination eA - eB
  rw [expand]
  exact poly_ident hu

private theorem exp_sub_inv {t : ℝ} :
    Complex.exp ((t : ℂ) * Complex.I) - (Complex.exp ((t : ℂ) * Complex.I))⁻¹
      = 2 * Complex.I * Complex.sin ((t : ℂ)) := by
  have h := Complex.two_sin ((t : ℂ))
  simp only [neg_mul] at h
  have hinv : (Complex.exp ((t : ℂ) * Complex.I))⁻¹
      = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [← Complex.exp_neg]
  rw [hinv]
  have hI : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  linear_combination (Complex.exp (↑t * Complex.I) - Complex.exp (-(↑t * Complex.I))) * hI
    - h * Complex.I

private theorem exp_prod_eq {t : ℝ} {r : ℝ} :
    (Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ))
      * ((Complex.exp ((t : ℂ) * Complex.I))⁻¹ - (r : ℂ))
      = ((1 - 2 * r * Real.cos t + r ^ 2 : ℝ) : ℂ) := by
  have h := Complex.two_cos ((t : ℂ))
  simp only [neg_mul] at h
  have hinv : (Complex.exp ((t : ℂ) * Complex.I))⁻¹
      = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [← Complex.exp_neg]
  have huu : Complex.exp ((t : ℂ) * Complex.I) * (Complex.exp ((t : ℂ) * Complex.I))⁻¹ = 1 :=
    mul_inv_cancel₀ (Complex.exp_ne_zero _)
  have hsum : Complex.exp ((t : ℂ) * Complex.I) + (Complex.exp ((t : ℂ) * Complex.I))⁻¹
      = 2 * Complex.cos ((t : ℂ)) := by
    rw [hinv]; linear_combination -h
  have hexpand : (Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ))
      * ((Complex.exp ((t : ℂ) * Complex.I))⁻¹ - (r : ℂ))
      = 1 - (r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I)
        + (Complex.exp ((t : ℂ) * Complex.I))⁻¹) + (r : ℂ) ^ 2 := by
    linear_combination huu
  rw [hexpand, hsum]
  push_cast [Complex.ofReal_cos]
  ring

private theorem fatou_kernel_identity {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (Complex.exp ((t : ℂ) * Complex.I)) *
      ((Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ)) ^ (-2 : ℤ)
        - ((r : ℂ) ^ 2)⁻¹ * (Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ)⁻¹) ^ (-2 : ℤ))
      = -2 * Complex.I * (((1 - r ^ 2) * Real.sin t / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2 : ℝ) :
          ℂ) := by
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr0
  have hu : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hnorm : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hur : Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ) ≠ 0 := by
    intro h
    have heq : Complex.exp ((t : ℂ) * Complex.I) = (r : ℂ) := sub_eq_zero.mp h
    have h1 : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = ‖(r : ℂ)‖ := by rw [heq]
    rw [hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at h1
    linarith
  have hurinv : Complex.exp ((t : ℂ) * Complex.I) - (r : ℂ)⁻¹ ≠ 0 := by
    intro h
    have heq : Complex.exp ((t : ℂ) * Complex.I) = (r : ℂ)⁻¹ := sub_eq_zero.mp h
    have h1 : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = ‖(r : ℂ)⁻¹‖ := by rw [heq]
    rw [hnorm, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at h1
    have hrinv : (1 : ℝ) < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
    linarith
  rw [zpow_neg, zpow_ofNat, zpow_neg, zpow_ofNat]
  have hrat := rat_ident hr0' hur hurinv hu
  rw [hrat, exp_sub_inv, exp_prod_eq, ← Complex.ofReal_sin]
  push_cast
  ring
private theorem circleIntegral_sub_sq_eq_deriv_unit_disc
    {G g : ℂ → ℂ} (hGcont : Continuous G)
    (hG : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt G (g z) z)
    {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    (∮ z in C((0 : ℂ), 1), (z - w) ^ (-2 : ℤ) • G z)
      = (2 * (Real.pi : ℂ) * Complex.I) * g w := by
  have hdiff : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) 1) :=
    fun z hz => ((hG z hz).hasDerivWithinAt).differentiableWithinAt
  have hcont : ContinuousOn G (closure (Metric.ball (0 : ℂ) 1)) := by
    rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
    exact hGcont.continuousOn
  have hDiff : DiffContOnCl ℂ G (Metric.ball (0 : ℂ) 1) := DiffContOnCl.mk hdiff hcont
  -- Cauchy formula: Φ = (2πi) • G on D
  have hCauchy : ∀ w' ∈ Metric.ball (0 : ℂ) 1,
      (∮ z in C((0 : ℂ), 1), (z - w')⁻¹ • G z) = (2 * (Real.pi : ℂ) * Complex.I) • G w' :=
    fun w' hw' => hDiff.circleIntegral_sub_inv_smul hw'
  have hmem : Metric.ball (0 : ℂ) 1 ∈ 𝓝 w := isOpen_ball.mem_nhds hw
  have hPhi : (fun w' => ∮ z in C((0 : ℂ), 1), (z - w')⁻¹ • G z)
      =ᶠ[𝓝 w] ((2 * (Real.pi : ℂ) * Complex.I) • G) :=
    Filter.eventuallyEq_of_mem hmem (fun w' hw' => hCauchy w' hw')
  have hderiv1 : HasDerivAt ((2 * (Real.pi : ℂ) * Complex.I) • G)
      ((2 * (Real.pi : ℂ) * Complex.I) • g w) w :=
    HasDerivAt.const_smul _ (hG w hw)
  have hderiv1' : HasDerivAt (fun w' => ∮ z in C((0 : ℂ), 1), (z - w')⁻¹ • G z)
      ((2 * (Real.pi : ℂ) * Complex.I) • g w) w :=
    hderiv1.congr_of_eventuallyEq hPhi
  have hCirc : CircleIntegrable G (0 : ℂ) 1 :=
    hGcont.continuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hwsph : w ∉ sphere (0 : ℂ) |1| := by
    rw [abs_one]
    intro hcon
    have h1 : dist w 0 = 1 := Metric.mem_sphere.mp hcon
    have h2 : dist w 0 < 1 := Metric.mem_ball.mp hw
    rw [dist_zero_right] at h1 h2
    linarith
  have hderiv2 : HasDerivAt (fun w' => ∮ z in C((0 : ℂ), 1), (z - w')⁻¹ • G z)
      (∮ z in C((0 : ℂ), 1), (z - w) ^ (-2 : ℤ) • G z) w :=
    hasDerivAt_circleIntegral_sub_inv_smul hCirc hwsph
  have heq := hderiv1'.unique hderiv2
  rw [smul_eq_mul] at heq
  exact heq.symm
private theorem circleIntegral_reflected_pole_eq_zero
    {G : ℂ → ℂ} (hGcont : Continuous G)
    (hGdiff : ∀ z ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ G z)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∮ z in C((0 : ℂ), 1), (z - (r : ℂ)⁻¹) ^ (-2 : ℤ) • G z) = 0 := by
  have hrinv_gt : (1 : ℝ) < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
  have hcnorm : ‖(r : ℂ)⁻¹‖ = r⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hne : ∀ z : ℂ, ‖z‖ ≤ 1 → z - (r : ℂ)⁻¹ ≠ 0 := by
    intro z hz hcon
    have heq : z = (r : ℂ)⁻¹ := sub_eq_zero.mp hcon
    rw [heq, hcnorm] at hz
    linarith
  have hsmul : (fun z : ℂ => (z - (r : ℂ)⁻¹) ^ (-2 : ℤ) • G z)
      = (fun z : ℂ => (z - (r : ℂ)⁻¹) ^ (-2 : ℤ) * G z) := by
    funext z; exact smul_eq_mul _ _
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable
    (by norm_num : (0 : ℝ) ≤ 1) (s := ∅) countable_empty ?_ ?_
  · rw [hsmul]
    apply ContinuousOn.mul _ hGcont.continuousOn
    apply ContinuousOn.zpow₀ (ContinuousOn.sub continuousOn_id continuousOn_const) (-2)
    intro a ha
    left
    apply hne
    have hdist : dist a 0 ≤ 1 := Metric.mem_closedBall.mp ha
    rwa [dist_zero_right] at hdist
  · intro z hz
    have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa using hz.1
    have hzne : z - (r : ℂ)⁻¹ ≠ 0 := by
      apply hne
      have hdist : dist z 0 < 1 := Metric.mem_ball.mp hzmem
      rw [dist_zero_right] at hdist
      linarith
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (w - (r : ℂ)⁻¹) ^ (-2 : ℤ)) z :=
      (differentiableAt_id.sub_const _).zpow (Or.inl hzne)
    rw [hsmul]
    exact hpow.mul (hGdiff z hzmem)
private noncomputable def fatouKernel (r t : ℝ) : ℝ :=
  (1 - r ^ 2) * Real.sin t / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2

private theorem kernel_cast_eq {r θ : ℝ} :
    (((1 - r ^ 2) * Real.sin θ / (1 - 2 * r * Real.cos θ + r ^ 2) ^ 2 : ℝ) : ℂ)
      = (fatouKernel r θ : ℂ) := by
  rfl

private theorem deriv_eq_poisson_core
    {G g : ℂ → ℂ} (hGcont : Continuous G)
    (hG : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt G (g z) z)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    2 * (Real.pi : ℂ) * Complex.I * g ((r : ℂ))
      = 2 * ∫ t in (0 : ℝ)..2 * Real.pi,
        ((fatouKernel r t : ℂ) * G (Complex.exp ((t : ℂ) * Complex.I))) := by
  have hGdiff : ∀ z ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ G z :=
    fun z hz => (hG z hz).differentiableAt
  have hc : (r : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
    exact hr1
  have hN4 := circleIntegral_sub_sq_eq_deriv_unit_disc hGcont hG hc
  have hN5 := circleIntegral_reflected_pole_eq_zero hGcont hGdiff hr0 hr1
  have hsmul1 : (fun z : ℂ => (z - (r : ℂ)) ^ (-2 : ℤ) • G z)
      = (fun z : ℂ => (z - (r : ℂ)) ^ (-2 : ℤ) * G z) := by
    funext z; exact smul_eq_mul _ _
  have hsmul2 : (fun z : ℂ => (z - (r : ℂ)⁻¹) ^ (-2 : ℤ) • G z)
      = (fun z : ℂ => (z - (r : ℂ)⁻¹) ^ (-2 : ℤ) * G z) := by
    funext z; exact smul_eq_mul _ _
  have hsph1 : ∀ z : ℂ, z ∈ sphere (0 : ℂ) 1 → z - (r : ℂ) ≠ 0 := by
    intro z hz hcon
    have h11 : dist z 0 = 1 := Metric.mem_sphere.mp hz
    rw [dist_zero_right] at h11
    have heq : z = (r : ℂ) := sub_eq_zero.mp hcon
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at h11
    linarith
  have hsph2 : ∀ z : ℂ, z ∈ sphere (0 : ℂ) 1 → z - (r : ℂ)⁻¹ ≠ 0 := by
    intro z hz hcon
    have h11 : dist z 0 = 1 := Metric.mem_sphere.mp hz
    rw [dist_zero_right] at h11
    have heq : z = (r : ℂ)⁻¹ := sub_eq_zero.mp hcon
    have hcn : ‖(r : ℂ)⁻¹‖ = r⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    rw [heq, hcn] at h11
    have hrinv : (1 : ℝ) < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
    linarith
  have hF1c : ContinuousOn (fun z : ℂ => (z - (r : ℂ)) ^ (-2 : ℤ) • G z) (sphere 0 1) := by
    rw [hsmul1]
    apply ContinuousOn.mul _ hGcont.continuousOn
    apply ContinuousOn.zpow₀ (ContinuousOn.sub continuousOn_id continuousOn_const) (-2)
    intro a ha; exact Or.inl (hsph1 a ha)
  have hF2c : ContinuousOn (fun z : ℂ => (z - (r : ℂ)⁻¹) ^ (-2 : ℤ) • G z) (sphere 0 1) := by
    rw [hsmul2]
    apply ContinuousOn.mul _ hGcont.continuousOn
    apply ContinuousOn.zpow₀ (ContinuousOn.sub continuousOn_id continuousOn_const) (-2)
    intro a ha; exact Or.inl (hsph2 a ha)
  have hF1i : CircleIntegrable (fun z : ℂ => (z - (r : ℂ)) ^ (-2 : ℤ) • G z) 0 1 :=
    hF1c.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have haF2c' : ContinuousOn (((r : ℂ) ^ 2)⁻¹ • (fun z : ℂ =>
      (z - (r : ℂ)⁻¹) ^ (-2 : ℤ) • G z)) (sphere 0 1) :=
    hF2c.const_smul _
  have haF2i : CircleIntegrable
      (fun z : ℂ => ((r : ℂ) ^ 2)⁻¹ • ((z - (r : ℂ)⁻¹) ^ (-2 : ℤ) • G z)) 0 1 := by
    exact haF2c'.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have hcomb : (∮ z in C((0 : ℂ), 1),
        ((z - (r : ℂ)) ^ (-2 : ℤ) • G z
          - ((r : ℂ) ^ 2)⁻¹ • ((z - (r : ℂ)⁻¹) ^ (-2 : ℤ) • G z)))
      = (2 * (Real.pi : ℂ) * Complex.I) * g (r : ℂ) := by
    rw [circleIntegral.integral_sub hF1i haF2i, circleIntegral.integral_smul,
      hN5, smul_zero, sub_zero]
    exact hN4
  unfold circleIntegral at hcomb
  have e1 : ∀ θ : ℝ, circleMap (0 : ℂ) 1 θ = Complex.exp ((θ : ℂ) * Complex.I) := by
    intro θ; rw [circleMap_zero, Complex.ofReal_one, one_mul]
  have hpt : ∀ θ : ℝ, deriv (circleMap (0 : ℂ) 1) θ
        • (((circleMap (0 : ℂ) 1 θ - (r : ℂ)) ^ (-2 : ℤ) • G (circleMap (0 : ℂ) 1 θ))
          - ((r : ℂ) ^ 2)⁻¹ • (((circleMap (0 : ℂ) 1 θ - (r : ℂ)⁻¹) ^ (-2 : ℤ))
            • G (circleMap (0 : ℂ) 1 θ)))
        = 2 * ((fatouKernel r θ : ℂ) * G (Complex.exp ((θ : ℂ) * Complex.I))) := by
    intro θ
    have e2 : deriv (circleMap (0 : ℂ) 1) θ
        = Complex.exp ((θ : ℂ) * Complex.I) * Complex.I := by
      rw [deriv_circleMap, e1]
    rw [e1, e2]
    have hN3 : (Complex.exp ((θ : ℂ) * Complex.I)) *
        ((Complex.exp ((θ : ℂ) * Complex.I) - (r : ℂ)) ^ (-2 : ℤ)
          - ((r : ℂ) ^ 2)⁻¹ * (Complex.exp ((θ : ℂ) * Complex.I) - (r : ℂ)⁻¹) ^ (-2 : ℤ))
        = -2 * Complex.I * (fatouKernel r θ : ℂ) := by
      rw [← kernel_cast_eq]
      exact fatou_kernel_identity hr0 hr1
    have hI2 : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
    simp only [smul_eq_mul] at hN3 ⊢
    linear_combination (G (Complex.exp (↑θ * Complex.I)) * Complex.I) * hN3
      + (-2 * (fatouKernel r θ : ℂ) * G (Complex.exp (↑θ * Complex.I))) * hI2
  have hcongr : (∫ θ in (0 : ℝ)..2 * Real.pi, deriv (circleMap (0 : ℂ) 1) θ
        • (((circleMap (0 : ℂ) 1 θ - (r : ℂ)) ^ (-2 : ℤ) • G (circleMap (0 : ℂ) 1 θ))
          - ((r : ℂ) ^ 2)⁻¹ • (((circleMap (0 : ℂ) 1 θ - (r : ℂ)⁻¹) ^ (-2 : ℤ))
            • G (circleMap (0 : ℂ) 1 θ))))
      = ∫ θ in (0 : ℝ)..2 * Real.pi,
        (2 * ((fatouKernel r θ : ℂ) * G (Complex.exp ((θ : ℂ) * Complex.I)))) := by
    apply intervalIntegral.integral_congr
    intro θ _
    exact hpt θ
  rw [hcongr, intervalIntegral.integral_const_mul] at hcomb
  exact hcomb.symm
private theorem kernel_periodic {G : ℂ → ℂ} (r : ℝ) :
    Function.Periodic (fun t : ℝ => (fatouKernel r t : ℂ)
      * G (Complex.exp ((t : ℂ) * Complex.I))) (2 * Real.pi) := by
  intro x
  have hs : Real.sin (x + 2 * Real.pi) = Real.sin x := Real.sin_periodic x
  have hc : Real.cos (x + 2 * Real.pi) = Real.cos x := Real.cos_periodic x
  have he : Complex.exp (((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x : ℂ) * Complex.I) := by
    have hcast : ((x + 2 * Real.pi : ℝ) : ℂ) = (x : ℂ) + 2 * (Real.pi : ℂ) := by
      push_cast; ring
    rw [hcast, add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  change (fatouKernel r (x + 2 * Real.pi) : ℂ)
      * G (Complex.exp (((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I))
      = (fatouKernel r x : ℂ) * G (Complex.exp ((x : ℂ) * Complex.I))
  unfold fatouKernel
  rw [hs, hc, he]

private theorem kernel_shift {G : ℂ → ℂ} (r : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, (fatouKernel r t : ℂ)
      * G (Complex.exp ((t : ℂ) * Complex.I)))
    = ∫ t in (-Real.pi)..Real.pi, (fatouKernel r t : ℂ)
      * G (Complex.exp ((t : ℂ) * Complex.I)) := by
  have hper := kernel_periodic (G := G) r
  have e := hper.intervalIntegral_add_eq (0 : ℝ) (-Real.pi)
  rwa [zero_add, show (-Real.pi) + 2 * Real.pi = Real.pi by ring] at e
private theorem poisson_div_algebra {g J : ℂ}
    (h2J : 2 * (Real.pi : ℂ) * Complex.I * g = 2 * J) :
    g = -(Complex.I / (Real.pi : ℂ)) * J := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2I : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) hI
  have hI2 : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  have key : (2 * (Real.pi : ℂ) * Complex.I) * (-(Complex.I / (Real.pi : ℂ)) * J)
      = 2 * J := by
    field_simp
    linear_combination (-J) * hI2
  apply mul_left_cancel₀ h2I
  rw [h2J, key]

private theorem deriv_eq_poisson_deriv_integral
    {G g : ℂ → ℂ} (hGcont : Continuous G)
    (hG : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt G (g z) z)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    g ((r : ℂ)) = -(Complex.I / (Real.pi : ℂ)) * ∫ t in (-Real.pi)..Real.pi,
      ((fatouKernel r t : ℂ) * G (Complex.exp ((t : ℂ) * Complex.I))) := by
  have hcore := deriv_eq_poisson_core hGcont hG hr0 hr1
  rw [kernel_shift] at hcore
  exact poisson_div_algebra hcore
private theorem fatou_kernel_weighted_bound {r t : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1)
    (ht : |t| ≤ Real.pi) :
    |t| * |fatouKernel r t|
      ≤ (Real.pi ^ 4 / 2) * ((1 - r) / ((1 - r) ^ 2 + t ^ 2)) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hr_nn : (0 : ℝ) ≤ r := by linarith
  have hSnn : (0 : ℝ) ≤ (1 - r) ^ 2 + t ^ 2 := by positivity
  have hSpos : (0 : ℝ) < (1 - r) ^ 2 + t ^ 2 := by
    have hsq : (0 : ℝ) < (1 - r) ^ 2 := by positivity
    linarith [sq_nonneg t]
  have hDlo := fatou_kernel_denom_bound hr1 hr2 ht
  have hpi2pos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hcpos : (0 : ℝ) < 2 / Real.pi ^ 2 := by positivity
  have hDnn : (0 : ℝ) ≤ 1 - 2 * r * Real.cos t + r ^ 2 := by
    have hprod := mul_nonneg (le_of_lt hcpos) hSnn
    linarith [hDlo]
  have hDpos : (0 : ℝ) < 1 - 2 * r * Real.cos t + r ^ 2 := by
    have h := mul_pos hcpos hSpos
    linarith [hDlo]
  have hD2pos : (0 : ℝ) < (1 - 2 * r * Real.cos t + r ^ 2) ^ 2 := by positivity
  have hD2ne : (1 - 2 * r * Real.cos t + r ^ 2) ^ 2 ≠ 0 := ne_of_gt hD2pos
  have h1r2 : (0 : ℝ) ≤ 1 - r ^ 2 := by nlinarith [h1r, hr_nn, sq_nonneg r]
  have hkform : |fatouKernel r t|
      = (1 - r ^ 2) * |Real.sin t| / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2 := by
    unfold fatouKernel
    rw [abs_div, abs_mul, abs_pow, abs_of_nonneg h1r2, abs_of_pos hDpos]
  have htsin : |t| * |Real.sin t| ≤ t ^ 2 := by
    have h := Real.abs_sin_le_abs (x := t)
    calc |t| * |Real.sin t| ≤ |t| * |t| :=
          mul_le_mul_of_nonneg_left h (abs_nonneg t)
      _ = t ^ 2 := by rw [← sq_abs t, pow_two]
  have h221 : (1 - r ^ 2) ≤ 2 * (1 - r) := by nlinarith [h1r, hr1]
  have hA : |t| * |fatouKernel r t|
      ≤ 2 * (1 - r) * t ^ 2 / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2 := by
    have e1 : |t| * |fatouKernel r t|
        = (|t| * |Real.sin t|) * (1 - r ^ 2)
          / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2 := by
      rw [hkform]; ring
    have step1 : (|t| * |Real.sin t|) * (1 - r ^ 2) ≤ t ^ 2 * (1 - r ^ 2) :=
      mul_le_mul_of_nonneg_right htsin h1r2
    have step2 : t ^ 2 * (1 - r ^ 2) ≤ t ^ 2 * (2 * (1 - r)) :=
      mul_le_mul_of_nonneg_left h221 (sq_nonneg t)
    have hle : (|t| * |Real.sin t|) * (1 - r ^ 2) ≤ 2 * (1 - r) * t ^ 2 := by
      have e2 : (2 * (1 - r) * t ^ 2) = t ^ 2 * (2 * (1 - r)) := by ring
      rw [e2]
      exact le_trans step1 step2
    rw [e1, div_le_iff₀ hD2pos, div_mul_cancel₀ _ hD2ne]
    exact hle
  have hDSq : 4 * ((1 - r) ^ 2 + t ^ 2) ^ 2
      ≤ (1 - 2 * r * Real.cos t + r ^ 2) ^ 2 * Real.pi ^ 4 := by
    have step : 2 * ((1 - r) ^ 2 + t ^ 2)
        ≤ (1 - 2 * r * Real.cos t + r ^ 2) * Real.pi ^ 2 := by
      rw [← div_le_iff₀ hpi2pos]
      have h2 := hDlo
      rwa [div_mul_eq_mul_div] at h2
    have h1nn : (0 : ℝ) ≤ (1 - 2 * r * Real.cos t + r ^ 2) * Real.pi ^ 2
        - 2 * ((1 - r) ^ 2 + t ^ 2) := by linarith [step]
    have hDpi : (0 : ℝ) ≤ (1 - 2 * r * Real.cos t + r ^ 2) * Real.pi ^ 2 :=
      mul_nonneg hDnn (sq_nonneg _)
    have h2nn : (0 : ℝ) ≤ (1 - 2 * r * Real.cos t + r ^ 2) * Real.pi ^ 2
        + 2 * ((1 - r) ^ 2 + t ^ 2) := by
      have hS2 : (0 : ℝ) ≤ 2 * ((1 - r) ^ 2 + t ^ 2) := by linarith [hSnn]
      linarith [hDpi, hS2]
    have e : (1 - 2 * r * Real.cos t + r ^ 2) ^ 2 * Real.pi ^ 4
          - 4 * ((1 - r) ^ 2 + t ^ 2) ^ 2
        = ((1 - 2 * r * Real.cos t + r ^ 2) * Real.pi ^ 2
          - 2 * ((1 - r) ^ 2 + t ^ 2))
        * ((1 - 2 * r * Real.cos t + r ^ 2) * Real.pi ^ 2
          + 2 * ((1 - r) ^ 2 + t ^ 2)) := by
      ring
    have p := mul_nonneg h1nn h2nn
    linarith [p]
  have hB : 2 * (1 - r) * t ^ 2 / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2
      ≤ (Real.pi ^ 4 / 2) * ((1 - r) / ((1 - r) ^ 2 + t ^ 2)) := by
    have hrw : (Real.pi ^ 4 / 2) * ((1 - r) / ((1 - r) ^ 2 + t ^ 2))
        = ((Real.pi ^ 4 / 2) * (1 - r)) / ((1 - r) ^ 2 + t ^ 2) := by
      ring
    rw [hrw, le_div_iff₀ hSpos, div_mul_eq_mul_div, div_le_iff₀ hD2pos]
    have h1 : (0 : ℝ) ≤ (1 - r)
        * ((1 - 2 * r * Real.cos t + r ^ 2) ^ 2 * Real.pi ^ 4
          - 4 * ((1 - r) ^ 2 + t ^ 2) ^ 2) :=
      mul_nonneg (le_of_lt h1r) (by linarith [hDSq])
    have hSqnn : (0 : ℝ) ≤ ((1 - r) ^ 2 + t ^ 2) ^ 2
        - t ^ 2 * ((1 - r) ^ 2 + t ^ 2) := by
      have e2 : ((1 - r) ^ 2 + t ^ 2) ^ 2 - t ^ 2 * ((1 - r) ^ 2 + t ^ 2)
          = ((1 - r) ^ 2 + t ^ 2) * (1 - r) ^ 2 := by ring
      rw [e2]
      exact mul_nonneg hSnn (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ (1 - r)
        * (((1 - r) ^ 2 + t ^ 2) ^ 2 - t ^ 2 * ((1 - r) ^ 2 + t ^ 2)) :=
      mul_nonneg (le_of_lt h1r) hSqnn
    linarith [h1, h2]
  exact le_trans hA hB
private theorem poisson_deriv_integral_tendsto_zero
    {ψ : ℝ → ℂ} (_hψcont : Continuous ψ)
    {K : ℝ} (hK : ∀ t : ℝ, |t| ≤ Real.pi → ‖ψ t‖ ≤ K * |t|)
    (hlittle : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ‖ψ t‖ ≤ ε * |t|) :
    Filter.Tendsto (fun r : ℝ => ∫ t in (-Real.pi)..Real.pi,
      ((fatouKernel r t : ℂ) * ψ t)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  rw [tendsto_nhdsWithin_nhds]
  intro ε₀ hε₀
  have hCpos : (0 : ℝ) < Real.pi ^ 4 / 2 := by positivity
  have hCπ : (0 : ℝ) < (Real.pi ^ 4 / 2) * Real.pi + 1 := by
    have := mul_nonneg (le_of_lt hCpos) (le_of_lt Real.pi_pos)
    linarith
  have hε₁pos : (0 : ℝ) < ε₀ / (2 * ((Real.pi ^ 4 / 2) * Real.pi + 1)) := by positivity
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hlittle _ hε₁pos
  have hδ₁pos : (0 : ℝ) < min δ₀ Real.pi := lt_min hδ₀pos Real.pi_pos
  have hδ₁leπ : min δ₀ Real.pi ≤ Real.pi := min_le_right _ _
  have hδ₁leδ : min δ₀ Real.pi ≤ δ₀ := min_le_left _ _
  set C := Real.pi ^ 4 / 2 with hC
  set ε₁ := ε₀ / (2 * ((Real.pi ^ 4 / 2) * Real.pi + 1)) with hε₁
  set δ₁ := min δ₀ Real.pi with hδ₁
  have hKnn : (0 : ℝ) ≤ |K| := abs_nonneg K
  have hK' : ∀ t : ℝ, |t| ≤ Real.pi → ‖ψ t‖ ≤ |K| * |t| := by
    intro t ht
    calc ‖ψ t‖ ≤ K * |t| := hK t ht
      _ ≤ |K| * |t| := mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg t)
  have hδ₁2pos : (0 : ℝ) < δ₁ ^ 2 := by positivity
  have hδ₁2ne : δ₁ ^ 2 ≠ 0 := ne_of_gt hδ₁2pos
  -- choice of radius-tolerance
  set D0 := ε₁ * δ₁ ^ 2 / (2 * Real.pi * |K| * C + 1) with hD0
  have hD0pos : (0 : ℝ) < D0 := by
    have h1 : (0 : ℝ) < 2 * Real.pi * |K| * C + 1 := by
      have hnn : (0 : ℝ) ≤ 2 * Real.pi * |K| * C := by
        have h1 : (0 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_pos]
        have h2 := mul_nonneg h1 hKnn
        have h3 := mul_nonneg h2 (le_of_lt hCpos)
        linarith [h3]
      linarith [hnn]
    have h2 : (0 : ℝ) < ε₁ * δ₁ ^ 2 := mul_pos hε₁pos hδ₁2pos
    exact div_pos h2 h1
  refine ⟨min (1 / 2) D0, lt_min (by norm_num) hD0pos, fun x hx hdist => ?_⟩
  have hxr1 : x < 1 := hx
  have hdist' : dist x 1 < min (1 / 2) D0 := hdist
  have hx12 : 1 / 2 ≤ x := by
    have h1 : dist x 1 < 1 / 2 := lt_of_lt_of_le hdist' (min_le_left _ _)
    rw [Real.dist_eq] at h1
    have h2 : x ≤ 1 := le_of_lt hxr1
    have habs : |x - 1| = 1 - x := by
      rw [abs_of_nonpos (by linarith : x - 1 ≤ 0)]
      ring
    rw [habs] at h1
    linarith
  have hax : x < 1 ∧ 1 / 2 ≤ x := ⟨hxr1, hx12⟩
  have ha : (0 : ℝ) < 1 - x := by linarith
  have hxa : 1 - x < D0 := by
    have h1 : dist x 1 < D0 := lt_of_lt_of_le hdist' (min_le_right _ _)
    rw [Real.dist_eq] at h1
    have habs : |x - 1| = 1 - x := by
      rw [abs_of_nonpos (by linarith : x - 1 ≤ 0)]
      ring
    rw [habs] at h1
    exact h1
  -- abbreviations for this r
  set a := 1 - x with ha_def
  have hapos : (0 : ℝ) < a := ha
  have hdenpos : ∀ t : ℝ, (0 : ℝ) < a ^ 2 + t ^ 2 := by
    intro t
    have h1 : (0 : ℝ) < a ^ 2 := pow_pos hapos 2
    linarith [sq_nonneg t]
  -- pointwise bound
  have hpt : ∀ t : ℝ, t ∈ Ioc (-Real.pi) Real.pi →
      ‖((fatouKernel x t : ℂ) * ψ t)‖
        ≤ ε₁ * C * (a / (a ^ 2 + t ^ 2)) + |K| * C * a / δ₁ ^ 2 := by
    intro t ht
    have htmem := ht
    rw [mem_Ioc] at htmem
    have habs : |t| ≤ Real.pi := by
      rw [abs_le]
      constructor <;> linarith [htmem.1, htmem.2]
    have hKb := fatou_kernel_weighted_bound hx12 hxr1 habs
    have hKb' : |t| * |fatouKernel x t| ≤ C * (a / (a ^ 2 + t ^ 2)) := hKb
    have hknorm : ‖((fatouKernel x t : ℂ) * ψ t)‖ = |fatouKernel x t| * ‖ψ t‖ := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hknorm]
    by_cases hcase : |t| < δ₁
    · have hψ := hδ₀ t (lt_of_lt_of_le hcase hδ₁leδ)
      have e : |fatouKernel x t| * ‖ψ t‖ ≤ |fatouKernel x t| * (ε₁ * |t|) :=
        mul_le_mul_of_nonneg_left hψ (abs_nonneg _)
      have e2 : |fatouKernel x t| * (ε₁ * |t|) = ε₁ * (|t| * |fatouKernel x t|) := by
        ring
      have s1 : |fatouKernel x t| * (ε₁ * |t|)
          ≤ ε₁ * C * (a / (a ^ 2 + t ^ 2)) := by
        rw [e2]
        have h := mul_le_mul_of_nonneg_left hKb' (le_of_lt hε₁pos)
        linarith [h]
      have hnn : (0 : ℝ) ≤ |K| * C * a / δ₁ ^ 2 := by positivity
      have e3 : |fatouKernel x t| * ‖ψ t‖
          ≤ ε₁ * C * (a / (a ^ 2 + t ^ 2)) + |K| * C * a / δ₁ ^ 2 := by
        linarith [le_trans e s1, hnn]
      exact e3
    · have hcase : δ₁ ≤ |t| := not_lt.mp hcase
      have hψ := hK' t habs
      have e : |fatouKernel x t| * ‖ψ t‖ ≤ |fatouKernel x t| * (|K| * |t|) :=
        mul_le_mul_of_nonneg_left hψ (abs_nonneg _)
      have e2 : |fatouKernel x t| * (|K| * |t|) = |K| * (|t| * |fatouKernel x t|) := by
        ring
      have s1 : |fatouKernel x t| * (|K| * |t|)
          ≤ |K| * (C * (a / (a ^ 2 + t ^ 2))) := by
        rw [e2]
        exact mul_le_mul_of_nonneg_left hKb' hKnn
      -- a/(a²+t²) ≤ a/δ₁²
      have hsq : δ₁ ^ 2 ≤ t ^ 2 := by
        rw [← sq_abs t]
        have p := mul_nonneg (sub_nonneg.mpr hcase)
          (show (0 : ℝ) ≤ |t| + δ₁ by linarith [abs_nonneg t, lt_of_lt_of_le hδ₁pos (le_refl _)])
        have e4 : |t| ^ 2 - δ₁ ^ 2 = (|t| - δ₁) * (|t| + δ₁) := by ring
        linarith [p]
      have hden : δ₁ ^ 2 ≤ a ^ 2 + t ^ 2 := by
        have h1 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
        linarith [hsq]
      have hfrac : (1 : ℝ) ≤ (a ^ 2 + t ^ 2) / δ₁ ^ 2 := by
        rw [le_div_iff₀ hδ₁2pos]
        linarith [hden]
      have hle2 : a / (a ^ 2 + t ^ 2) ≤ a / δ₁ ^ 2 := by
        have hdenpos' : (0 : ℝ) < a ^ 2 + t ^ 2 := hdenpos t
        rw [div_le_iff₀ hdenpos', div_mul_eq_mul_div, le_div_iff₀ hδ₁2pos]
        exact mul_le_mul_of_nonneg_left hden (le_of_lt hapos)
      have KCnn : (0 : ℝ) ≤ |K| * C := mul_nonneg hKnn (le_of_lt hCpos)
      have e6 : |K| * (C * (a / (a ^ 2 + t ^ 2))) ≤ |K| * (C * (a / δ₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hle2 (le_of_lt hCpos)) hKnn
      have e7 : |K| * (C * (a / δ₁ ^ 2)) = |K| * C * a / δ₁ ^ 2 := by ring
      have e8 : |K| * (C * (a / (a ^ 2 + t ^ 2))) = |K| * C * a / (a ^ 2 + t ^ 2) := by
        ring
      have hnn : (0 : ℝ) ≤ ε₁ * C * (a / (a ^ 2 + t ^ 2)) := by positivity
      rw [e8] at e6
      have e3 : |fatouKernel x t| * ‖ψ t‖
          ≤ ε₁ * C * (a / (a ^ 2 + t ^ 2)) + |K| * C * a / δ₁ ^ 2 := by
        linarith [le_trans e s1, e6, e7, hnn]
      exact e3
  -- bound function and its integral
  have hBcont : Continuous (fun t : ℝ =>
      ε₁ * C * (a / (a ^ 2 + t ^ 2)) + |K| * C * a / δ₁ ^ 2) := by
    apply Continuous.add
    · apply Continuous.const_mul
      apply Continuous.div continuous_const
      · exact continuous_const.add (continuous_id.pow 2)
      · intro t
        exact ne_of_gt (hdenpos t)
    · exact continuous_const
  have hBint : IntervalIntegrable (fun t : ℝ =>
      ε₁ * C * (a / (a ^ 2 + t ^ 2)) + |K| * C * a / δ₁ ^ 2)
      volume (-Real.pi) Real.pi :=
    hBcont.intervalIntegrable _ _
  have hae : ∀ᵐ t : ℝ ∂volume, t ∈ Ioc (-Real.pi) Real.pi →
      ‖((fatouKernel x t : ℂ) * ψ t)‖
        ≤ ε₁ * C * (a / (a ^ 2 + t ^ 2)) + |K| * C * a / δ₁ ^ 2 :=
    Filter.Eventually.of_forall (fun t ht => hpt t ht)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (a := -Real.pi) (b := Real.pi)
    (f := fun t : ℝ => ((fatouKernel x t : ℂ) * ψ t))
    (g := fun t : ℝ => ε₁ * C * (a / (a ^ 2 + t ^ 2)) + |K| * C * a / δ₁ ^ 2)
    (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi) hae hBint
  have hlor := integral_lorentzian_le_pi hapos
  have hint1 : IntervalIntegrable (fun t : ℝ => a / (a ^ 2 + t ^ 2)) volume
      (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const
    · exact continuous_const.add (continuous_id.pow 2)
    · intro t
      exact ne_of_gt (hdenpos t)
  have hint2 : IntervalIntegrable (fun _ : ℝ => |K| * C * a / δ₁ ^ 2) volume
      (-Real.pi) Real.pi :=
    continuous_const.intervalIntegrable _ _
  have hsplit : (∫ t in (-Real.pi)..Real.pi,
        (ε₁ * C * (a / (a ^ 2 + t ^ 2)) + |K| * C * a / δ₁ ^ 2))
      = ε₁ * C * (∫ t in (-Real.pi)..Real.pi, a / (a ^ 2 + t ^ 2))
        + (|K| * C * a / δ₁ ^ 2) * (2 * Real.pi) := by
    have e1 : (∫ t in (-Real.pi)..Real.pi,
          (ε₁ * C * (a / (a ^ 2 + t ^ 2)) + |K| * C * a / δ₁ ^ 2))
        = (∫ t in (-Real.pi)..Real.pi, ε₁ * C * (a / (a ^ 2 + t ^ 2)))
          + ∫ _ in (-Real.pi)..Real.pi, |K| * C * a / δ₁ ^ 2 := by
      have e1a : IntervalIntegrable (fun t : ℝ => ε₁ * C * (a / (a ^ 2 + t ^ 2)))
          volume (-Real.pi) Real.pi :=
        IntervalIntegrable.const_mul hint1 (ε₁ * C)
      exact intervalIntegral.integral_add e1a hint2
    rw [e1, intervalIntegral.integral_const_mul]
    have e2 : (∫ _ in (-Real.pi)..Real.pi, |K| * C * a / δ₁ ^ 2)
        = (|K| * C * a / δ₁ ^ 2) * (2 * Real.pi) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    rw [e2]
  have hfinal : ‖∫ t in (-Real.pi)..Real.pi,
        ((fatouKernel x t : ℂ) * ψ t)‖ < ε₀ := by
    have hle : ‖∫ t in (-Real.pi)..Real.pi, ((fatouKernel x t : ℂ) * ψ t)‖
        ≤ ε₁ * C * (∫ t in (-Real.pi)..Real.pi, a / (a ^ 2 + t ^ 2))
          + (|K| * C * a / δ₁ ^ 2) * (2 * Real.pi) :=
      le_trans hnorm (by rw [hsplit])
    have h1 : ε₁ * C * (∫ t in (-Real.pi)..Real.pi, a / (a ^ 2 + t ^ 2))
        ≤ ε₁ * C * Real.pi :=
      mul_le_mul_of_nonneg_left hlor (by positivity)
    have haxD : a < D0 := hxa
    have h2 : (|K| * C * a / δ₁ ^ 2) * (2 * Real.pi) ≤ ε₁ := by
      have hD0bd : a * (2 * Real.pi * |K| * C) ≤ ε₁ * δ₁ ^ 2 := by
        have hD0def := hD0
        -- D0 = ε₁δ₁²/(2π|K|C+1), a < D0
        have hden : (0 : ℝ) < 2 * Real.pi * |K| * C + 1 := by
          have hnn : (0 : ℝ) ≤ 2 * Real.pi * |K| * C := by
            have h1 : (0 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_pos]
            have h2 := mul_nonneg h1 hKnn
            have h3 := mul_nonneg h2 (le_of_lt hCpos)
            linarith [h3]
          linarith [hnn]
        have h3 : a < ε₁ * δ₁ ^ 2 / (2 * Real.pi * |K| * C + 1) := by
          rw [hD0def] at haxD
          exact haxD
        rw [lt_div_iff₀ hden] at h3
        linarith [h3]
      have e9 : (|K| * C * a / δ₁ ^ 2) * (2 * Real.pi)
          = a * (2 * Real.pi * |K| * C) / δ₁ ^ 2 := by ring
      rw [e9, div_le_iff₀ hδ₁2pos]
      linarith [hD0bd]
    have hsum : ε₁ * C * (∫ t in (-Real.pi)..Real.pi, a / (a ^ 2 + t ^ 2))
          + (|K| * C * a / δ₁ ^ 2) * (2 * Real.pi)
        ≤ ε₁ * C * Real.pi + ε₁ := add_le_add h1 h2
    have heq : ε₁ * C * Real.pi + ε₁ = ε₀ / 2 := by
      rw [hC, hε₁]
      have hne : (2 : ℝ) * ((Real.pi ^ 4 / 2) * Real.pi + 1) ≠ 0 :=
        ne_of_gt (by
          have h := hCπ
          rw [hC] at h
          linarith [h])
      field_simp
    linarith [hle, hsum, heq]
  rw [dist_zero_right]
  exact hfinal
private theorem radial_limit_at_one_of_hasDerivAt_boundary
    {G : ℂ → ℂ} {K : NNReal} (hGlip : LipschitzWith K G)
    {g : ℂ → ℂ} (hG : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt G (g z) z)
    {c : ℂ}
    (hφ : HasDerivAt (fun t : ℝ => G (Complex.exp ((t : ℂ) * Complex.I))) c 0) :
    Filter.Tendsto (fun r : ℝ => g ((r : ℂ))) (𝓝[<] (1 : ℝ)) (𝓝 (c / Complex.I)) := by
  have hGcont : Continuous G := hGlip.continuous
  -- derivative of t ↦ exp((t:ℂ)*I) at 0 is I
  have hofReal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 (0 : ℝ) :=
    ContinuousLinearMap.hasDerivAt Complex.ofRealCLM
  have hinner : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) (1 * Complex.I) 0 :=
    hofReal.mul_const Complex.I
  have he : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) Complex.I 0 := by
    have h := hinner.cexp
    simpa using h
  -- the corrected function A
  have hAcont : Continuous (fun z : ℂ => G z - G 1 - (c / Complex.I) * (z - 1)) := by
    have h1 : Continuous (fun z : ℂ => G z - G 1) := hGcont.sub continuous_const
    have h2 : Continuous (fun z : ℂ => (c / Complex.I) * (z - 1)) :=
      Continuous.const_mul (continuous_id.sub continuous_const) _
    exact h1.sub h2
  have hA : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun z : ℂ => G z - G 1 - (c / Complex.I) * (z - 1))
        (g z - c / Complex.I) z := by
    intro z hz
    have h1 := (hG z hz).sub_const (G 1)
    have h2 : HasDerivAt (fun z : ℂ => (c / Complex.I) * (z - 1))
        ((c / Complex.I) * 1) z :=
      ((hasDerivAt_id z).sub_const 1).const_mul (c / Complex.I)
    have h := h1.sub h2
    have ederiv : g z - (c / Complex.I) * 1 = g z - c / Complex.I := by rw [mul_one]
    rw [ederiv] at h
    exact h
  -- boundary function ψ and its derivative 0 at 0
  have hψ : HasDerivAt
      (fun t : ℝ => G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
        - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1))
      (c - (c / Complex.I) * Complex.I) 0 :=
    (hφ.sub_const (G 1)).sub (((he.sub_const 1).const_mul (c / Complex.I)))
  have hcI : c - (c / Complex.I) * Complex.I = 0 := by
    rw [div_mul_cancel₀ c Complex.I_ne_zero, sub_self]
  rw [hcI] at hψ
  have he0 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  have hψ0val : G (Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - G 1
      - (c / Complex.I) * (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) - 1) = 0 := by
    rw [he0]; ring
  -- little-o in ε-δ form
  have hlittle : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ‖G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
        - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1)‖
        ≤ ε * |t| := by
    intro ε hε
    have hiso := hψ.isLittleO
    have hfn : (fun t : ℝ => (G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
        - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1))
        - (G (Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) - G 1
        - (c / Complex.I) * (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) - 1))
        - (t - 0) • (0 : ℂ))
        = (fun t : ℝ => G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
          - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
      funext t
      rw [hψ0val]
      simp
    rw [hfn] at hiso
    have hae := hiso.def hε
    rw [Metric.eventually_nhds_iff] at hae
    obtain ⟨δ, hδpos, hδ⟩ := hae
    refine ⟨δ, hδpos, fun t ht => ?_⟩
    have hdist : dist t 0 < δ := by rwa [Real.dist_eq, sub_zero]
    have h2 := hδ hdist
    rwa [sub_zero, Real.norm_eq_abs] at h2
  -- global Lipschitz bound
  have hKex : ∃ K' : ℝ, ∀ t : ℝ, |t| ≤ Real.pi →
      ‖G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
        - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1)‖
        ≤ K' * |t| := by
    refine ⟨(K : ℝ) + ‖c / Complex.I‖, fun t ht => ?_⟩
    have hGbd : ‖G (Complex.exp ((t : ℂ) * Complex.I)) - G 1‖
        ≤ (K : ℝ) * ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ := by
      have h := hGlip.dist_le_mul (Complex.exp ((t : ℂ) * Complex.I)) 1
      rwa [dist_eq_norm, dist_eq_norm] at h
    have he1 : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
      have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
      have e : ((t : ℂ) * Complex.I) = Complex.I * (t : ℂ) := mul_comm _ _
      rw [e, ← Real.norm_eq_abs]
      exact h
    have hdecomp : ‖G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
          - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1)‖
        ≤ ‖G (Complex.exp ((t : ℂ) * Complex.I)) - G 1‖
          + ‖c / Complex.I‖ * ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ := by
      have h1 := norm_sub_le
        (G (Complex.exp ((t : ℂ) * Complex.I)) - G 1)
        ((c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1))
      rwa [norm_mul] at h1
    have hnn : (0 : ℝ) ≤ (K : ℝ) + ‖c / Complex.I‖ := by positivity
    calc ‖G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
            - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1)‖
          ≤ ‖G (Complex.exp ((t : ℂ) * Complex.I)) - G 1‖
            + ‖c / Complex.I‖ * ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ :=
            hdecomp
        _ ≤ (K : ℝ) * ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖
            + ‖c / Complex.I‖ * ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ :=
            add_le_add hGbd le_rfl
        _ = ((K : ℝ) + ‖c / Complex.I‖)
            * ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ := by ring
        _ ≤ ((K : ℝ) + ‖c / Complex.I‖) * |t| :=
            mul_le_mul_of_nonneg_left he1 hnn
  obtain ⟨K', hKb⟩ := hKex
  have hψcont : Continuous (fun t : ℝ => G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
      - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
    apply Continuous.sub
    · apply Continuous.sub
      · apply hGcont.comp
        apply Complex.continuous_exp.comp
        exact Complex.continuous_ofReal.mul continuous_const
      · exact continuous_const
    · apply Continuous.const_mul
      apply Continuous.sub
      · apply Complex.continuous_exp.comp
        exact Complex.continuous_ofReal.mul continuous_const
      · exact continuous_const
  have hlim0 : Filter.Tendsto (fun r : ℝ => ∫ t in (-Real.pi)..Real.pi,
      ((fatouKernel r t : ℂ)
        * (G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
          - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1))))
      (𝓝[<] (1 : ℝ)) (𝓝 0) :=
    poisson_deriv_integral_tendsto_zero hψcont hKb hlittle
  have hlim : Filter.Tendsto (fun r : ℝ => g ((r : ℂ)) - c / Complex.I)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hev : (fun r : ℝ => g ((r : ℂ)) - c / Complex.I) =ᶠ[𝓝[<] (1 : ℝ)]
        (fun r : ℝ => -(Complex.I / (Real.pi : ℂ)) * ∫ t in (-Real.pi)..Real.pi,
          ((fatouKernel r t : ℂ)
            * (G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
              - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1)))) := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      exact deriv_eq_poisson_deriv_integral hAcont hA hr.1 hr.2
    have h0 : Filter.Tendsto (fun r : ℝ => -(Complex.I / (Real.pi : ℂ))
        * ∫ t in (-Real.pi)..Real.pi, ((fatouKernel r t : ℂ)
          * (G (Complex.exp ((t : ℂ) * Complex.I)) - G 1
            - (c / Complex.I) * (Complex.exp ((t : ℂ) * Complex.I) - 1))))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have hcc := hlim0.const_mul (-(Complex.I / (Real.pi : ℂ)))
      simpa using hcc
    exact Filter.Tendsto.congr' hev.symm h0
  have hfin : Filter.Tendsto (fun r : ℝ => (g ((r : ℂ)) - c / Complex.I) + c / Complex.I)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 + c / Complex.I)) :=
    hlim.add tendsto_const_nhds
  simpa using hfin
private theorem rotate_lipschitz_primitive
    {G f : ℂ → ℂ} {K : NNReal} (hG : LipschitzWith K G)
    (hf : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt G (f z) z)
    {θ : ℝ} {ω : ℂ} (hω : ω = Complex.exp ((θ : ℂ) * Complex.I)) :
    (LipschitzWith K (fun z => G (ω * z)))
    ∧ (∀ z ∈ Metric.ball (0 : ℂ) 1,
        HasDerivAt (fun z => G (ω * z)) (ω * f (ω * z)) z)
    ∧ (DifferentiableAt ℝ (fun (t : ℝ) => G (Complex.exp ((t : ℂ) * Complex.I))) θ →
        HasDerivAt (fun t : ℝ => G (ω * Complex.exp ((t : ℂ) * Complex.I)))
          (deriv (fun (t : ℝ) => G (Complex.exp ((t : ℂ) * Complex.I))) θ) 0) := by
  have hω1 : ‖ω‖ = 1 := by
    rw [hω]
    exact Complex.norm_exp_ofReal_mul_I θ
  have hdist : ∀ x y : ℂ, dist (ω * x) (ω * y) = dist x y := by
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hω1, one_mul]
  have hrot : LipschitzWith 1 (fun z : ℂ => ω * z) := by
    intro x y
    simp only [edist_dist]
    rw [hdist]
    simp
  have hcomp := hG.comp hrot
  have eK : K * 1 = K := mul_one K
  rw [eK] at hcomp
  have efun : (G ∘ (fun z : ℂ => ω * z)) = (fun z : ℂ => G (ω * z)) := rfl
  rw [efun] at hcomp
  have hmem : ∀ z ∈ Metric.ball (0 : ℂ) 1, ω * z ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hω1, one_mul]
    have h := Metric.mem_ball.mp hz
    rwa [dist_zero_right] at h
  have hii : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun z => G (ω * z)) (ω * f (ω * z)) z := by
    intro z hz
    have hchain := (hf (ω * z) (hmem z hz)).comp z
      ((hasDerivAt_id z).const_mul ω)
    have efun2 : (G ∘ HMul.hMul ω) = (fun z : ℂ => G (ω * z)) := rfl
    have ederiv : f (ω * z) * (ω * 1) = ω * f (ω * z) := by ring
    rw [efun2, ederiv] at hchain
    exact hchain
  have hiii : ∀ hφ : DifferentiableAt ℝ
        (fun (t : ℝ) => G (Complex.exp ((t : ℂ) * Complex.I))) θ,
      HasDerivAt (fun t : ℝ => G (ω * Complex.exp ((t : ℂ) * Complex.I)))
        (deriv (fun (t : ℝ) => G (Complex.exp ((t : ℂ) * Complex.I))) θ) 0 := by
    intro hφ
    have hexp : ∀ t : ℝ, ω * Complex.exp ((t : ℂ) * Complex.I)
        = Complex.exp ((((θ + t : ℝ)) : ℂ) * Complex.I) := by
      intro t
      rw [hω, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hh₂ : HasDerivAt (fun (t : ℝ) => G (Complex.exp ((t : ℂ) * Complex.I)))
        (deriv (fun (t : ℝ) => G (Complex.exp ((t : ℂ) * Complex.I))) θ) (θ + 0) := by
      rw [add_zero]
      exact hφ.hasDerivAt
    have hder := HasDerivAt.comp_const_add θ 0 hh₂
    have hev : (fun t : ℝ => G (ω * Complex.exp ((t : ℂ) * Complex.I)))
        =ᶠ[𝓝 (0 : ℝ)]
        (fun x : ℝ => (fun (t : ℝ) => G (Complex.exp ((t : ℂ) * Complex.I))) (θ + x)) :=
      Filter.Eventually.of_forall (fun t => by
        change G (ω * Complex.exp ((t : ℂ) * Complex.I))
          = G (Complex.exp ((((θ + t : ℝ)) : ℂ) * Complex.I))
        rw [hexp t])
    exact hder.congr_of_eventuallyEq hev
  exact ⟨hcomp, hii, hiii⟩
/--
**Fatou's theorem on radial limits.** Let $f : \mathbb{C} \to \mathbb{C}$ be holomorphic and
bounded on the open unit disc $|z| < 1$. Then for Lebesgue-almost every $\theta \in [0, 2\pi]$ the
radial limit $\lim_{r \to 1^-} f(r e^{i\theta})$ exists in $\mathbb{C}$.

Source: Fatou radial limit theorem for H∞, P. Fatou, Acta Math. 30
(1906); see Rudin, Real and Complex Analysis, Bounded Analytic Functions; Lean is bounded
holomorphic on ball 0 1 with a.e. radial limit via volume.restrict Icc 0 (2π) and 𝓝[<] 1.

Proves `Wanted` entry `fatou_radial_limit`.
-/
theorem fatou_radial_limit
    (f : ℂ → ℂ)
    (hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_bdd : ∃ M : ℝ, ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ M) :
    ∀ᵐ θ : ℝ ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))),
      ∃ L : ℂ,
        Filter.Tendsto (fun r : ℝ =>
          f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (𝓝[<] (1 : ℝ)) (𝓝 L) := by
  obtain ⟨M, hM⟩ := hf_bdd
  obtain ⟨G, K, hGlip, hG⟩ := exists_lipschitz_primitive_on_unit_disc f hf_diff hM
  have hae := ae_differentiableAt_circle_comp hGlip
  have hrest : ∀ᵐ θ : ℝ ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))),
      DifferentiableAt ℝ (fun t : ℝ => G (Complex.exp ((t : ℂ) * Complex.I))) θ :=
    ae_restrict_of_ae hae
  filter_upwards [hrest] with θ hθ
  set ω := Complex.exp ((θ : ℂ) * Complex.I) with hωdef
  have hω : ω = Complex.exp ((θ : ℂ) * Complex.I) := rfl
  have hω0 : ω ≠ 0 := by rw [hω]; exact Complex.exp_ne_zero _
  obtain ⟨hGθlip, hGθ, hGθφ⟩ := rotate_lipschitz_primitive hGlip hG hω
  have hder := hGθφ hθ
  have hlim := radial_limit_at_one_of_hasDerivAt_boundary hGθlip hGθ hder
  refine ⟨ω⁻¹ * (deriv (fun (t : ℝ) =>
    G (Complex.exp ((t : ℂ) * Complex.I))) θ / Complex.I), ?_⟩
  have hmul := hlim.const_mul (ω⁻¹)
  apply Filter.Tendsto.congr _ hmul
  intro r
  change ω⁻¹ * ((fun z : ℂ => ω * f (ω * z)) ((r : ℂ))) = f ((r : ℂ) * ω)
  change ω⁻¹ * (ω * f (ω * ((r : ℂ)))) = f ((r : ℂ) * ω)
  rw [← mul_assoc, inv_mul_cancel₀ hω0, one_mul, mul_comm ω ((r : ℂ))]

end MathlibExt.Analysis.Complex.FatouRadialWanted
end
