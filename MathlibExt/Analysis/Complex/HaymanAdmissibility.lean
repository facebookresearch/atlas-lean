/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Hayman's admissibility theorem for asymptotic coefficients.
-- Source: Ljuben Mutafchiev, "The Limiting Distribution of the Hook Length
-- of a Randomly Chosen Cell in a Random Young Diagram", arXiv:1906.07169v2,
-- reproducing the Flajolet-Sedgewick Chapter VIII.5 formulation (Hayman 1956).
-- Auxiliary functions and admissibility conditions: tex lines 453-493;
-- coefficient theorem: tex lines 495-506.

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Hayman's coefficient asymptotic

This file defines finite-radius Hayman admissibility and proves the associated saddle-point
coefficient asymptotic. The proof uses Cauchy's coefficient formula for power series on a disk
and the asymptotic of truncated Gaussian integrals.
-/

set_option autoImplicit false

@[expose] public section

open scoped ENNReal NNReal

namespace MetaMathlibExt

open Asymptotics Filter MeasureTheory Metric Set
open scoped Interval Real Topology

/-- **Hayman auxiliary function $A$.** For a function $G : \mathbb{C} \to \mathbb{C}$ and a real
number $r$, $A(r)$ is the real part of $r\,G'(r)/G(r)$, where $G'$ is the complex derivative of
$G$. -/
noncomputable def haymanAuxiliaryA (G : ℂ → ℂ) (r : ℝ) : ℝ :=
  Complex.re (((r : ℂ) * deriv G (r : ℂ) / G (r : ℂ)))

/-- **Hayman auxiliary function $B$.** For a function $G : \mathbb{C} \to \mathbb{C}$ and a real
number $r$, $B(r) = r\,A'(r)$, where $A$ is the Hayman auxiliary function of $G$, viewed as a
real function of $r$, and $A'$ is its derivative. -/
noncomputable def haymanAuxiliaryB (G : ℂ → ℂ) (r : ℝ) : ℝ :=
  r * deriv (haymanAuxiliaryA G) r

/-- **Hayman-admissible function (finite radius).** Let $G : \mathbb{C} \to \mathbb{C}$, let
$R_0$ and $\rho$ be real numbers, write $G'$ for the complex derivative of $G$ and $A$, $B$ for
the Hayman auxiliary functions of $G$, and say that a property holds for $r$ near $\rho$ if there
is $\eta > 0$ such that it holds for every $r \in (R_0, \rho)$ with $r > \rho - \eta$. Then $G$ is
Hayman admissible on $(R_0, \rho)$ when $0 < R_0 < \rho$; $G$ is analytic on the open disk
$|z| < \rho$; for every $r \in (R_0, \rho)$, $G(r)$ is a positive real number and
$r\,G'(r)/G(r)$ is real; $A(r) \to \infty$ and $B(r) \to \infty$ as $r$ tends to $\rho$ within
$(R_0, \rho)$; and there is a function $\delta : \mathbb{R} \to \mathbb{R}$ with
$0 < \delta(r) < \pi$ for $r$ near $\rho$ such that for every $\varepsilon > 0$ and all $r$ near
$\rho$, every real $\theta$ with $|\theta| \le \delta(r)$ satisfies the locality estimate
$$\left|G(re^{i\theta}) - G(r)\,e^{i\theta A(r) - \theta^2 B(r)/2}\right|
\le \varepsilon \left|G(r)\,e^{i\theta A(r) - \theta^2 B(r)/2}\right|,$$
and every real $\theta$ with $\delta(r) \le |\theta| < \pi$ satisfies the decay estimate
$|G(re^{i\theta})| \le \varepsilon\,|G(r)|/\sqrt{B(r)}$.

The capture, locality and decay conditions follow the Flajolet-Sedgewick formulation rather than
the abbreviated maximum-modulus restatement (Jiyou Li, "Asymptotic Estimate for the Multinomial
Coefficients", Journal of Integer Sequences 23 (2020), Article 20.1.3, Lemma [Hayman] `lem2`),
whose maximum-modulus condition is insufficient as stated and is not used. -/
noncomputable def IsHaymanAdmissible (G : ℂ → ℂ) (R0 ρ : ℝ) : Prop :=
  0 < R0 ∧ R0 < ρ ∧
  AnalyticOn ℂ G (Metric.ball (0 : ℂ) ρ) ∧
  (∀ r ∈ Set.Ioo R0 ρ,
    0 < Complex.re (G (r : ℂ)) ∧ Complex.im (G (r : ℂ)) = 0 ∧
    Complex.im (((r : ℂ) * deriv G (r : ℂ) / G (r : ℂ))) = 0) ∧
  Filter.Tendsto (fun r => haymanAuxiliaryA G r)
    (nhdsWithin ρ (Set.Ioo R0 ρ)) Filter.atTop ∧
  Filter.Tendsto (fun r => haymanAuxiliaryB G r)
    (nhdsWithin ρ (Set.Ioo R0 ρ)) Filter.atTop ∧
  ∃ δ : ℝ → ℝ,
    Filter.Eventually (fun r => 0 < δ r ∧ δ r < Real.pi)
      (nhdsWithin ρ (Set.Ioo R0 ρ)) ∧
    (∀ ε : ℝ, 0 < ε →
      Filter.Eventually
        (fun r => ∀ θ : ℝ, |θ| ≤ δ r →
          ‖G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            G (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) *
              (haymanAuxiliaryA G r : ℂ) -
              ((θ ^ 2 * haymanAuxiliaryB G r / 2 : ℝ) : ℂ))‖ ≤
          ε * ‖G (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) *
            (haymanAuxiliaryA G r : ℂ) -
            ((θ ^ 2 * haymanAuxiliaryB G r / 2 : ℝ) : ℂ))‖)
        (nhdsWithin ρ (Set.Ioo R0 ρ))) ∧
    (∀ ε : ℝ, 0 < ε →
      Filter.Eventually
        (fun r => ∀ θ : ℝ, δ r ≤ |θ| → |θ| < Real.pi →
          ‖G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤
          ε * (‖G (r : ℂ)‖ / Real.sqrt (haymanAuxiliaryB G r)))
        (nhdsWithin ρ (Set.Ioo R0 ρ)))

private theorem hayman_powerSeries_coefficient_eq_circleIntegral
    (G : ℂ → ℂ) (coeff : ℕ → ℂ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r < ρ)
    (hsum : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => coeff n * z ^ n) (G z))
    (n : ℕ) :
    coeff n = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∮ z in C(0, r), z ^ (-(n : ℤ) - 1) * G z := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ coeff
  let R : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hp_radius : (R : ℝ≥0∞) ≤ p.radius := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro s hs
    have hsρ : (s : ℝ) < ρ := by
      have hsR : s < R := by exact_mod_cast hs
      exact_mod_cast hsR
    have ht := (hsum (s : ℂ) (by simpa using hsρ)).summable.tendsto_atTop_zero.norm
    apply p.le_radius_of_tendsto
    simpa [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, abs_of_nonneg s.coe_nonneg]
      using ht
  have hp : HasFPowerSeriesOnBall G p 0 R := by
    refine { r_le := hp_radius, r_pos := ENNReal.coe_pos.2 hρ, hasSum := ?_ }
    intro z hz
    have hzρ : ‖z‖ < ρ := by
      have hzR : ‖z‖₊ < R := by
        simpa only [mem_eball_zero_iff, enorm_lt_coe] using hz
      exact_mod_cast hzR
    simpa [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      hsum z hzρ
  let rnn : ℝ≥0 := ⟨r, hr.le⟩
  have hd : DifferentiableOn ℂ G (Metric.closedBall 0 r) := by
    apply hp.differentiableOn.mono
    intro z hz
    have hzr : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall] using hz
    have hzR : ‖z‖₊ < R := by
      exact_mod_cast hzr.trans_lt hrρ
    simpa only [mem_eball_zero_iff, enorm_lt_coe] using hzR
  have hrnn : 0 < rnn := by exact_mod_cast hr
  have hc := hd.hasFPowerSeriesOnBall (R := rnn) hrnn
  have heq : p = cauchyPowerSeries G 0 r :=
    hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hc.hasFPowerSeriesAt
  have hcoeff := congrArg
    (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n fun _ => (1 : ℂ)) heq
  simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, one_pow, mul_one,
    cauchyPowerSeries_apply] at hcoeff
  rw [hcoeff]
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    have hzero : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hz
    exact hr.ne' hzero.symm
  simp only [sub_zero, one_div]
  rw [← zpow_natCast, inv_zpow, ← zpow_neg, ← zpow_neg_one, ← mul_assoc,
    ← zpow_add₀ hz0]
  congr 2

private theorem hayman_circleIntegral_eq_intervalIntegral
    (G : ℂ → ℂ) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (∮ z in C(0, r), z ^ (-(n : ℤ) - 1) * G z) =
      (Complex.I * (r : ℂ) ^ (-(n : ℤ))) *
        ∫ θ : ℝ in 0..2 * Real.pi,
          G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) := by
  rw [circleIntegral]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [deriv_circleMap, circleMap, zero_add, smul_eq_mul]
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he0 : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hz0 : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero hr0 he0
  have hreduce :
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (-(n : ℤ) - 1) =
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (-(n : ℤ)) := by
    calc
      _ = ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (1 : ℤ) *
          ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (-(n : ℤ) - 1) := by
        rw [zpow_one]
      _ = ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^
          ((1 : ℤ) + (-(n : ℤ) - 1)) := (zpow_add₀ hz0 _ _).symm
      _ = _ := by
        congr 1
        ring_nf
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) ^ (-(n : ℤ)) =
      Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) := by
    rw [← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  calc
    _ = Complex.I * (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (-(n : ℤ) - 1)) *
        G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by ring
    _ = Complex.I * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (-(n : ℤ)) *
        G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by rw [hreduce]
    _ = _ := by rw [mul_zpow, hexp]; ring_nf

private theorem hayman_angular_integral_periodic
    (G : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    (∫ θ : ℝ in 0..2 * Real.pi,
      G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ)))) =
    ∫ θ : ℝ in -Real.pi..Real.pi,
      G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) := by
  let F : ℝ → ℂ := fun θ =>
    G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ)))
  have hF : Function.Periodic F (2 * Real.pi) := by
    intro θ
    dsimp [F]
    have hcircle : Complex.exp (Complex.I * ((θ + 2 * Real.pi : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [show Complex.I * ((θ + 2 * Real.pi : ℝ) : ℂ) =
        Complex.I * (θ : ℂ) + 2 * Real.pi * Complex.I by
          push_cast
          ring]
      exact Complex.exp_periodic _
    rw [hcircle]
    congr 1
    rw [show -(Complex.I * ((θ + 2 * Real.pi : ℝ) : ℂ) * (n : ℂ)) =
      -(Complex.I * (θ : ℂ) * (n : ℂ)) + (-(n : ℤ) : ℂ) *
        (2 * Real.pi * Complex.I) by
        push_cast
        ring]
    rw [Complex.exp_add]
    have hnexp : Complex.exp ((-(n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
      simpa using Complex.exp_int_mul_two_pi_mul_I (-(n : ℤ))
    rw [hnexp, mul_one]
  change (∫ θ : ℝ in 0..2 * Real.pi, F θ) = ∫ θ : ℝ in -Real.pi..Real.pi, F θ
  convert hF.intervalIntegral_add_eq 0 (-Real.pi) using 1 <;> ring_nf

private theorem hayman_powerSeries_coefficient_eq_intervalIntegral
    (G : ℂ → ℂ) (coeff : ℕ → ℂ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r < ρ)
    (hsum : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => coeff n * z ^ n) (G z))
    (n : ℕ) :
    coeff n = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (r : ℂ) ^ (-(n : ℤ)) *
      ∫ θ : ℝ in -Real.pi..Real.pi,
        G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) := by
  rw [hayman_powerSeries_coefficient_eq_circleIntegral G coeff hρ hr hrρ hsum n,
    hayman_circleIntegral_eq_intervalIntegral G r hr n,
    hayman_angular_integral_periodic G r n]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hconst : (2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ := by
    field_simp
    push_cast
    ring
  calc
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) *
        (r : ℂ) ^ (-(n : ℤ)) *
          ∫ θ : ℝ in -Real.pi..Real.pi,
            G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) := by ring
    _ = _ := by rw [hconst]

private theorem hayman_auxiliaryA_continuousOn
    {G : ℂ → ℂ} {R0 ρ : ℝ} (hR0 : 0 < R0)
    (hG : AnalyticOn ℂ G (ball (0 : ℂ) ρ))
    (hpos : ∀ r ∈ Ioo R0 ρ, 0 < Complex.re (G (r : ℂ))) :
    ContinuousOn (haymanAuxiliaryA G) (Ioo R0 ρ) := by
  have hGn : AnalyticOnNhd ℂ G (ball (0 : ℂ) ρ) :=
    isOpen_ball.analyticOn_iff_analyticOnNhd.mp hG
  have hDn : AnalyticOnNhd ℂ (deriv G) (ball (0 : ℂ) ρ) :=
    hGn.deriv_of_isOpen isOpen_ball
  intro r hr
  apply ContinuousAt.continuousWithinAt
  have hrpos : 0 < r := hR0.trans hr.1
  have hrball : (r : ℂ) ∈ ball (0 : ℂ) ρ := by
    simpa [mem_ball, abs_of_pos hrpos] using hr.2
  have hcast : ContinuousAt (fun x : ℝ => (x : ℂ)) r :=
    Complex.continuous_ofReal.continuousAt
  have hGc : ContinuousAt (fun x : ℝ => G (x : ℂ)) r := by
    simpa [Function.comp_def] using (hGn (r : ℂ) hrball).continuousAt.comp hcast
  have hDc : ContinuousAt (fun x : ℝ => deriv G (x : ℂ)) r := by
    simpa [Function.comp_def] using (hDn (r : ℂ) hrball).continuousAt.comp hcast
  have hGne : G (r : ℂ) ≠ 0 := by
    intro h
    simpa [h] using hpos r hr
  unfold haymanAuxiliaryA
  simpa [Function.comp_def] using
    Complex.continuous_re.continuousAt.comp ((hcast.mul hDc).div hGc hGne)

private theorem hayman_saddle_tendsto
    {A : ℝ → ℝ} {R0 ρ : ℝ} {saddle : ℕ → ℝ}
    (hRρ : R0 < ρ) (hcont : ContinuousOn A (Ioo R0 ρ))
    (hA : Tendsto A (𝓝[Ioo R0 ρ] ρ) atTop)
    (hsaddle : ∀ᶠ n : ℕ in atTop, saddle n ∈ Ioo R0 ρ ∧ A (saddle n) = (n : ℝ) ∧
      ∀ r ∈ Ioo R0 ρ, A r = (n : ℝ) → r = saddle n) :
    Tendsto saddle atTop (𝓝[Ioo R0 ρ] ρ) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · rw [tendsto_order]
    constructor
    · intro c hc
      have hmax : max c R0 < ρ := max_lt hc hRρ
      obtain ⟨d, hmaxd, hdρ⟩ := exists_between hmax
      have hcd : c < d := (le_max_left c R0).trans_lt hmaxd
      have hR0d : R0 < d := (le_max_right c R0).trans_lt hmaxd
      filter_upwards [hsaddle,
        tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (A d))] with n hn hnd
      let _ : (𝓝[Ioo R0 ρ] ρ).NeBot := right_nhdsWithin_Ioo_neBot hRρ
      have hxd : ∀ᶠ x in 𝓝[Ioo R0 ρ] ρ, d < x :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hdρ)
      have hAx : ∀ᶠ x in 𝓝[Ioo R0 ρ] ρ, (n : ℝ) < A x :=
        hA.eventually (eventually_gt_atTop (n : ℝ))
      have hxI : ∀ᶠ x in 𝓝[Ioo R0 ρ] ρ, x ∈ Ioo R0 ρ := self_mem_nhdsWithin
      obtain ⟨x, hxIoo, hdx, hnx⟩ := (hxI.and (hxd.and hAx)).exists
      have hsub : Icc d x ⊆ Ioo R0 ρ := by
        intro y hy
        exact ⟨hR0d.trans_le hy.1, hy.2.trans_lt hxIoo.2⟩
      obtain ⟨y, hyIcc, hyA⟩ :=
        intermediate_value_Icc hdx.le (hcont.mono hsub) ⟨hnd.le, hnx.le⟩
      have hdy : d < y := by
        apply lt_of_le_of_ne hyIcc.1
        intro hdy
        subst y
        linarith
      have hyIoo := hsub hyIcc
      have hysaddle : y = saddle n := hn.2.2 y hyIoo hyA
      simpa [← hysaddle] using hcd.trans hdy
    · intro c hc
      filter_upwards [hsaddle] with n hn
      exact hn.1.2.trans hc
  · exact hsaddle.mono fun _ hn => hn.1

private theorem hayman_scaled_cutoff_tendsto_of_bound
    {α : Type*} {l : Filter α} (B δ : α → ℝ)
    (hB : Tendsto B l atTop) (hδ : ∀ᶠ a in l, 0 < δ a)
    (hbound : ∀ᶠ a in l,
      Real.sqrt (B a) * Real.exp (-(δ a ^ 2 * B a / 2)) ≤ 2) :
    Tendsto (fun a => δ a * Real.sqrt (B a)) l atTop := by
  apply Filter.tendsto_atTop.2
  intro K
  let q : ℝ := 2 * Real.exp (K ^ 2 / 2) + 1
  filter_upwards [hδ, hbound, hB.eventually (eventually_gt_atTop (q ^ 2))] with
    a hδa hba hBq
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hB0 : 0 < B a := lt_of_le_of_lt (sq_nonneg q) hBq
  have hsqrt : q < Real.sqrt (B a) := (Real.lt_sqrt hq).2 hBq
  have hsqrt0 : 0 < Real.sqrt (B a) := Real.sqrt_pos.2 hB0
  have hT0 : 0 ≤ δ a * Real.sqrt (B a) := mul_nonneg hδa.le hsqrt0.le
  by_contra hTK
  have hTK' : δ a * Real.sqrt (B a) ≤ K := (lt_of_not_ge hTK).le
  have hK0 : 0 ≤ K := hT0.trans hTK'
  have hsq : δ a ^ 2 * B a ≤ K ^ 2 := by
    have heq : (δ a * Real.sqrt (B a)) ^ 2 = δ a ^ 2 * B a := by
      rw [mul_pow, Real.sq_sqrt hB0.le]
    nlinarith
  have hexp : Real.exp (-(K ^ 2 / 2)) ≤
      Real.exp (-(δ a ^ 2 * B a / 2)) := by
    rw [Real.exp_le_exp]
    linarith
  have hlarge : 2 * Real.exp (K ^ 2 / 2) < Real.sqrt (B a) := by
    dsimp [q] at hsqrt
    linarith
  have hprod : Real.exp (K ^ 2 / 2) * Real.exp (-(K ^ 2 / 2)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have htwo : 2 < Real.sqrt (B a) * Real.exp (-(K ^ 2 / 2)) := by
    calc
      2 = (2 * Real.exp (K ^ 2 / 2)) * Real.exp (-(K ^ 2 / 2)) := by
        rw [mul_assoc, hprod, mul_one]
      _ < _ := mul_lt_mul_of_pos_right hlarge (Real.exp_pos _)
  have hle : Real.sqrt (B a) * Real.exp (-(K ^ 2 / 2)) ≤
      Real.sqrt (B a) * Real.exp (-(δ a ^ 2 * B a / 2)) :=
    mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg (B a))
  exact (not_lt_of_ge (hle.trans hba)) htwo

private theorem hayman_cutoff_scaled_tendsto
    {G : ℂ → ℂ} {R0 ρ : ℝ} {δ : ℝ → ℝ}
    (hpos : ∀ r ∈ Ioo R0 ρ, 0 < Complex.re (G (r : ℂ)))
    (hB : Tendsto (haymanAuxiliaryB G) (𝓝[Ioo R0 ρ] ρ) atTop)
    (hδ : ∀ᶠ r in 𝓝[Ioo R0 ρ] ρ, 0 < δ r ∧ δ r < Real.pi)
    (hloc : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r in 𝓝[Ioo R0 ρ] ρ, ∀ θ : ℝ, |θ| ≤ δ r →
        ‖G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          G (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) *
            (haymanAuxiliaryA G r : ℂ) -
            ((θ ^ 2 * haymanAuxiliaryB G r / 2 : ℝ) : ℂ))‖ ≤
        ε * ‖G (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) *
          (haymanAuxiliaryA G r : ℂ) -
          ((θ ^ 2 * haymanAuxiliaryB G r / 2 : ℝ) : ℂ))‖)
    (hdecay : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r in 𝓝[Ioo R0 ρ] ρ, ∀ θ : ℝ, δ r ≤ |θ| → |θ| < Real.pi →
        ‖G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤
        ε * (‖G (r : ℂ)‖ / Real.sqrt (haymanAuxiliaryB G r))) :
    Tendsto (fun r => δ r * Real.sqrt (haymanAuxiliaryB G r))
      (𝓝[Ioo R0 ρ] ρ) atTop := by
  apply hayman_scaled_cutoff_tendsto_of_bound _ _ hB (hδ.mono fun _ h => h.1)
  filter_upwards [self_mem_nhdsWithin, hB.eventually (eventually_gt_atTop 0), hδ,
    hloc (1 / 2) (by norm_num), hdecay 1 zero_lt_one] with r hrI hrB hrδ hrloc hrdec
  let point : ℂ := G ((r : ℂ) * Complex.exp (Complex.I * (δ r : ℂ)))
  let model : ℂ := G (r : ℂ) * Complex.exp (Complex.I * (δ r : ℂ) *
    (haymanAuxiliaryA G r : ℂ) -
    ((δ r ^ 2 * haymanAuxiliaryB G r / 2 : ℝ) : ℂ))
  have hlocδ : ‖point - model‖ ≤ (1 / 2 : ℝ) * ‖model‖ := by
    apply hrloc (δ r)
    simp [abs_of_pos hrδ.1]
  have hdecδ : ‖point‖ ≤ ‖G (r : ℂ)‖ / Real.sqrt (haymanAuxiliaryB G r) := by
    simpa [point, abs_of_pos hrδ.1] using
      hrdec (δ r) (by simp [abs_of_pos hrδ.1])
        (by simpa [abs_of_pos hrδ.1] using hrδ.2)
  have hmodel : ‖model‖ = ‖G (r : ℂ)‖ *
      Real.exp (-(δ r ^ 2 * haymanAuxiliaryB G r / 2)) := by
    dsimp [model]
    rw [norm_mul, Complex.norm_exp]
    rw [show (Complex.I * (δ r : ℂ) * (haymanAuxiliaryA G r : ℂ) -
      ((δ r ^ 2 * haymanAuxiliaryB G r / 2 : ℝ) : ℂ)).re =
        -(δ r ^ 2 * haymanAuxiliaryB G r / 2) by
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring]
  have htri : ‖model‖ ≤ ‖point - model‖ + ‖point‖ := by
    calc
      ‖model‖ = ‖-(point - model) + point‖ := by
        congr 1
        ring
      _ ≤ ‖-(point - model)‖ + ‖point‖ := norm_add_le _ _
      _ = ‖point - model‖ + ‖point‖ := by rw [norm_neg]
  have hlower : (1 / 2 : ℝ) * ‖model‖ ≤ ‖point‖ := by linarith
  have hGne : G (r : ℂ) ≠ 0 := by
    intro h
    simpa [h] using hpos r hrI
  have hGnorm : 0 < ‖G (r : ℂ)‖ := norm_pos_iff.mpr hGne
  have hsqrt : 0 < Real.sqrt (haymanAuxiliaryB G r) := Real.sqrt_pos.2 hrB
  have hupper : Real.sqrt (haymanAuxiliaryB G r) * ‖point‖ ≤ ‖G (r : ℂ)‖ := by
    calc
      _ ≤ Real.sqrt (haymanAuxiliaryB G r) *
          (‖G (r : ℂ)‖ / Real.sqrt (haymanAuxiliaryB G r)) :=
        mul_le_mul_of_nonneg_left hdecδ hsqrt.le
      _ = _ := by field_simp
  rw [hmodel] at hlower
  have hmain : Real.sqrt (haymanAuxiliaryB G r) *
      ((1 / 2 : ℝ) * (‖G (r : ℂ)‖ *
        Real.exp (-(δ r ^ 2 * haymanAuxiliaryB G r / 2)))) ≤ ‖G (r : ℂ)‖ :=
    (mul_le_mul_of_nonneg_left hlower hsqrt.le).trans hupper
  have hcancel : ‖G (r : ℂ)‖ *
      (Real.sqrt (haymanAuxiliaryB G r) *
        Real.exp (-(δ r ^ 2 * haymanAuxiliaryB G r / 2))) ≤
      ‖G (r : ℂ)‖ * 2 := by
    nlinarith
  exact le_of_mul_le_mul_left hcancel hGnorm

private theorem hayman_gaussian_scaled_tendsto
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (b δ : α → ℝ) (hb : Tendsto b l atTop)
    (hδ : ∀ᶠ a in l, 0 ≤ δ a)
    (hscale : Tendsto (fun a => δ a * Real.sqrt (b a)) l atTop) :
    Tendsto
      (fun a => Real.sqrt (b a) *
        ∫ x : ℝ in -δ a..δ a, Real.exp (-(b a / 2) * x ^ 2))
      l (𝓝 (Real.sqrt (2 * Real.pi))) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(1 / 2 : ℝ) * x ^ 2)
  let T : α → ℝ := fun a => δ a * Real.sqrt (b a)
  have hf : Integrable f := by
    simpa [f] using integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  have hJ : Tendsto (fun a => ∫ x : ℝ in -T a..T a, f x) l
      (𝓝 (Real.sqrt (2 * Real.pi))) := by
    have h := intervalIntegral_tendsto_integral hf
      (tendsto_neg_atTop_atBot.comp hscale) hscale
    have hinter : (∫ x : ℝ, f x) = Real.sqrt (2 * Real.pi) := by
      change (∫ x : ℝ, Real.exp (-(1 / 2 : ℝ) * x ^ 2)) = _
      rw [integral_gaussian]
      congr 1
      ring
    rw [hinter] at h
    exact h
  apply hJ.congr'
  filter_upwards [hb.eventually (eventually_gt_atTop 0), hδ] with a hba hδa
  have hsqrt : Real.sqrt (b a) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hba)
  have hchange :
      (∫ x : ℝ in -δ a..δ a, Real.exp (-(b a / 2) * x ^ 2)) =
        (Real.sqrt (b a))⁻¹ * ∫ x : ℝ in -T a..T a, f x := by
    convert intervalIntegral.integral_comp_mul_right
      (a := -δ a) (b := δ a) f hsqrt using 1
    · apply intervalIntegral.integral_congr
      intro x _
      simp only [f]
      congr 1
      rw [mul_pow, Real.sq_sqrt hba.le]
      ring
    · simp [T]
  rw [hchange]
  field_simp

private theorem hayman_central_error_scaled_tendsto
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (b δ : α → ℝ) (E : α → ℝ → ℂ)
    (hb : Tendsto b l atTop) (hδ : ∀ᶠ a in l, 0 ≤ δ a)
    (hscale : Tendsto (fun a => δ a * Real.sqrt (b a)) l atTop)
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ a in l, ∀ θ : ℝ, |θ| ≤ δ a →
      ‖E a θ‖ ≤ ε * Real.exp (-(b a / 2) * θ ^ 2)) :
    Tendsto
      (fun a => (Real.sqrt (b a) : ℂ) * ∫ θ : ℝ in -δ a..δ a, E a θ)
      l (𝓝 0) := by
  have hG := hayman_gaussian_scaled_tendsto b δ hb hδ hscale
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C : ℝ := Real.sqrt (2 * Real.pi) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let η : ℝ := ε / C
  have hη : 0 < η := div_pos hε hC
  have hGupper : ∀ᶠ a in l,
      Real.sqrt (b a) *
          (∫ x : ℝ in -δ a..δ a, Real.exp (-(b a / 2) * x ^ 2)) < C := by
    have hnear := (Metric.tendsto_nhds.mp hG) 1 zero_lt_one
    filter_upwards [hnear] with a ha
    rw [Real.dist_eq] at ha
    dsimp [C]
    linarith [le_abs_self
      (Real.sqrt (b a) *
        (∫ x : ℝ in -δ a..δ a, Real.exp (-(b a / 2) * x ^ 2)) -
          Real.sqrt (2 * Real.pi))]
  filter_upwards [hb.eventually (eventually_gt_atTop 0), hδ, hE η hη, hGupper] with
    a hba hδa hEa hGauss
  have hsqrt : 0 ≤ Real.sqrt (b a) := Real.sqrt_nonneg _
  have hInt : ‖∫ θ : ℝ in -δ a..δ a, E a θ‖ ≤
      η * ∫ θ : ℝ in -δ a..δ a, Real.exp (-(b a / 2) * θ ^ 2) := by
    have hbound : IntervalIntegrable
        (fun θ : ℝ => η * Real.exp (-(b a / 2) * θ ^ 2)) volume (-δ a) (δ a) :=
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.pow 2)))).intervalIntegrable _ _
    calc
      _ ≤ ∫ θ : ℝ in -δ a..δ a,
          η * Real.exp (-(b a / 2) * θ ^ 2) := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by linarith) _ hbound
        filter_upwards [] with θ hθ
        apply hEa θ
        rw [abs_le]
        exact ⟨hθ.1.le, hθ.2⟩
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hsqrt]
  calc
    _ ≤ Real.sqrt (b a) *
        (η * ∫ θ : ℝ in -δ a..δ a, Real.exp (-(b a / 2) * θ ^ 2)) :=
      mul_le_mul_of_nonneg_left hInt hsqrt
    _ = η * (Real.sqrt (b a) *
        ∫ θ : ℝ in -δ a..δ a, Real.exp (-(b a / 2) * θ ^ 2)) := by ring
    _ < η * C := mul_lt_mul_of_pos_left hGauss hη
    _ = ε := div_mul_cancel₀ ε hC.ne'

private theorem hayman_tail_scaled_tendsto
    {α : Type*} {l : Filter α}
    (b δ : α → ℝ) (H : α → ℝ → ℂ)
    (hb : Tendsto b l atTop)
    (hδ : ∀ᶠ a in l, 0 ≤ δ a ∧ δ a < Real.pi)
    (hH : ∀ ε : ℝ, 0 < ε → ∀ᶠ a in l, ∀ θ : ℝ,
      δ a ≤ |θ| → |θ| < Real.pi →
        ‖H a θ‖ ≤ ε / Real.sqrt (b a)) :
    Tendsto
      (fun a => (Real.sqrt (b a) : ℂ) *
        ((∫ θ : ℝ in -Real.pi..-δ a, H a θ) +
          ∫ θ : ℝ in δ a..Real.pi, H a θ))
      l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C : ℝ := 2 * Real.pi + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let η : ℝ := ε / C
  have hη : 0 < η := div_pos hε hC
  filter_upwards [hb.eventually (eventually_gt_atTop 0), hδ, hH η hη] with
    a hba hδa hHa
  have hsqrt : 0 < Real.sqrt (b a) := Real.sqrt_pos.2 hba
  have hconst : 0 ≤ η / Real.sqrt (b a) := (div_pos hη hsqrt).le
  have hleft : ‖∫ θ : ℝ in -Real.pi..-δ a, H a θ‖ ≤
      (η / Real.sqrt (b a)) * Real.pi := by
    have hraw : ‖∫ θ : ℝ in -Real.pi..-δ a, H a θ‖ ≤
        (η / Real.sqrt (b a)) * |-δ a - -Real.pi| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (C := η / Real.sqrt (b a)) (by
          intro θ hθ
          have hI : θ ∈ Ioc (-Real.pi) (-δ a) := by
            simpa [uIoc_of_le (neg_le_neg hδa.2.le)] using hθ
          have hθnonpos : θ ≤ 0 := hI.2.trans (neg_nonpos.2 hδa.1)
          apply hHa θ
          · rw [abs_of_nonpos hθnonpos]
            simpa using neg_le_neg hI.2
          · rw [abs_of_nonpos hθnonpos]
            simpa using neg_lt_neg hI.1)
    calc
      _ ≤ (η / Real.sqrt (b a)) * |-δ a - -Real.pi| := hraw
      _ ≤ _ := by
        rw [abs_of_nonneg (by linarith : 0 ≤ -δ a - -Real.pi)]
        exact mul_le_mul_of_nonneg_left (by linarith [Real.pi_pos]) hconst
  have hright : ‖∫ θ : ℝ in δ a..Real.pi, H a θ‖ ≤
      (η / Real.sqrt (b a)) * Real.pi := by
    have hraw : ‖∫ θ : ℝ in δ a..Real.pi, H a θ‖ ≤
        (η / Real.sqrt (b a)) * |Real.pi - δ a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const_ae
        (C := η / Real.sqrt (b a)) (by
          filter_upwards [volume.ae_ne Real.pi] with θ hne hθ
          have hI : θ ∈ Ioc (δ a) Real.pi := by
            simpa [uIoc_of_le hδa.2.le] using hθ
          have hθnonneg : 0 ≤ θ := hδa.1.trans hI.1.le
          apply hHa θ
          · simpa [abs_of_nonneg hθnonneg] using hI.1.le
          · rw [abs_of_nonneg hθnonneg]
            exact hI.2.lt_of_ne hne)
    calc
      _ ≤ (η / Real.sqrt (b a)) * |Real.pi - δ a| := hraw
      _ ≤ _ := by
        rw [abs_of_nonneg (by linarith [hδa.2.le] : 0 ≤ Real.pi - δ a)]
        exact mul_le_mul_of_nonneg_left (by linarith [Real.pi_pos]) hconst
  have heta : 2 * η * Real.pi < ε := by
    have heq : η * C = ε := div_mul_cancel₀ ε hC.ne'
    dsimp [C] at heq
    linarith
  rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsqrt]
  calc
    _ ≤ Real.sqrt (b a) *
        (‖∫ θ : ℝ in -Real.pi..-δ a, H a θ‖ +
          ‖∫ θ : ℝ in δ a..Real.pi, H a θ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hsqrt.le
    _ ≤ Real.sqrt (b a) *
        ((η / Real.sqrt (b a)) * Real.pi +
          (η / Real.sqrt (b a)) * Real.pi) :=
      mul_le_mul_of_nonneg_left (add_le_add hleft hright) hsqrt.le
    _ = 2 * η * Real.pi := by field_simp; ring
    _ < ε := heta

private theorem hayman_normalized_locality
    (P G0 : ℂ) (θ A B ε : ℝ) (n : ℕ)
    (hG : G0 ≠ 0) (hA : A = (n : ℝ))
    (hloc : ‖P - G0 * Complex.exp
      (Complex.I * (θ : ℂ) * (A : ℂ) - ((θ ^ 2 * B / 2 : ℝ) : ℂ))‖ ≤
      ε * ‖G0 * Complex.exp
        (Complex.I * (θ : ℂ) * (A : ℂ) - ((θ ^ 2 * B / 2 : ℝ) : ℂ))‖) :
    ‖P * Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) / G0 -
      (Real.exp (-(B / 2) * θ ^ 2) : ℂ)‖ ≤
      ε * Real.exp (-(B / 2) * θ ^ 2) := by
  rw [hA] at hloc
  let phase : ℂ := Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ)))
  let q : ℝ := θ ^ 2 * B / 2
  let model : ℂ := G0 * Complex.exp
    (Complex.I * (θ : ℂ) * (n : ℂ) - (q : ℂ))
  have hphase_norm : ‖phase‖ = 1 := by
    dsimp [phase]
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp
  have hmodel_phase : model * phase = G0 * (Real.exp (-q) : ℂ) := by
    dsimp [model, phase]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hid : P * phase / G0 - (Real.exp (-q) : ℂ) =
      (P - model) * phase / G0 := by
    field_simp
    calc
      P * phase - G0 * (Real.exp (-q) : ℂ) = P * phase - model * phase := by
        rw [hmodel_phase]
      _ = phase * (P - model) := by ring
  have hGnorm : ‖G0‖ ≠ 0 := norm_ne_zero_iff.mpr hG
  have hq : -(B / 2) * θ ^ 2 = -q := by
    dsimp [q]
    ring
  rw [hq]
  change ‖P * phase / G0 - (Real.exp (-q) : ℂ)‖ ≤ ε * Real.exp (-q)
  rw [hid, norm_div, norm_mul, hphase_norm, mul_one]
  change ‖P - model‖ / ‖G0‖ ≤ _
  apply (div_le_div_of_nonneg_right (by simpa [model, q] using hloc)
    (norm_nonneg G0)).trans_eq
  rw [Complex.norm_exp]
  simp only [Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  have hpowre : ((θ : ℂ) ^ 2).re = θ ^ 2 := by
    simp [pow_two, Complex.mul_re]
  rw [hpowre]
  dsimp [q]
  field_simp
  congr 2
  ring

private theorem hayman_normalized_decay
    (P G0 phase : ℂ) (B ε : ℝ)
    (hG : G0 ≠ 0) (hB : 0 < B)
    (hdec : ‖P‖ ≤ ε * (‖G0‖ / Real.sqrt B))
    (hphase : ‖phase‖ = 1) :
    ‖P * phase / G0‖ ≤ ε / Real.sqrt B := by
  have hGnorm : 0 < ‖G0‖ := norm_pos_iff.mpr hG
  rw [norm_div, norm_mul, hphase, mul_one]
  apply (div_le_div_of_nonneg_right hdec (norm_nonneg G0)).trans_eq
  have hsqrt : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  field_simp

private theorem hayman_normalized_integral_tendsto
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (b δ : α → ℝ) (H : α → ℝ → ℂ)
    (hb : Tendsto b l atTop)
    (hδ : ∀ᶠ a in l, 0 ≤ δ a ∧ δ a < Real.pi)
    (hscale : Tendsto (fun a => δ a * Real.sqrt (b a)) l atTop)
    (hHcont : ∀ᶠ a in l, Continuous (H a))
    (hcentral : ∀ ε : ℝ, 0 < ε → ∀ᶠ a in l, ∀ θ : ℝ, |θ| ≤ δ a →
      ‖H a θ - (Real.exp (-(b a / 2) * θ ^ 2) : ℂ)‖ ≤
        ε * Real.exp (-(b a / 2) * θ ^ 2))
    (htail : ∀ ε : ℝ, 0 < ε → ∀ᶠ a in l, ∀ θ : ℝ,
      δ a ≤ |θ| → |θ| < Real.pi →
        ‖H a θ‖ ≤ ε / Real.sqrt (b a)) :
    Tendsto
      (fun a => (Real.sqrt (b a) : ℂ) *
        ∫ θ : ℝ in -Real.pi..Real.pi, H a θ)
      l (𝓝 (Real.sqrt (2 * Real.pi) : ℂ)) := by
  have hgauss := hayman_gaussian_scaled_tendsto b δ hb
    (hδ.mono fun _ ha => ha.1) hscale
  have herr := hayman_central_error_scaled_tendsto b δ
    (fun a θ => H a θ - (Real.exp (-(b a / 2) * θ ^ 2) : ℂ)) hb
    (hδ.mono fun _ ha => ha.1) hscale hcentral
  have htail' := hayman_tail_scaled_tendsto b δ H hb hδ htail
  have hgaussC : Tendsto
      (fun a => (Real.sqrt (b a) : ℂ) *
        ∫ x : ℝ in -δ a..δ a, (Real.exp (-(b a / 2) * x ^ 2) : ℂ))
      l (𝓝 (Real.sqrt (2 * Real.pi) : ℂ)) := by
    apply hgauss.ofReal.congr'
    filter_upwards [] with a
    rw [intervalIntegral.integral_ofReal]
    push_cast
    rfl
  have hcentralSum := hgaussC.add herr
  have hcentral' : Tendsto
      (fun a => (Real.sqrt (b a) : ℂ) *
        ∫ θ : ℝ in -δ a..δ a, H a θ)
      l (𝓝 (Real.sqrt (2 * Real.pi) : ℂ)) := by
    simp only [add_zero] at hcentralSum
    apply hcentralSum.congr'
    filter_upwards [hHcont] with a hca
    have hgcont : Continuous (fun θ : ℝ =>
        (Real.exp (-(b a / 2) * θ ^ 2) : ℂ)) := by fun_prop
    have hgint : IntervalIntegrable (fun θ : ℝ =>
        (Real.exp (-(b a / 2) * θ ^ 2) : ℂ)) volume (-δ a) (δ a) :=
      hgcont.intervalIntegrable _ _
    have heint : IntervalIntegrable (fun θ : ℝ =>
        H a θ - (Real.exp (-(b a / 2) * θ ^ 2) : ℂ)) volume (-δ a) (δ a) :=
      (hca.sub hgcont).intervalIntegrable _ _
    rw [← mul_add, ← intervalIntegral.integral_add hgint heint]
    apply congrArg
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  have hsum := htail'.add hcentral'
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hHcont] with a hca
  have hleft : IntervalIntegrable (H a) volume (-Real.pi) (-δ a) :=
    hca.intervalIntegrable _ _
  have hmid : IntervalIntegrable (H a) volume (-δ a) (δ a) :=
    hca.intervalIntegrable _ _
  have hright : IntervalIntegrable (H a) volume (δ a) Real.pi :=
    hca.intervalIntegrable _ _
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hleft hmid
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmid) hright
  calc
    _ = (Real.sqrt (b a) : ℂ) *
        (((∫ θ : ℝ in -Real.pi..-δ a, H a θ) +
          ∫ θ : ℝ in -δ a..δ a, H a θ) +
          ∫ θ : ℝ in δ a..Real.pi, H a θ) := by ring
    _ = (Real.sqrt (b a) : ℂ) *
        ((∫ θ : ℝ in -Real.pi..δ a, H a θ) +
          ∫ θ : ℝ in δ a..Real.pi, H a θ) := by rw [hsplit1]
    _ = _ := by rw [hsplit2]

private theorem hayman_angular_integral_tendsto
    (G : ℂ → ℂ) (saddle : ℕ → ℝ) (δ : ℝ → ℝ)
    (hB : Tendsto (fun n => haymanAuxiliaryB G (saddle n)) atTop atTop)
    (hδ : ∀ᶠ n : ℕ in atTop, 0 < δ (saddle n) ∧ δ (saddle n) < Real.pi)
    (hscale : Tendsto
      (fun n => δ (saddle n) * Real.sqrt (haymanAuxiliaryB G (saddle n)))
      atTop atTop)
    (hGne : ∀ᶠ n : ℕ in atTop, G (saddle n : ℂ) ≠ 0)
    (hA : ∀ᶠ n : ℕ in atTop,
      haymanAuxiliaryA G (saddle n) = (n : ℝ))
    (hcircle : ∀ᶠ n : ℕ in atTop, Continuous (fun θ : ℝ =>
      G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))))
    (hloc : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ,
      |θ| ≤ δ (saddle n) →
        ‖G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          G (saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ) *
            (haymanAuxiliaryA G (saddle n) : ℂ) -
            ((θ ^ 2 * haymanAuxiliaryB G (saddle n) / 2 : ℝ) : ℂ))‖ ≤
        ε * ‖G (saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ) *
          (haymanAuxiliaryA G (saddle n) : ℂ) -
          ((θ ^ 2 * haymanAuxiliaryB G (saddle n) / 2 : ℝ) : ℂ))‖)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ,
      δ (saddle n) ≤ |θ| → |θ| < Real.pi →
        ‖G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤
        ε * (‖G (saddle n : ℂ)‖ /
          Real.sqrt (haymanAuxiliaryB G (saddle n)))) :
    Tendsto
      (fun n => (Real.sqrt (haymanAuxiliaryB G (saddle n)) : ℂ) *
        ∫ θ : ℝ in -Real.pi..Real.pi,
          G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) /
              G (saddle n : ℂ))
      atTop (𝓝 (Real.sqrt (2 * Real.pi) : ℂ)) := by
  let b : ℕ → ℝ := fun n => haymanAuxiliaryB G (saddle n)
  let d : ℕ → ℝ := fun n => δ (saddle n)
  let H : ℕ → ℝ → ℂ := fun n θ =>
    G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) /
        G (saddle n : ℂ)
  apply hayman_normalized_integral_tendsto b d H
  · simpa [b] using hB
  · simpa [d] using hδ.mono fun _ hn => ⟨hn.1.le, hn.2⟩
  · simpa [b, d] using hscale
  · filter_upwards [hcircle] with n hn
    dsimp [H]
    have hcast : Continuous (fun θ : ℝ => (θ : ℂ)) := Complex.continuous_ofReal
    have hphase : Continuous (fun θ : ℝ =>
        Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ)))) :=
      Complex.continuous_exp.comp
        (((continuous_const.mul hcast).mul continuous_const).neg)
    exact (hn.mul hphase).div_const _
  · intro ε hε
    filter_upwards [hGne, hA, hloc ε hε] with n hGn hAn hnloc
    intro θ hθ
    simpa [H, b, d] using hayman_normalized_locality
      (G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (G (saddle n : ℂ)) θ (haymanAuxiliaryA G (saddle n))
      (haymanAuxiliaryB G (saddle n)) ε n hGn hAn (hnloc θ hθ)
  · intro ε hε
    filter_upwards [hB.eventually (eventually_gt_atTop 0), hGne,
      hdecay ε hε] with n hBn hGn hndec
    intro θ hδθ hθpi
    apply hayman_normalized_decay
      (G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (G (saddle n : ℂ))
      (Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))))
      (haymanAuxiliaryB G (saddle n)) ε hGn hBn (hndec θ hδθ hθpi)
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp

private theorem hayman_coefficient_ratio_identity
    (r B : ℝ) (n : ℕ) (G0 J : ℂ)
    (hr : r ≠ 0) (hB : 0 < B) (hG : G0 ≠ 0) :
    (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (r : ℂ) ^ (-(n : ℤ)) * J) /
        (G0 / ((r : ℂ) ^ n * (Real.sqrt (2 * Real.pi * B) : ℂ))) =
      ((Real.sqrt B : ℂ) * (J / G0)) /
        (Real.sqrt (2 * Real.pi) : ℂ) := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrtpi : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hsqrtB : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  rw [Real.sqrt_mul (mul_nonneg (by norm_num) Real.pi_pos.le)]
  push_cast
  rw [zpow_neg, zpow_natCast]
  field_simp
  have hsqrtpiC : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = (2 * Real.pi : ℝ) := by
    exact_mod_cast Real.sq_sqrt (mul_nonneg (by norm_num) Real.pi_pos.le)
  rw [hsqrtpiC]
  push_cast
  ring

/-- **Hayman's coefficient asymptotic (finite radius).** Let $G : \mathbb{C} \to \mathbb{C}$ be
Hayman admissible on $(R_0, \rho)$, with Hayman auxiliary functions $A$ and $B$. Let
$(c_n)_{n \ge 0}$ be complex numbers such that $\sum_{n \ge 0} c_n z^n$ converges absolutely to
$G(z)$ for every complex $z$ with $|z| < \rho$, and let $(r_n)_{n \ge 0}$ be real numbers such
that for all sufficiently large $n$, $r_n \in (R_0, \rho)$, $A(r_n) = n$, and $r_n$ is the only
$r \in (R_0, \rho)$ with $A(r) = n$. Then, as $n \to \infty$,
$$c_n \sim \frac{G(r_n)}{r_n^n \sqrt{2\pi B(r_n)}}.$$

Proof: The saddle converges to the finite radius, Cauchy's coefficient integral is split at the
admissibility cutoff, and the central Gaussian term and decaying tails are normalized separately.

Proves `Wanted` entry `hayman_coefficient_asymptotic`.

Source: arXiv:1906.07169v2, tex lines 495-506.
-/
theorem hayman_coefficient_asymptotic
    (G : ℂ → ℂ) (coeff : ℕ → ℂ) (R0 ρ : ℝ) (saddle : ℕ → ℝ) :
    IsHaymanAdmissible G R0 ρ →
    (∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => coeff n * z ^ n) (G z)) →
    (∀ᶠ n : ℕ in Filter.atTop, saddle n ∈ Set.Ioo R0 ρ ∧
      haymanAuxiliaryA G (saddle n) = (n : ℝ) ∧
      (∀ r ∈ Set.Ioo R0 ρ, haymanAuxiliaryA G r = (n : ℝ) → r = saddle n)) →
    Asymptotics.IsEquivalent Filter.atTop coeff
      (fun n => G (saddle n : ℂ) /
        ((saddle n : ℂ) ^ n *
          (Real.sqrt (2 * Real.pi * haymanAuxiliaryB G (saddle n)) : ℂ))) := by
  rintro hAdm hsum hsaddle
  rcases hAdm with
    ⟨hR0, hRρ, hG, haxis, hAinf, hBinf, δ, hδ, hloc, hdecay⟩
  have hρ : 0 < ρ := hR0.trans hRρ
  have hAcont : ContinuousOn (haymanAuxiliaryA G) (Ioo R0 ρ) :=
    hayman_auxiliaryA_continuousOn hR0 hG fun r hr => (haxis r hr).1
  have hrs : Tendsto saddle atTop (𝓝[Ioo R0 ρ] ρ) :=
    hayman_saddle_tendsto hRρ hAcont hAinf hsaddle
  have hBsat : Tendsto (fun n => haymanAuxiliaryB G (saddle n)) atTop atTop :=
    hBinf.comp hrs
  have hδsat : ∀ᶠ n : ℕ in atTop,
      0 < δ (saddle n) ∧ δ (saddle n) < Real.pi := hrs.eventually hδ
  have hscale : Tendsto
      (fun n => δ (saddle n) * Real.sqrt (haymanAuxiliaryB G (saddle n)))
      atTop atTop :=
    (hayman_cutoff_scaled_tendsto (fun r hr => (haxis r hr).1)
      hBinf hδ hloc hdecay).comp hrs
  have hGne : ∀ᶠ n : ℕ in atTop, G (saddle n : ℂ) ≠ 0 := by
    filter_upwards [hsaddle] with n hn
    intro hzero
    simpa [hzero] using (haxis (saddle n) hn.1).1
  have hAeq : ∀ᶠ n : ℕ in atTop,
      haymanAuxiliaryA G (saddle n) = (n : ℝ) :=
    hsaddle.mono fun _ hn => hn.2.1
  have hcircle : ∀ᶠ n : ℕ in atTop, Continuous (fun θ : ℝ =>
      G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
    filter_upwards [hsaddle] with n hn
    have hrpos : 0 < saddle n := hR0.trans hn.1.1
    let circle : ℝ → ℂ := fun θ =>
      (saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
    have hcast : Continuous (fun θ : ℝ => (θ : ℂ)) := Complex.continuous_ofReal
    have hcircleCont : Continuous circle := by
      dsimp [circle]
      exact continuous_const.mul
        (Complex.continuous_exp.comp (continuous_const.mul hcast))
    have hcircleMem : ∀ θ : ℝ, circle θ ∈ ball (0 : ℂ) ρ := by
      intro θ
      have hnormexp : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re]
      simpa [circle, mem_ball, norm_mul, hnormexp, abs_of_pos hrpos] using hn.1.2
    simpa [Function.comp_def, circle] using
      hG.continuousOn.comp_continuous hcircleCont hcircleMem
  have hlocsat : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ,
      |θ| ≤ δ (saddle n) →
        ‖G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          G (saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ) *
            (haymanAuxiliaryA G (saddle n) : ℂ) -
            ((θ ^ 2 * haymanAuxiliaryB G (saddle n) / 2 : ℝ) : ℂ))‖ ≤
        ε * ‖G (saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ) *
          (haymanAuxiliaryA G (saddle n) : ℂ) -
          ((θ ^ 2 * haymanAuxiliaryB G (saddle n) / 2 : ℝ) : ℂ))‖ := by
    intro ε hε
    exact hrs.eventually (hloc ε hε)
  have hdecaysat : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ,
      δ (saddle n) ≤ |θ| → |θ| < Real.pi →
        ‖G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤
        ε * (‖G (saddle n : ℂ)‖ /
          Real.sqrt (haymanAuxiliaryB G (saddle n))) := by
    intro ε hε
    exact hrs.eventually (hdecay ε hε)
  have hangular := hayman_angular_integral_tendsto G saddle δ hBsat hδsat hscale
    hGne hAeq hcircle hlocsat hdecaysat
  have hsqrtpi : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hnormalized : Tendsto
      (fun n => ((Real.sqrt (haymanAuxiliaryB G (saddle n)) : ℂ) *
        ∫ θ : ℝ in -Real.pi..Real.pi,
          G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) /
              G (saddle n : ℂ)) /
        (Real.sqrt (2 * Real.pi) : ℂ)) atTop (𝓝 1) := by
    simpa only [div_self hsqrtpi] using
      hangular.div_const (Real.sqrt (2 * Real.pi) : ℂ)
  have htarget : ∀ᶠ n : ℕ in atTop,
      G (saddle n : ℂ) /
        ((saddle n : ℂ) ^ n *
          (Real.sqrt (2 * Real.pi * haymanAuxiliaryB G (saddle n)) : ℂ)) ≠ 0 := by
    filter_upwards [hsaddle, hBsat.eventually (eventually_gt_atTop 0), hGne] with
      n hn hBn hGn
    apply div_ne_zero hGn
    apply mul_ne_zero
    · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hR0.trans hn.1.1)))
    · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2
        (mul_pos (mul_pos (by norm_num) Real.pi_pos) hBn)))
  apply (isEquivalent_iff_tendsto_one htarget).2
  apply hnormalized.congr'
  filter_upwards [hsaddle, hBsat.eventually (eventually_gt_atTop 0), hGne] with
    n hn hBn hGn
  let J : ℂ := ∫ θ : ℝ in -Real.pi..Real.pi,
    G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ)))
  have hcoeff : coeff n = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (saddle n : ℂ) ^ (-(n : ℤ)) * J := by
    simpa [J] using hayman_powerSeries_coefficient_eq_intervalIntegral
      G coeff hρ (hR0.trans hn.1.1) hn.1.2 hsum n
  have hnormalizedIntegral :
      (∫ θ : ℝ in -Real.pi..Real.pi,
        G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) /
            G (saddle n : ℂ)) = J / G (saddle n : ℂ) := by
    change (∫ θ : ℝ in -Real.pi..Real.pi,
      (G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ)))) *
          (G (saddle n : ℂ))⁻¹) = J / G (saddle n : ℂ)
    rw [intervalIntegral.integral_mul_const]
    rfl
  change
    ((Real.sqrt (haymanAuxiliaryB G (saddle n)) : ℂ) *
      ∫ θ : ℝ in -Real.pi..Real.pi,
        G ((saddle n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          Complex.exp (-(Complex.I * (θ : ℂ) * (n : ℂ))) /
            G (saddle n : ℂ)) /
      (Real.sqrt (2 * Real.pi) : ℂ) =
    coeff n / (G (saddle n : ℂ) /
      ((saddle n : ℂ) ^ n *
        (Real.sqrt (2 * Real.pi * haymanAuxiliaryB G (saddle n)) : ℂ)))
  rw [hcoeff, hnormalizedIntegral]
  exact (hayman_coefficient_ratio_identity (saddle n)
    (haymanAuxiliaryB G (saddle n)) n (G (saddle n : ℂ)) J
    (ne_of_gt (hR0.trans hn.1.1)) hBn hGn).symm

end MetaMathlibExt
