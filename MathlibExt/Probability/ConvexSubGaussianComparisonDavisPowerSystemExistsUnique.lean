/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import MathlibExt.Probability.ConvexSubGaussianComparison
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

/-!
# Existence and uniqueness for the Davis–Power system

This module proves `davisPowerSystem_existsUnique`: there is exactly one quadruple
$(a, p_0, z, c_0)$ of real numbers that is a valid solution of the Davis–Power system.
It holds the Davis–Power equation data (`standardNormalTail`, `davisPowerT0`,
`davisPowerA`, `davisPowerB`, `davisPowerH`, `DavisPowerSolution` and
`DavisPowerSolution.IsValid`), moved here from the literature-requests module, and the
existence-and-uniqueness theorem.

The system decouples: the threshold equation $h(a) = B$ has exactly one solution above
$t_0$ because $h$ is strictly decreasing there with $h(t_0) = A = 2B$ and limit $0$ at
infinity; then $p_0 = 2e^{-a^2/2}$ lies in $(0, 1)$; the Gaussian tail $Q$ takes the value
$p_0$ exactly once since it decreases strictly from $1$ to $0$; and $c_0 = B/\varphi(z)$
is forced.

Source: Davis–Power (2026), equations (3)–(6), existence and uniqueness.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.ConvexSubGaussianComparison

namespace MathlibExt.Probability.ConvexSubGaussianComparisonWantedDavis

open Set Filter Topology

/-- **Standard Gaussian upper tail.** For a real number $x$, the standard Gaussian upper tail at
$x$ is $Q(x) = \int_x^\infty \varphi(t)\,dt$, where $\varphi(t) = e^{-t^2/2}/\sqrt{2\pi}$ is the
standard Gaussian density. -/
noncomputable def standardNormalTail (x : ℝ) : ℝ :=
  ∫ t in Ici x, gaussianPDFReal 0 1 t

/-- **The Davis–Power transition threshold.** The transition threshold is the real number
$t_0 = \sqrt{2\log 2}$, where $\log$ is the natural logarithm. -/
noncomputable def davisPowerT0 : ℝ :=
  Real.sqrt (2 * Real.log 2)

/-- **The envelope integral $A$.** Let $A = \int_0^\infty \min(1, 2e^{-t^2/2})\,dt$, the integral
over $[0, \infty)$ of the capped Gaussian tail envelope $t \mapsto \min(1, 2e^{-t^2/2})$.

This integral appears in equation (3) of Davis–Power (2026). -/
noncomputable def davisPowerA : ℝ :=
  ∫ t in Ici (0 : ℝ), gaussianTailEnvelope t

/-- **Half the envelope integral, $B$.** Let $B = A/2$, where
$A = \int_0^\infty \min(1, 2e^{-t^2/2})\,dt$ is the integral over $[0, \infty)$ of the capped
Gaussian tail envelope.

This constant appears in equation (3) of Davis–Power (2026). -/
noncomputable def davisPowerB : ℝ :=
  davisPowerA / 2

/-- **The function $h$ of Davis–Power.** For real $x$, let
$h(x) = 2x e^{-x^2/2} + 2\int_x^\infty e^{-t^2/2}\,dt$.

This is equation (4) of Davis–Power (2026); the Davis–Power equation system uses $h$ only at
points above the transition threshold $\sqrt{2 \log 2}$. -/
noncomputable def davisPowerH (x : ℝ) : ℝ :=
  2 * x * Real.exp (-x ^ 2 / 2) + 2 * ∫ t in Ici x, Real.exp (-t ^ 2 / 2)

/-- **Parameter quadruples of the Davis–Power system.** A parameter quadruple is a quadruple
$(a, p_0, z, c_0)$ of real numbers, the unknowns of the Davis–Power equation system. Being a
solution of the system is a separate condition. -/
@[ext] structure DavisPowerSolution where
  a : ℝ
  p0 : ℝ
  z : ℝ
  c0 : ℝ

/-- **Valid solutions of the Davis–Power system.** Let $\varphi(t) = e^{-t^2/2}/\sqrt{2\pi}$ be
the standard Gaussian density, $Q(x) = \int_x^\infty \varphi(t)\,dt$ its upper tail,
$t_0 = \sqrt{2\log 2}$ with $\log$ the natural logarithm,
$B = \frac{1}{2}\int_0^\infty \min(1, 2e^{-t^2/2})\,dt$ and
$h(x) = 2x e^{-x^2/2} + 2\int_x^\infty e^{-t^2/2}\,dt$. A quadruple $(a, p_0, z, c_0)$ of real
numbers is a valid solution of the Davis–Power system when $a > t_0$, $h(a) = B$,
$p_0 = 2e^{-a^2/2}$, $0 < p_0 < 1$, $Q(z) = p_0$ and $c_0 = B/\varphi(z)$.

These are equations (3)–(6) of Davis–Power (2026), with the domain conditions that select the
solution. -/
noncomputable def DavisPowerSolution.IsValid (q : DavisPowerSolution) : Prop :=
  davisPowerT0 < q.a ∧
    davisPowerH q.a = davisPowerB ∧
    q.p0 = 2 * Real.exp (-q.a ^ 2 / 2) ∧
    0 < q.p0 ∧ q.p0 < 1 ∧
    standardNormalTail q.z = q.p0 ∧
    q.c0 = davisPowerB / gaussianPDFReal 0 1 q.z

/-- The radicand $2\log 2$ of the transition threshold is positive. -/
private lemma two_mul_log_two_pos : 0 < 2 * Real.log 2 :=
  mul_pos (by norm_num) (Real.log_pos one_lt_two)

/-- The transition threshold $t_0$ is positive. -/
private lemma davisPowerT0_pos : 0 < davisPowerT0 :=
  Real.sqrt_pos.mpr two_mul_log_two_pos

/-- The transition threshold $t_0$ is nonnegative. -/
private lemma davisPowerT0_nonneg : 0 ≤ davisPowerT0 := davisPowerT0_pos.le

/-- The square of the transition threshold is $t_0^2 = 2\log 2$. -/
private lemma davisPowerT0_sq : davisPowerT0 ^ 2 = 2 * Real.log 2 :=
  Real.sq_sqrt two_mul_log_two_pos.le

/-- The Gaussian factor at the threshold: $e^{-t_0^2/2} = 1/2$. -/
private lemma exp_neg_t0_sq : Real.exp (-davisPowerT0 ^ 2 / 2) = 1 / 2 := by
  rw [davisPowerT0_sq]
  have hlog : Real.exp (-Real.log 2) = ((2 : ℝ))⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
  have harg : -(2 * Real.log 2) / 2 = -Real.log 2 := by ring
  rw [harg, hlog]
  norm_num

/-- Continuity of $t \mapsto e^{-t^2/2}$. -/
private lemma continuous_exp_neg_sq : Continuous fun t : ℝ => Real.exp (-t ^ 2 / 2) := by
  fun_prop

/-- Integrability of $t \mapsto e^{-t^2/2}$. -/
private lemma integrable_exp_neg_sq :
    Integrable (fun t : ℝ => Real.exp (-t ^ 2 / 2)) volume := by
  have h := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 / 2 by norm_num)
  have e : (fun t : ℝ => Real.exp (-t ^ 2 / 2))
      = (fun x : ℝ => Real.exp (-(1/2) * x ^ 2)) := by
    ext x
    congr 1
    ring
  rw [e]
  exact h

/-- The derivative of an upper-tail integral is the negated integrand. -/
private lemma hasDerivAt_tailIntegral {f : ℝ → ℝ} (hf : Continuous f)
    (hint : Integrable f volume) (x0 : ℝ) :
    HasDerivAt (fun x => ∫ t in Ici x, f t ∂volume) (-f x0) x0 := by
  have hsub : ∀ x : ℝ, (∫ t in Ioi x, f t ∂volume)
      = (∫ t in Ioi x0, f t ∂volume) - ∫ t in x0..x, f t ∂volume := by
    intro x
    have h : (∫ t in Ioi x0, f t ∂volume) - ∫ t in Ioi x, f t ∂volume
        = ∫ t in x0..x, f t ∂volume :=
      intervalIntegral.integral_Ioi_sub_Ioi' hint.integrableOn hint.integrableOn
    linarith
  have hFTC : HasDerivAt (fun u => ∫ t in x0..u, f t ∂volume) (f x0) x0 :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_univ (fun x _ => hf.continuousAt) x0
        (mem_univ x0))
      hf.continuousAt
  have hmain : HasDerivAt (fun x => (∫ t in Ioi x0, f t ∂volume) - ∫ t in x0..x, f t ∂volume)
      (-f x0) x0 := by
    have h := HasDerivAt.const_sub (∫ t in Ioi x0, f t ∂volume) hFTC
    simpa using h
  have heq : (fun x => ∫ t in Ici x, f t ∂volume)
      =ᶠ[𝓝 x0] (fun x => (∫ t in Ioi x0, f t ∂volume) - ∫ t in x0..x, f t ∂volume) := by
    filter_upwards with x
    rw [integral_Ici_eq_integral_Ioi, hsub x]
  exact hmain.congr_of_eventuallyEq heq

/-- The derivative of the explicit term $x \mapsto 2x e^{-x^2/2}$ of $h$. -/
private lemma hasDerivAt_g (x : ℝ) :
    HasDerivAt (fun x => 2 * x * Real.exp (-x ^ 2 / 2))
      (2 * Real.exp (-x ^ 2 / 2) * (1 - x ^ 2)) x := by
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-(2 * x) / 2) x := by
    refine (hp.neg.div_const 2).congr_of_eventuallyEq ?_
    filter_upwards with y
    simp [Pi.neg_apply]
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 2))
      (Real.exp (-x ^ 2 / 2) * (-(2 * x) / 2)) x :=
    h1.exp
  have hmul : HasDerivAt (fun x : ℝ => x * Real.exp (-x ^ 2 / 2))
      (1 * Real.exp (-x ^ 2 / 2) + x * (Real.exp (-x ^ 2 / 2) * (-(2 * x) / 2))) x := by
    refine ((hasDerivAt_id' x).mul hexp).congr_of_eventuallyEq ?_
    filter_upwards with y
    simp [Pi.mul_apply]
  have h2 := hmul.const_mul 2
  have hfun : (fun x : ℝ => 2 * x * Real.exp (-x ^ 2 / 2))
      = fun x => 2 * (x * Real.exp (-x ^ 2 / 2)) := by
    ext y
    ring
  have hder : 2 * Real.exp (-x ^ 2 / 2) * (1 - x ^ 2)
      = 2 * (1 * Real.exp (-x ^ 2 / 2)
        + x * (Real.exp (-x ^ 2 / 2) * (-(2 * x) / 2))) := by
    ring
  rw [hfun, hder]
  exact h2

/-- The derivative of $h$: $h'(x) = -2x^2 e^{-x^2/2}$. -/
private lemma hasDerivAt_h (x : ℝ) :
    HasDerivAt davisPowerH (-2 * x ^ 2 * Real.exp (-x ^ 2 / 2)) x := by
  have hg := hasDerivAt_g x
  have hI := hasDerivAt_tailIntegral continuous_exp_neg_sq integrable_exp_neg_sq x
  have h2I := HasDerivAt.const_mul 2 hI
  have hadd := hg.add h2I
  have hfun : davisPowerH = (fun x => 2 * x * Real.exp (-x ^ 2 / 2))
      + fun x => 2 * ∫ t in Ici x, Real.exp (-t ^ 2 / 2) ∂volume := rfl
  have hder : (-2 * x ^ 2 * Real.exp (-x ^ 2 / 2))
      = 2 * Real.exp (-x ^ 2 / 2) * (1 - x ^ 2) + 2 * -Real.exp (-x ^ 2 / 2) := by
    ring
  rw [hfun, hder]
  exact hadd

/-- The derivative of $h$ as an equation. -/
private lemma deriv_h_eq (x : ℝ) :
    deriv davisPowerH x = -2 * x ^ 2 * Real.exp (-x ^ 2 / 2) :=
  (hasDerivAt_h x).deriv

/-- The derivative of $h$ never vanishes on $\mathrm{Ici}\ t_0$. -/
private lemma deriv_h_ne_zero {x : ℝ} (hx : x ∈ Ici davisPowerT0) :
    deriv davisPowerH x ≠ 0 := by
  rw [deriv_h_eq]
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le davisPowerT0_pos hx)
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hx0))
    (Real.exp_pos _).ne'

/-- The derivative of $h$ is negative on the interior of $\mathrm{Ici}\ t_0$. -/
private lemma deriv_h_neg {x : ℝ} (hx : x ∈ interior (Ici davisPowerT0)) :
    deriv davisPowerH x < 0 := by
  rw [interior_Ici] at hx
  rw [deriv_h_eq]
  have hx0 : 0 < x := lt_trans davisPowerT0_pos hx
  have h1 : 0 < x ^ 2 := pow_pos hx0 2
  have h2 : 0 < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
  have h3 : 0 < 2 * x ^ 2 * Real.exp (-x ^ 2 / 2) :=
    mul_pos (mul_pos (by norm_num) h1) h2
  linarith

/-- The function $h$ is strictly decreasing on $\mathrm{Ici}\ t_0$. -/
private lemma strictAntiOn_h : StrictAntiOn davisPowerH (Ici davisPowerT0) :=
  strictAntiOn_of_deriv_neg (convex_Ici _)
    (fun _x hx => (differentiableAt_of_deriv_ne_zero
      (deriv_h_ne_zero hx)).differentiableWithinAt.continuousWithinAt)
    (fun _x hx => deriv_h_neg hx)

/-- The explicit term $x e^{-x^2/2}$ vanishes at infinity. -/
private lemma tendsto_mul_exp_neg_sq :
    Tendsto (fun x : ℝ => x * Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
  have hub : Tendsto (fun x : ℝ => 2 / x) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => (2 : ℝ) * r⁻¹) atTop (𝓝 ((2 : ℝ) * 0)) :=
      Filter.Tendsto.const_mul 2 tendsto_inv_atTop_zero
    rw [mul_zero] at h
    have hfun : (fun x : ℝ => 2 / x) = fun r : ℝ => (2 : ℝ) * r⁻¹ := by
      ext r
      rw [div_eq_mul_inv]
    rw [hfun]
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact mul_nonneg hx (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
    have hE : x ^ 2 / 2 + 1 ≤ Real.exp (x ^ 2 / 2) := Real.add_one_le_exp _
    have hEpos : 0 < Real.exp (x ^ 2 / 2) := Real.exp_pos _
    have hexp : Real.exp (-x ^ 2 / 2) = (Real.exp (x ^ 2 / 2))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    have hxx : x * x ≤ 2 * Real.exp (x ^ 2 / 2) := by
      have h1 : x ^ 2 / 2 ≤ Real.exp (x ^ 2 / 2) := le_trans (by linarith) hE
      have h2 : x * x = x ^ 2 := by ring
      rw [h2]
      linarith
    rw [hexp, ← div_eq_mul_inv]
    exact (div_le_div_iff₀ hEpos hx0).mpr hxx

/-- Set integrals vanish along a filter when their indicators tend to zero. -/
private lemma tendsto_setIntegral_of_indicator_tendsto_zero {s : ℝ → Set ℝ}
    (hs : ∀ x, MeasurableSet (s x)) {f : ℝ → ℝ} (hint : Integrable f volume)
    {l : Filter ℝ} [l.IsCountablyGenerated]
    (hlim : ∀ t, Tendsto (fun x => (s x).indicator f t) l (𝓝 0)) :
    Tendsto (fun x => ∫ t in s x, f t ∂volume) l (𝓝 0) := by
  have heq : (fun x : ℝ => ∫ t in s x, f t ∂volume)
      = fun x => ∫ t, (s x).indicator f t ∂volume :=
    funext fun x => (integral_indicator (hs x)).symm
  rw [heq]
  have hlim0 : Tendsto (fun x : ℝ => ∫ t, (s x).indicator f t ∂volume) l
      (𝓝 (∫ t, (0 : ℝ → ℝ) t ∂volume)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖) ?_ ?_
      hint.norm ?_
    · filter_upwards with x
      exact hint.aestronglyMeasurable.indicator (hs x)
    · refine Eventually.of_forall fun x => Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ s x
      · rw [indicator_of_mem ht]
      · rw [indicator_of_notMem ht]
        simp
    · filter_upwards with t
      exact hlim t
  simpa using hlim0

/-- Upper-tail integrals vanish at infinity. -/
private lemma tendsto_Ici_atTop_zero {f : ℝ → ℝ} (hint : Integrable f volume) :
    Tendsto (fun x : ℝ => ∫ t in Ici x, f t ∂volume) atTop (𝓝 0) := by
  apply tendsto_setIntegral_of_indicator_tendsto_zero (fun x => measurableSet_Ici) hint
  intro t
  have hev : ∀ᶠ x in (atTop : Filter ℝ), (Ici x).indicator f t = 0 := by
    filter_upwards [eventually_gt_atTop t] with x hx
    exact indicator_of_notMem (not_le_of_gt hx) f
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

/-- Lower-tail integrals vanish at negative infinity. -/
private lemma tendsto_Iio_atBot_zero {f : ℝ → ℝ} (hint : Integrable f volume) :
    Tendsto (fun x : ℝ => ∫ t in Iio x, f t ∂volume) atBot (𝓝 0) := by
  apply tendsto_setIntegral_of_indicator_tendsto_zero (fun x => measurableSet_Iio) hint
  intro t
  have hev : ∀ᶠ x in (atBot : Filter ℝ), (Iio x).indicator f t = 0 := by
    filter_upwards [eventually_lt_atBot t] with x hx
    exact indicator_of_notMem (not_lt_of_ge hx.le) f
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

/-- The function $h$ vanishes at infinity. -/
private lemma tendsto_h_atTop : Tendsto davisPowerH atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => 2 * x * Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => (2 : ℝ) * (r * Real.exp (-r ^ 2 / 2))) atTop
        (𝓝 ((2 : ℝ) * 0)) :=
      Filter.Tendsto.const_mul 2 tendsto_mul_exp_neg_sq
    rw [mul_zero] at h
    have hfun : (fun x : ℝ => 2 * x * Real.exp (-x ^ 2 / 2))
        = fun r : ℝ => (2 : ℝ) * (r * Real.exp (-r ^ 2 / 2)) := by
      ext r
      ring
    rw [hfun]
    exact h
  have hI : Tendsto (fun x : ℝ => 2 * ∫ t in Ici x, Real.exp (-t ^ 2 / 2) ∂volume)
      atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => (2 : ℝ) * ∫ t in Ici x, Real.exp (-t ^ 2 / 2) ∂volume)
        atTop (𝓝 ((2 : ℝ) * 0)) :=
      Filter.Tendsto.const_mul 2 (tendsto_Ici_atTop_zero integrable_exp_neg_sq)
    rw [mul_zero] at h
    exact h
  have hfun : davisPowerH = fun x => (2 * x * Real.exp (-x ^ 2 / 2))
      + (2 * ∫ t in Ici x, Real.exp (-t ^ 2 / 2) ∂volume) := rfl
  rw [hfun]
  simpa using hg.add hI

/-- Continuity of the capped Gaussian tail envelope. -/
private lemma continuous_envelope : Continuous gaussianTailEnvelope := by
  have h : Continuous fun t : ℝ => min (1 : ℝ) (2 * Real.exp (-t ^ 2 / 2)) :=
    continuous_const.min (continuous_const.mul continuous_exp_neg_sq)
  exact h

/-- Integrability of the envelope on $\mathrm{Ici}\ 0$. -/
private lemma integrableOn_envelope_Ici0 :
    IntegrableOn gaussianTailEnvelope (Ici (0 : ℝ)) volume := by
  have h2 : IntegrableOn (fun t : ℝ => 2 * Real.exp (-t ^ 2 / 2)) (Ici (0 : ℝ)) volume :=
    (integrable_exp_neg_sq.const_mul 2).integrableOn
  refine h2.mono' ?_ ?_
  · exact continuous_envelope.aestronglyMeasurable.restrict
  · rw [ae_restrict_iff' measurableSet_Ici]
    refine ae_of_all _ fun t _ => ?_
    have hnn : 0 ≤ gaussianTailEnvelope t := by
      rw [gaussianTailEnvelope]
      exact le_min (by norm_num) (by positivity)
    have hle : gaussianTailEnvelope t ≤ 2 * Real.exp (-t ^ 2 / 2) := by
      rw [gaussianTailEnvelope]
      exact min_le_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hle

/-- The envelope equals $1$ below the transition threshold. -/
private lemma envelope_eq_one_of_mem_Ico {t : ℝ} (ht : t ∈ Ico (0 : ℝ) davisPowerT0) :
    gaussianTailEnvelope t = 1 := by
  have ht0 : 0 ≤ t := ht.1
  have htt0 : t < davisPowerT0 := ht.2
  have hsq : t ^ 2 < 2 * Real.log 2 := by
    have h1 : t ^ 2 < davisPowerT0 ^ 2 := pow_lt_pow_left₀ htt0 ht0 two_ne_zero
    rwa [davisPowerT0_sq] at h1
  have h : (1 : ℝ) ≤ 2 * Real.exp (-t ^ 2 / 2) := by
    have h2 : Real.exp (-Real.log 2) < Real.exp (-t ^ 2 / 2) :=
      Real.exp_lt_exp.mpr (by linarith [hsq])
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at h2
    have h4 : ((2 : ℝ))⁻¹ = 1/2 := by norm_num
    rw [h4] at h2
    linarith
  rw [gaussianTailEnvelope, min_eq_left h]

/-- The envelope equals $2e^{-t^2/2}$ above the transition threshold. -/
private lemma envelope_eq_of_mem_Ici {t : ℝ} (ht : t ∈ Ici davisPowerT0) :
    gaussianTailEnvelope t = 2 * Real.exp (-t ^ 2 / 2) := by
  have ht0 : davisPowerT0 ≤ t := ht
  have hsq : 2 * Real.log 2 ≤ t ^ 2 := by
    have h1 : davisPowerT0 ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ davisPowerT0_nonneg ht0 2
    rwa [davisPowerT0_sq] at h1
  have h : 2 * Real.exp (-t ^ 2 / 2) ≤ (1 : ℝ) := by
    have h2 : Real.exp (-t ^ 2 / 2) ≤ Real.exp (-Real.log 2) :=
      Real.exp_le_exp.mpr (by linarith [hsq])
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at h2
    have h4 : ((2 : ℝ))⁻¹ = 1/2 := by norm_num
    rw [h4] at h2
    linarith
  rw [gaussianTailEnvelope, min_eq_right h]

/-- Splitting the envelope integral at $t_0$: $A = t_0 + 2\int_{t_0}^\infty e^{-t^2/2}$. -/
private lemma davisPowerA_eq : davisPowerA
    = davisPowerT0 + 2 * ∫ t in Ici davisPowerT0, Real.exp (-t ^ 2 / 2) ∂volume := by
  have hsplit := intervalIntegral.integral_Ici_sub_Ici integrableOn_envelope_Ici0
    davisPowerT0_nonneg
  have hIco : (∫ t in Ico (0 : ℝ) davisPowerT0, gaussianTailEnvelope t ∂volume)
      = davisPowerT0 := by
    have hcongr : (∫ t in Ico (0 : ℝ) davisPowerT0, gaussianTailEnvelope t ∂volume)
        = ∫ t in Ico (0 : ℝ) davisPowerT0, (1 : ℝ) ∂volume := by
      apply setIntegral_congr_ae measurableSet_Ico
      refine ae_of_all _ fun t ht => ?_
      exact envelope_eq_one_of_mem_Ico ht
    rw [hcongr, setIntegral_const, Measure.real_def, Real.volume_Ico,
      ENNReal.toReal_ofReal (by linarith [davisPowerT0_nonneg] : (0 : ℝ) ≤ davisPowerT0 - 0)]
    simp
  have hIci : (∫ t in Ici davisPowerT0, gaussianTailEnvelope t ∂volume)
      = 2 * ∫ t in Ici davisPowerT0, Real.exp (-t ^ 2 / 2) ∂volume := by
    have hcongr : (∫ t in Ici davisPowerT0, gaussianTailEnvelope t ∂volume)
        = ∫ t in Ici davisPowerT0, (2 * Real.exp (-t ^ 2 / 2)) ∂volume := by
      apply setIntegral_congr_ae measurableSet_Ici
      refine ae_of_all _ fun t ht => ?_
      exact envelope_eq_of_mem_Ici ht
    rw [hcongr, integral_const_mul]
  have hA : davisPowerA = ∫ t in Ici (0 : ℝ), gaussianTailEnvelope t ∂volume := rfl
  rw [hA]
  linarith [hsplit, hIco, hIci]

/-- The value of $h$ at the threshold. -/
private lemma davisPowerH_t0 : davisPowerH davisPowerT0
    = davisPowerT0 + 2 * ∫ t in Ici davisPowerT0, Real.exp (-t ^ 2 / 2) ∂volume := by
  have h : davisPowerH davisPowerT0
      = 2 * davisPowerT0 * Real.exp (-davisPowerT0 ^ 2 / 2)
        + 2 * ∫ t in Ici davisPowerT0, Real.exp (-t ^ 2 / 2) ∂volume := rfl
  rw [h, exp_neg_t0_sq]
  ring

/-- The envelope integral equals $h(t_0)$. -/
private lemma davisPowerA_eq_h_t0 : davisPowerA = davisPowerH davisPowerT0 := by
  rw [davisPowerA_eq, davisPowerH_t0]

/-- Upper-tail integrals of $e^{-t^2/2}$ are nonnegative. -/
private lemma tailIntegral_nonneg (c : ℝ) :
    0 ≤ ∫ t in Ici c, Real.exp (-t ^ 2 / 2) ∂volume := by
  rw [← integral_indicator measurableSet_Ici]
  apply integral_nonneg
  intro t
  by_cases ht : t ∈ Ici c
  · rw [indicator_of_mem ht]
    exact (Real.exp_pos _).le
  · rw [indicator_of_notMem ht]
    exact le_rfl

/-- The constant $B$ is positive. -/
private lemma davisPowerB_pos : 0 < davisPowerB := by
  have hA : 0 < davisPowerA := by
    rw [davisPowerA_eq_h_t0, davisPowerH_t0]
    have hnn := tailIntegral_nonneg davisPowerT0
    linarith [davisPowerT0_pos, hnn]
  have hB : davisPowerB = davisPowerA / 2 := rfl
  rw [hB]
  linarith

/-- Existence of a threshold parameter: some $a > t_0$ satisfies $h(a) = B$. -/
private lemma exists_a : ∃ a : ℝ, davisPowerT0 < a ∧ davisPowerH a = davisPowerB := by
  have hev : ∀ᶠ x in (atTop : Filter ℝ), davisPowerH x < davisPowerB :=
    tendsto_h_atTop.eventually (eventually_lt_nhds davisPowerB_pos)
  have h2 : ∀ᶠ x in (atTop : Filter ℝ), davisPowerT0 ≤ x ∧ davisPowerH x < davisPowerB :=
    (eventually_ge_atTop davisPowerT0).and hev
  obtain ⟨x1, hx1t0, hx1B⟩ := h2.exists
  have hBt0 : davisPowerH davisPowerT0 = 2 * davisPowerB := by
    have hB : davisPowerB = davisPowerA / 2 := rfl
    linarith [davisPowerA_eq_h_t0, hB]
  have hmem : davisPowerB ∈ Ioo (davisPowerH x1) (davisPowerH davisPowerT0) :=
    ⟨hx1B, by linarith [hBt0, davisPowerB_pos]⟩
  have hcont : ContinuousOn davisPowerH (Icc davisPowerT0 x1) := by
    intro x hx
    have hxIci : x ∈ Ici davisPowerT0 := hx.1
    exact (differentiableAt_of_deriv_ne_zero
      (deriv_h_ne_zero hxIci)).continuousAt.continuousWithinAt
  obtain ⟨a, haIoo, haeq⟩ := intermediate_value_Ioo' hx1t0 hcont hmem
  exact ⟨a, haIoo.1, haeq⟩

/-- Uniqueness of the threshold parameter. -/
private lemma unique_a {a1 a2 : ℝ} (h1 : davisPowerT0 < a1)
    (h2 : davisPowerH a1 = davisPowerB) (h3 : davisPowerT0 < a2)
    (h4 : davisPowerH a2 = davisPowerB) : a1 = a2 :=
  strictAntiOn_h.injOn (le_of_lt h1) (le_of_lt h3) (h2.trans h4.symm)

/-- Continuity of the standard Gaussian density. -/
private lemma continuous_phi : Continuous (gaussianPDFReal (0 : ℝ) (1 : NNReal)) := by
  rw [gaussianPDFReal_def]
  fun_prop

/-- Integrability of the standard Gaussian density. -/
private lemma integrable_phi : Integrable (gaussianPDFReal (0 : ℝ) (1 : NNReal)) volume :=
  integrable_gaussianPDFReal 0 1

/-- The standard Gaussian density integrates to one. -/
private lemma integral_phi_eq_one :
    (∫ x, gaussianPDFReal (0 : ℝ) (1 : NNReal) x ∂volume) = 1 :=
  integral_gaussianPDFReal_eq_one 0 (by simp)

/-- The derivative of the Gaussian tail: $Q'(x) = -\varphi(x)$. -/
private lemma hasDerivAt_Q (x0 : ℝ) :
    HasDerivAt standardNormalTail (-gaussianPDFReal 0 1 x0) x0 :=
  hasDerivAt_tailIntegral continuous_phi integrable_phi x0

/-- The derivative of the Gaussian tail as an equation. -/
private lemma deriv_Q_eq (x : ℝ) :
    deriv standardNormalTail x = -gaussianPDFReal 0 1 x :=
  (hasDerivAt_Q x).deriv

/-- The derivative of the Gaussian tail never vanishes. -/
private lemma deriv_Q_ne_zero (x : ℝ) : deriv standardNormalTail x ≠ 0 := by
  rw [deriv_Q_eq x]
  exact neg_ne_zero.mpr (ne_of_gt (gaussianPDFReal_pos 0 1 x (by simp)))

/-- The Gaussian tail is strictly decreasing on the whole line. -/
private lemma strictAnti_Q : StrictAntiOn standardNormalTail univ := by
  apply strictAntiOn_of_deriv_neg convex_univ _ _
  · intro x _
    exact (differentiableAt_of_deriv_ne_zero
      (deriv_Q_ne_zero x)).differentiableWithinAt.continuousWithinAt
  · intro x hx
    rw [interior_univ] at hx
    rw [deriv_Q_eq x]
    exact neg_lt_zero.mpr (gaussianPDFReal_pos 0 1 x (by simp))

/-- The Gaussian tail vanishes at infinity. -/
private lemma tendsto_Q_atTop : Tendsto standardNormalTail atTop (𝓝 0) :=
  tendsto_Ici_atTop_zero integrable_phi

/-- The Gaussian tail tends to one at negative infinity. -/
private lemma tendsto_Q_atBot : Tendsto standardNormalTail atBot (𝓝 1) := by
  have hsplit : ∀ x : ℝ, standardNormalTail x
      = 1 - ∫ t in Iio x, gaussianPDFReal 0 1 t ∂volume := by
    intro x
    have h : (∫ t in Iio x, gaussianPDFReal 0 1 t ∂volume)
        + ∫ t in Ici x, gaussianPDFReal 0 1 t ∂volume
        = ∫ t, gaussianPDFReal 0 1 t ∂volume :=
      intervalIntegral.integral_Iio_add_Ici integrable_phi.integrableOn
        integrable_phi.integrableOn
    rw [integral_phi_eq_one] at h
    have hQ : standardNormalTail x = ∫ t in Ici x, gaussianPDFReal 0 1 t ∂volume := rfl
    rw [hQ]
    linarith
  have hlim : Tendsto (fun x : ℝ => 1 - ∫ t in Iio x, gaussianPDFReal 0 1 t ∂volume)
      atBot (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_Iio_atBot_zero integrable_phi)
  rw [sub_zero] at hlim
  have heq : standardNormalTail
      = fun x : ℝ => 1 - ∫ t in Iio x, gaussianPDFReal 0 1 t ∂volume :=
    funext hsplit
  rw [heq]
  exact hlim

/-- Existence of a quantile: every $p_0 \in (0, 1)$ is a value of the Gaussian tail. -/
private lemma exists_z {p0 : ℝ} (hpos : 0 < p0) (hlt : p0 < 1) :
    ∃ z : ℝ, standardNormalTail z = p0 := by
  have hev_lo : ∀ᶠ x in (atTop : Filter ℝ), standardNormalTail x < p0 :=
    tendsto_Q_atTop.eventually (eventually_lt_nhds hpos)
  have hev_hi : ∀ᶠ x in (atBot : Filter ℝ), p0 < standardNormalTail x :=
    tendsto_Q_atBot.eventually (eventually_gt_nhds hlt)
  obtain ⟨x1, hx1⟩ := hev_lo.exists
  obtain ⟨x2, hx2⟩ := hev_hi.exists
  have hcont : ContinuousOn standardNormalTail (Icc x2 x1) := by
    intro x _
    exact (differentiableAt_of_deriv_ne_zero
      (deriv_Q_ne_zero x)).continuousAt.continuousWithinAt
  rcases le_total x2 x1 with hle | hle
  · have hmem : p0 ∈ Ioo (standardNormalTail x1) (standardNormalTail x2) := ⟨hx1, hx2⟩
    obtain ⟨z, _, hzeq⟩ := intermediate_value_Ioo' hle hcont hmem
    exact ⟨z, hzeq⟩
  · have hle' : standardNormalTail x2 ≤ standardNormalTail x1 :=
      strictAnti_Q.antitoneOn (mem_univ x1) (mem_univ x2) hle
    linarith

/-- Uniqueness of the quantile. -/
private lemma unique_z {z1 z2 p0 : ℝ} (h1 : standardNormalTail z1 = p0)
    (h2 : standardNormalTail z2 = p0) : z1 = z2 :=
  strictAnti_Q.injOn (mem_univ z1) (mem_univ z2) (h1.trans h2.symm)

/-- The formula $2e^{-a^2/2}$ for $p_0$ is positive. -/
private lemma exp_p0_pos (a : ℝ) : 0 < 2 * Real.exp (-a ^ 2 / 2) :=
  mul_pos (by norm_num) (Real.exp_pos _)

/-- The formula $2e^{-a^2/2}$ for $p_0$ is below one when $a > t_0$. -/
private lemma p0_lt_one {a : ℝ} (ha : davisPowerT0 < a) :
    2 * Real.exp (-a ^ 2 / 2) < 1 := by
  have hsq : 2 * Real.log 2 < a ^ 2 := by
    have h1 : davisPowerT0 ^ 2 < a ^ 2 :=
      pow_lt_pow_left₀ ha davisPowerT0_nonneg two_ne_zero
    rwa [davisPowerT0_sq] at h1
  have h2 : Real.exp (-a ^ 2 / 2) < Real.exp (-Real.log 2) :=
    Real.exp_lt_exp.mpr (by linarith [hsq])
  rw [Real.exp_neg, Real.exp_log (by norm_num)] at h2
  have h4 : ((2 : ℝ))⁻¹ = 1/2 := by norm_num
  rw [h4] at h2
  linarith

end MathlibExt.Probability.ConvexSubGaussianComparisonWantedDavis

open MathlibExt.Probability.ConvexSubGaussianComparisonWantedDavis

namespace MathlibExt.Probability.ConvexSubGaussianComparisonWanted

/-- **Existence and uniqueness for the Davis–Power system.** There is exactly one quadruple
$(a, p_0, z, c_0)$ of real numbers that is a valid solution of the Davis–Power system.

Source: Davis–Power (2026), equations (3)–(6), existence and uniqueness. -/
theorem davisPowerSystem_existsUnique :
    ∃! q : DavisPowerSolution, q.IsValid := by
  obtain ⟨a, ha_gt, ha_eq⟩ := exists_a
  obtain ⟨z, hz_eq⟩ := exists_z (exp_p0_pos a) (p0_lt_one ha_gt)
  refine ⟨⟨a, 2 * Real.exp (-a ^ 2 / 2), z,
    davisPowerB / gaussianPDFReal 0 1 z⟩, ?_, ?_⟩
  · exact ⟨ha_gt, ha_eq, rfl, exp_p0_pos a, p0_lt_one ha_gt, hz_eq, rfl⟩
  · rintro r ⟨ra_gt, ra_eq, rp0, _, _, rz_eq, rc0⟩
    have ha_eq_a : r.a = a := unique_a ra_gt ra_eq ha_gt ha_eq
    have hp_eq : r.p0 = 2 * Real.exp (-a ^ 2 / 2) := by rw [rp0, ha_eq_a]
    have hz_eq_z : r.z = z := by
      refine unique_z ?_ hz_eq
      rw [rz_eq, hp_eq]
    have hc_eq : r.c0 = davisPowerB / gaussianPDFReal 0 1 z := by
      rw [rc0, hz_eq_z]
    exact DavisPowerSolution.ext ha_eq_a hp_eq hz_eq_z hc_eq

end MathlibExt.Probability.ConvexSubGaussianComparisonWanted
