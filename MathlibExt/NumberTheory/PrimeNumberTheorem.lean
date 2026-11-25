/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import MathlibExt.Analysis.Asymptotics.MonotoneIntegralCriterion
import MathlibExt.Analysis.LaplaceTransform.ExponentialBound
import MathlibExt.Analysis.LaplaceTransform.NewmanTauberian
import MathlibExt.Analysis.PerronKernel
import MathlibExt.NumberTheory.PrimeCounting.Chebyshev
import MathlibExt.NumberTheory.PrimeCounting.LaplaceThetaContinuation
import MathlibExt.NumberTheory.PrimeCounting.NormalizedThetaError

open Filter MeasureTheory Set Topology
open scoped Asymptotics

/-! Private helpers for Newman's analytic theorem and the
PNT deduction. All names are prefixed `pnt_` and private. -/

/-- Convergence of `∫ H`. -/
private lemma pnt_integral_H_tendsto :
    ∃ L : ℝ, Filter.Tendsto
      (fun U : ℝ => ∫ u : ℝ in (0 : ℝ)..U, Chebyshev.normalizedThetaError u)
      Filter.atTop (𝓝 L) := by
  have hmeas : Measurable (fun t : ℝ => (Chebyshev.normalizedThetaError t : ℂ)) :=
    Complex.measurable_ofReal.comp Chebyshev.measurable_normalizedThetaError
  have hfmeas : AEStronglyMeasurable (fun t : ℝ => (Chebyshev.normalizedThetaError t : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hmeas.aestronglyMeasurable
  have hB : (0 : ℝ) ≤ Real.log 4 + 1 := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖(Chebyshev.normalizedThetaError t : ℂ)‖ ≤ Real.log 4 + 1 := by
    intro t _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Chebyshev.abs_normalizedThetaError_le t
  have hmain := newman_tauberian (fun t : ℝ => (Chebyshev.normalizedThetaError t : ℂ))
    (Real.log 4 + 1) hfmeas hB hbound Chebyshev.normalizedThetaErrorContinuation
    Chebyshev.normalizedThetaErrorContinuation_analyticOn
    Chebyshev.hasLaplace_normalizedThetaError
  refine ⟨(Chebyshev.normalizedThetaErrorContinuation 0).re, ?_⟩
  have hcast : ∀ U : ℝ,
      ((∫ u : ℝ in (0 : ℝ)..U, (Chebyshev.normalizedThetaError u : ℂ)).re)
        = ∫ u : ℝ in (0 : ℝ)..U, Chebyshev.normalizedThetaError u := by
    intro U
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have h2 := (Complex.continuous_re.tendsto
    (Chebyshev.normalizedThetaErrorContinuation 0)).comp hmain
  have e : (fun U : ℝ => ∫ u : ℝ in (0 : ℝ)..U, Chebyshev.normalizedThetaError u)
      = Complex.re ∘ (fun T : ℝ => ∫ u : ℝ in (0 : ℝ)..T,
        (Chebyshev.normalizedThetaError u : ℂ)) :=
    funext fun U => (hcast U).symm
  rw [e]
  exact h2

/-- The substitution `t = e^u` turns the `θ` integral into `∫ H`. -/
private lemma pnt_integral_theta_eq_integral_H (x : ℝ) (hx : 1 ≤ x) :
    ∫ t : ℝ in Set.Ioc 1 x, (Chebyshev.theta t - t) / t ^ 2
      = ∫ u : ℝ in (0 : ℝ)..Real.log x, Chebyshev.normalizedThetaError u := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have himg : Set.Ioc 1 x = Real.exp '' Set.Ioc 0 (Real.log x) := by
    rw [Real.image_exp_Ioc, Real.exp_zero, Real.exp_log hx0]
  -- Pointwise identification of the substituted integrand with `H`.
  have hpt : ∀ u : ℝ, |Real.exp u| • ((Chebyshev.theta (Real.exp u) - Real.exp u)
      / (Real.exp u) ^ 2) = Chebyshev.normalizedThetaError u := by
    intro u
    have hne : Real.exp u ≠ 0 := Real.exp_ne_zero u
    have hexp : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [abs_of_pos (Real.exp_pos u), smul_eq_mul]
    unfold Chebyshev.normalizedThetaError
    field_simp
    linear_combination (-(Chebyshev.theta (Real.exp u))) * hexp
  have hchange : (∫ t : ℝ in Real.exp '' Set.Ioc 0 (Real.log x),
        (Chebyshev.theta t - t) / t ^ 2)
      = ∫ u : ℝ in Set.Ioc 0 (Real.log x),
        |Real.exp u| • ((Chebyshev.theta (Real.exp u) - Real.exp u)
          / (Real.exp u) ^ 2) :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioc
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
      (Real.exp_injective.injOn) _
  have step1 : (∫ t : ℝ in Set.Ioc 1 x, (Chebyshev.theta t - t) / t ^ 2)
      = ∫ u : ℝ in Set.Ioc 0 (Real.log x),
        |Real.exp u| • ((Chebyshev.theta (Real.exp u) - Real.exp u)
          / (Real.exp u) ^ 2) := by
    rw [himg]
    exact hchange
  have step2 : (∫ u : ℝ in Set.Ioc 0 (Real.log x),
        |Real.exp u| • ((Chebyshev.theta (Real.exp u) - Real.exp u)
          / (Real.exp u) ^ 2))
      = ∫ u : ℝ in Set.Ioc 0 (Real.log x), Chebyshev.normalizedThetaError u :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u _ => hpt u)
  have step3 : (∫ u : ℝ in Set.Ioc 0 (Real.log x), Chebyshev.normalizedThetaError u)
      = ∫ u : ℝ in (0 : ℝ)..Real.log x, Chebyshev.normalizedThetaError u :=
    (intervalIntegral.integral_of_le hlog).symm
  exact step1.trans (step2.trans step3)

/-- Convergence of the `θ` integral. -/
private lemma pnt_integral_theta_tendsto :
    ∃ L : ℝ, Filter.Tendsto
      (fun x => ∫ t : ℝ in Set.Ioc 1 x, (Chebyshev.theta t - t) / t ^ 2)
      Filter.atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := pnt_integral_H_tendsto
  refine ⟨L, ?_⟩
  have hcomp : Filter.Tendsto
      (fun x : ℝ => ∫ u : ℝ in (0 : ℝ)..Real.log x,
        Chebyshev.normalizedThetaError u)
      Filter.atTop (𝓝 L) :=
    hL.comp Real.tendsto_log_atTop
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have hev := h1.mono
    (fun x hx => (pnt_integral_theta_eq_integral_H x hx).symm)
  exact Filter.Tendsto.congr' hev hcomp

/-- `θ ~ id`. -/
private lemma pnt_theta_isEquivalent :
    Chebyshev.theta ~[Filter.atTop] (fun x : ℝ => x) := by
  obtain ⟨L, hL⟩ := pnt_integral_theta_tendsto
  exact Asymptotics.isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq
    Chebyshev.theta (Chebyshev.theta_mono.monotoneOn _) ⟨L, hL⟩

/-- Step (VI) over `ℝ`. -/
private lemma pnt_primeCounting_floor_isEquivalent :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[Filter.atTop]
      (fun x => x / Real.log x) :=
  Chebyshev.primeCounting_isEquivalent_of_theta_isEquivalent
    pnt_theta_isEquivalent

/-- Transfer from `ℝ` to `ℕ`. -/
private lemma pnt_nat_transfer
    (h : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[Filter.atTop]
      (fun x => x / Real.log x)) :
    Asymptotics.IsEquivalent (Filter.atTop : Filter ℕ)
      (fun n : ℕ => (Nat.primeCounting n : ℝ))
      (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  have hcast := h.comp_tendsto tendsto_natCast_atTop_atTop
  have eleft : ((fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ∘ ((↑) : ℕ → ℝ))
      = (fun n : ℕ => (Nat.primeCounting n : ℝ)) := by
    funext n
    simp only [Function.comp_apply, Nat.floor_natCast]
  have eright : ((fun x : ℝ => x / Real.log x) ∘ ((↑) : ℕ → ℝ))
      = (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := rfl
  rw [eleft, eright] at hcast
  exact hcast

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeNumberTheoremWanted

/-!
# Prime number theorem
This file proves the prime number theorem following Newman's analytic proof: D. J. Newman,
"Simple analytic proof of the prime number theorem", Amer. Math. Monthly 87 (1980) 693–696, in the
form of D. Zagier, "Newman's short proof of the prime number theorem", Amer. Math. Monthly 104
(1997) 705–708. The historical sources of the statement are in the docstring of
`prime_number_theorem`.
-/

/--
**Prime number theorem.** Let $\pi(n)$ be the number of primes $p \le n$. Then
$\pi(n) \sim n / \log n$ as $n \to \infty$ through the natural numbers, that is,
$\pi(n) - n / \log n = o(n / \log n)$, where $\log$ is the natural logarithm.

Proves `Wanted` entry `prime_number_theorem`.

Source: J. Hadamard and C. de la
Vallée Poussin, 1896 independent proofs of PNT; original: Hadamard, Sur la distribution des zéros
de ζ, Bull. Soc. Math. France 24 (1896) 199–220, de la Vallée Poussin, Recherches analytiques,
Ann. Soc. Sci. Bruxelles 20 (1896); textbook in Apostol, Introduction to Analytic Number Theory
-/
public theorem prime_number_theorem :
    Asymptotics.IsEquivalent (Filter.atTop : Filter ℕ)
      (fun n : ℕ => (Nat.primeCounting n : ℝ))
      (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) :=
  pnt_nat_transfer pnt_primeCounting_floor_isEquivalent

end MathlibExt.NumberTheory.PrimeNumberTheoremWanted
