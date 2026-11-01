/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import MathlibExt.Probability.OrnsteinUhlenbeck

/-!
# Wanted: the Itô integral, Itô's formula and the Ornstein–Uhlenbeck SDE

Pinned Mathlib defines Brownian motion through its finite-dimensional laws
(`ProbabilityTheory.IsPreBrownianReal`, `ProbabilityTheory.IsBrownianReal`) but has no
stochastic integral, no quadratic variation and no theory of stochastic differential equations.
This file records the missing pieces needed to state the Ornstein–Uhlenbeck SDE
`dX = -θ X dt + σ dW` in its Itô form.

* `itoIntegral`: the Itô integral `∫_0^t H_u dB_u` (a missing construction).
* `itoIntegral_indicator_Ioc`: its value on elementary integrands, which pins down the hole.
* `itoIntegral_isometry`, `martingale_itoIntegral`: the Itô isometry and the martingale property.
* `itoIntegral_deterministic_eq`: Wiener's integration by parts for a `C¹` deterministic
  integrand.
* `ito_formula`: Itô's formula for `f(B_t)` with `f` of class `C²` with bounded first and second
  derivatives.
* `ito_ou_solution_eq_ouPathSolution`: the Itô form `e^{-θt} X₀ + σ ∫_0^t e^{-θ(t-s)} dB_s` of
  the OU solution agrees with the pathwise solution `ouPathSolution` of
  `MathlibExt.Probability.OrnsteinUhlenbeck` (which is proved there to solve
  `X t = X₀ - θ ∫_0^t X + σ (B t - B 0)` path by path).
* `isOrnsteinUhlenbeckFromZero_ouPathSolution`, `isStationaryOrnsteinUhlenbeck_ouPathSolution`: the
  pathwise solution driven by a Brownian motion is an OU process (started at `0`, or stationary
  when started from an independent `N(0, σ² / (2θ))` variable). These need no stochastic
  integral; the gap is that a pathwise Riemann integral of a continuous Gaussian process is
  jointly Gaussian with the process (a.s. limits of Gaussian vectors are Gaussian), which pinned
  Mathlib lacks.

Brownian motion with respect to a filtration `F` is spelled out by hypotheses:
`IsBrownianReal B P`, `Adapted F B`, and independence of each increment `B t - B s` from `F s`.
Time integrals over `[0, t]` of processes indexed by `ℝ≥0` are written as interval integrals of
`u ↦ H (Real.toNNReal u)`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991: Section 3.2 (construction and isometry), Section 3.3 (Itô's rule), Section 5.6 (linear
  equations and the Ornstein–Uhlenbeck process).
* B. Øksendal, *Stochastic Differential Equations*, 6th ed., Springer, 2003, Chapters 3–5.
* G. E. Uhlenbeck and L. S. Ornstein, *On the theory of the Brownian motion*, Phys. Rev. 36
  (1930), 823–841.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ProbabilityTheory

namespace MathlibExt.Probability.ItoCalculusWanted

/-- The **Itô integral** `t ↦ ∫_0^t H_u dB_u` of an `F`-progressive integrand `H` with
`E ∫_0^t H_u² du < ∞` against an `F`-Brownian motion `B`, as a real process (determined up to
indistinguishability; Karatzas–Shreve 1991, Definition 3.2.9). Mathlib has no stochastic
integral. -/
public def_wanted itoIntegral {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) (B H : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ

/-- **Elementary integrands.** For `a < b` and a bounded `F a`-measurable `ξ`, the Itô integral
of `ξ 1_{(a, b]}` against an `F`-Brownian motion `B` is `ξ (B (b ∧ t) - B (a ∧ t))` almost surely
(Karatzas–Shreve 1991, Section 3.2.A). -/
public theorem_wanted itoIntegral_indicator_Ioc {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {a b : ℝ≥0} (hab : a < b) {ξ : Ω → ℝ} (hξ : Measurable[F a] ξ) (C : ℝ)
    (hξC : ∀ ω, |ξ ω| ≤ C) (t : ℝ≥0) :
    ❰itoIntegral❱ P F B (fun u ω ↦ Set.indicator (Set.Ioc a b) (fun _ ↦ ξ ω) u) t =ᵐ[P]
      fun ω ↦ ξ ω * (B (min b t) ω - B (min a t) ω)

/-- **Itô isometry.** For an `F`-progressive integrand `H` with genuine `L²` integrability —
for a.e. `ω` the time integral `∫_0^t H_u² du` is `IntervalIntegrable` (so it is not the
totalized `0` of a nonintegrable integrand) and the resulting expectation is integrable —
the Itô integral at `t` is square-integrable and
`E[(∫_0^t H dB)²] = E ∫_0^t H_u² du` (Karatzas–Shreve 1991, Section 3.2). -/
public theorem_wanted itoIntegral_isometry {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (t : ℝ≥0)
    (hH2int : ∀ᵐ ω ∂P, IntervalIntegrable (fun u => (H (Real.toNNReal u) ω) ^ 2)
      volume (0 : ℝ) t)
    (hH2 : Integrable (fun ω ↦ ∫ u in (0 : ℝ)..t, H (Real.toNNReal u) ω ^ 2) P) :
    MemLp (fun ω ↦ ❰itoIntegral❱ P F B H t ω) 2 P ∧
      P[fun ω ↦ (❰itoIntegral❱ P F B H t ω) ^ 2] =
        P[fun ω ↦ ∫ u in (0 : ℝ)..t, H (Real.toNNReal u) ω ^ 2]

/-- **Martingale property.** For an `F`-progressive integrand `H` with genuine `L²`
integrability at every `t` (a.e. `IntervalIntegrable` time integrals with integrable
expectation, as in `itoIntegral_isometry`), the Itô integral `t ↦ ∫_0^t H dB` is an
`F`-martingale (Karatzas–Shreve 1991, Proposition 3.2.10). -/
public theorem_wanted martingale_itoIntegral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hH2int : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, IntervalIntegrable (fun u => (H (Real.toNNReal u) ω) ^ 2)
      volume (0 : ℝ) t)
    (hH2 : ∀ t : ℝ≥0, Integrable (fun ω ↦ ∫ u in (0 : ℝ)..t, H (Real.toNNReal u) ω ^ 2) P) :
    Martingale (❰itoIntegral❱ P F B H) F P

/-- **Wiener's integration by parts.** For a `C¹` deterministic integrand `g`,
`∫_0^t g dB = g t B t - g 0 B 0 - ∫_0^t g'(u) B u du` almost surely (Karatzas–Shreve 1991,
Section 3.3; the right side is a pathwise Riemann integral). -/
public theorem_wanted itoIntegral_deterministic_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (t : ℝ≥0) :
    ❰itoIntegral❱ P F B (fun u _ ↦ g u) t =ᵐ[P]
      fun ω ↦ g t * B t ω - g 0 * B 0 ω -
        ∫ u in (0 : ℝ)..t, deriv g u * B (Real.toNNReal u) ω

/-- **Itô's formula** for Brownian motion: for `f` of class `C²` with bounded `f'` and `f''`,
`f(B t) = f(B 0) + ∫_0^t f'(B u) dB u + (1/2) ∫_0^t f''(B u) du` almost surely
(Karatzas–Shreve 1991, Theorem 3.3.3). -/
public theorem_wanted ito_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (C : ℝ) (hf1 : ∀ x, |deriv f x| ≤ C)
    (hf2 : ∀ x, |deriv (deriv f) x| ≤ C) (t : ℝ≥0) :
    (fun ω ↦ f (B t ω)) =ᵐ[P]
      fun ω ↦ f (B 0 ω) + ❰itoIntegral❱ P F B (fun u ω' ↦ deriv f (B u ω')) t ω +
        (1 / 2) * ∫ u in (0 : ℝ)..t, deriv (deriv f) (B (Real.toNNReal u) ω)

/-- **The OU solution in Itô form.** For an `F 0`-measurable initial value `X₀`, the Itô form
`e^{-θt} X₀ + σ e^{-θt} ∫_0^t e^{θs} dB_s = e^{-θt} X₀ + σ ∫_0^t e^{-θ(t-s)} dB_s` of the solution
of `dX = -θ X dt + σ dB` (Karatzas–Shreve 1991, Section 5.6) agrees almost surely with the
pathwise solution `ouPathSolution`, which solves `X t = X₀ - θ ∫_0^t X + σ (B t - B 0)` path by
path (`ProbabilityTheory.ouPathSolution_integral_eq`). -/
public theorem_wanted ito_ou_solution_eq_ouPathSolution {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    (θ σ : ℝ) {X₀ : Ω → ℝ} (hX₀ : Measurable[F 0] X₀) (t : ℝ≥0) :
    (fun ω ↦ exp (-θ * t) * X₀ ω +
        σ * exp (-θ * t) * ❰itoIntegral❱ P F B (fun u _ ↦ exp (θ * u)) t ω) =ᵐ[P]
      fun ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) t

/-- **The pathwise Langevin solution is an OU process.** Driven by a Brownian motion and started
at `0`, `ouPathSolution` is an Ornstein–Uhlenbeck process started at `0` (Karatzas–Shreve 1991,
Section 5.6). The missing ingredient is the Gaussianity of pathwise integrals of a continuous
Gaussian process. -/
public theorem_wanted isOrnsteinUhlenbeckFromZero_ouPathSolution {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) :
    IsOrnsteinUhlenbeckFromZero θ σ
      (fun t ω ↦ ouPathSolution θ σ 0 (fun u ↦ B (Real.toNNReal u) ω) t) P

/-- **Stationary start.** Driven by a Brownian motion `B` and started from `X₀ ~ N(0, σ²/(2θ))`
independent of `B`, `ouPathSolution` is a stationary Ornstein–Uhlenbeck process
(Karatzas–Shreve 1991, Section 5.6). -/
public theorem_wanted isStationaryOrnsteinUhlenbeck_ouPathSolution {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) {X₀ : Ω → ℝ}
    (hX₀ : HasLaw X₀ (gaussianReal 0 (σ ^ 2 / (2 * θ)).toNNReal) P)
    (hind : IndepFun X₀ (fun ω t ↦ B t ω) P) :
    IsStationaryOrnsteinUhlenbeck θ σ
      (fun t ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) t) P

end MathlibExt.Probability.ItoCalculusWanted
