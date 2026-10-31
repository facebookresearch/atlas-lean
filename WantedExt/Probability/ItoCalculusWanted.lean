/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import MathlibExt.Probability.ItoIntegral

/-!
# Wanted: density of elementary integrands, Itô's formula, and the OU process from the SDE

`MathlibExt.Probability.ItoIntegral` constructs the Itô integral `ProbabilityTheory.itoIntegral`
as the `L²` extension of the elementary Itô integral, and proves the Itô isometry and the
martingale property for every integrand that is an `L²(P ⊗ du)`-limit of elementary integrands
(`ProbabilityTheory.IsItoApproximable`), the value on elementary integrands, Wiener's integration
by parts for deterministic `C¹` integrands, and the identification of the Itô form of the
Ornstein–Uhlenbeck solution with `ProbabilityTheory.ouPathSolution`.
`MathlibExt.Probability.ItoDensity` proves that every progressive integrand with
`E ∫_0^t H² < ∞` is Itô-approximable, so the isometry and the martingale property hold for
progressive integrands. This file records what is still missing.

* `ito_formula`: Itô's formula for `f(B_t)` with `f` of class `C²` with bounded first and second
  derivatives; it needs the quadratic variation of Brownian motion, which is not formalized.
* `isOrnsteinUhlenbeckFromZero_ouPathSolution`, `isStationaryOrnsteinUhlenbeck_ouPathSolution`: the
  pathwise solution driven by a Brownian motion is an OU process (started at `0`, or stationary
  when started from an independent `N(0, σ² / (2θ))` variable). The missing ingredients are the
  closure of jointly Gaussian vectors under `L²` limits (Mathlib has no such statement) and the
  covariance computation `E[I_s I_t] = ∫_0^{s ∧ t} e^{2θu} du` for the Wiener integrals
  `I_t = ∫_0^t e^{θu} dB_u`.

Brownian motion with respect to a filtration `F` is spelled out by hypotheses:
`IsBrownianReal B P`, `Adapted F B`, and independence of each increment `B t - B s` from `F s`.
Time integrals over `[0, t]` of processes indexed by `ℝ≥0` are written as interval integrals of
`u ↦ H (Real.toNNReal u)`; square integrability is stated with lower Lebesgue integrals, so that
no junk value of the Bochner integral can make a hypothesis vacuous.

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
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExt.Probability.ItoCalculusWanted

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
      fun ω ↦ f (B 0 ω) + itoIntegral P F B (fun u ω' ↦ deriv f (B u ω')) t ω +
        (1 / 2) * ∫ u in (0 : ℝ)..t, deriv (deriv f) (B (Real.toNNReal u) ω)

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
