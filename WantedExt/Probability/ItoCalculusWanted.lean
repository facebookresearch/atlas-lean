/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.ItoIntegral

/-!
# Wanted: remaining statements of Itô calculus

`MathlibExt.Probability.ItoIntegral` constructs the Itô integral `ProbabilityTheory.itoIntegral`
as the `L²` extension of the elementary Itô integral, and proves the Itô isometry and the
martingale property for every integrand that is an `L²(P ⊗ du)`-limit of elementary integrands
(`ProbabilityTheory.IsItoApproximable`), the value on elementary integrands, Wiener's integration
by parts for deterministic `C¹` integrands, and the identification of the Itô form of the
Ornstein–Uhlenbeck solution with `ProbabilityTheory.ouPathSolution`.
`MathlibExt.Probability.ItoDensity` proves that every progressive integrand with
`E ∫_0^t H² < ∞` is Itô-approximable, so the isometry (with square integrability of the integral,
`ProbabilityTheory.memLp_itoIntegral`) and the martingale property hold for progressive
integrands. This file records what is still missing.

* `itoIntegral_add`, `itoIntegral_smul`, `itoIntegral_isometry_sub`: linearity and the difference
  isometry for progressive integrands.
* `itoIntegral_continuous_modification`: the Itô integral has a version with continuous paths.

Itô's formula is proved in `MathlibExt.Probability.ItoFormula`, and
`MathlibExt.Probability.OrnsteinUhlenbeckSDE` proves that the pathwise solution driven by a
Brownian motion is an Ornstein–Uhlenbeck process.

Brownian motion with respect to a filtration `F` is spelled out by hypotheses:
`IsBrownianReal B P`, `Adapted F B`, and independence of each increment `B t - B s` from `F s`.
Time integrals over `[0, t]` of processes indexed by `ℝ≥0` are written as interval integrals of
`u ↦ H (Real.toNNReal u)`; square integrability is stated with lower Lebesgue integrals, so that
no junk value of the Bochner integral can make a hypothesis vacuous.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991: Section 3.2 (construction and isometry).
* B. Øksendal, *Stochastic Differential Equations*, 6th ed., Springer, 2003, Chapter 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExt.Probability.ItoCalculusWanted

/-- **Linearity (additivity).** The Itô integral is additive in the integrand: for
`F`-progressive integrands `H₁, H₂` with `E ∫_0^t H_i² du < ∞`, the integral of the sum is almost
surely the sum of the integrals. Together with homogeneity and the difference isometry this pins
down the integral on the whole `L²` space of progressive integrands. -/
public theorem_wanted itoIntegral_add {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂) (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegral P F B (H₁ + H₂) t =ᵐ[P]
      fun ω ↦ itoIntegral P F B H₁ t ω + itoIntegral P F B H₂ t ω

/-- **Linearity (homogeneity).** The Itô integral is homogeneous in the integrand. -/
public theorem_wanted itoIntegral_smul {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (a : ℝ) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    itoIntegral P F B (a • H) t =ᵐ[P] fun ω ↦ a * itoIntegral P F B H t ω

/-- **Difference isometry.** For two `F`-progressive integrands with `E ∫_0^t H_i² du < ∞`, the
difference of the integrals is square-integrable and
`E[(∫ H₁ dB - ∫ H₂ dB)²] = E ∫ (H₁ - H₂)² du`. With linearity this is the two-integrand isometry
that, together with the elementary-integrand formula, determines the construction on the whole
`L²` space. -/
public theorem_wanted itoIntegral_isometry_sub {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H₁ H₂ : ℝ≥0 → Ω → ℝ} (hH₁ : IsProgressive F H₁) (hH₂ : IsProgressive F H₂) (t : ℝ≥0)
    (hH₁2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hH₂2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₂ u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    MemLp (fun ω ↦ itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω) 2 P ∧
      ∫⁻ ω, ‖itoIntegral P F B H₁ t ω - itoIntegral P F B H₂ t ω‖ₑ ^ 2 ∂P =
        ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H₁ u.toNNReal ω - H₂ u.toNNReal ω‖ₑ ^ 2) ∂P

/-- **Continuous modification.** The Itô integral admits a modification with continuous paths:
there is a process `J` with continuous paths such that `J t = ∫_0^t H dB` almost surely for each
`t` (Karatzas–Shreve 1991, Section 3.2). `ProbabilityTheory.itoIntegral` chooses its version
separately at each time, so it is only determined up to a null set that may depend on `t`; the
statement therefore asks for a modification rather than for a process indistinguishable from
this particular choice. Any two continuous modifications are indistinguishable. -/
public theorem_wanted itoIntegral_continuous_modification {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hH2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    ∃ J : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t ↦ J t ω) ∧
      ∀ t, J t =ᵐ[P] itoIntegral P F B H t

end MathlibExt.Probability.ItoCalculusWanted
