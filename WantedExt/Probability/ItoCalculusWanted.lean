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
# Wanted: density of elementary integrands

`MathlibExt.Probability.ItoIntegral` constructs the Itô integral `ProbabilityTheory.itoIntegral`
as the `L²` extension of the elementary Itô integral, and proves the Itô isometry and the
martingale property for every integrand that is an `L²(P ⊗ du)`-limit of elementary integrands
(`ProbabilityTheory.IsItoApproximable`), the value on elementary integrands, Wiener's integration
by parts for deterministic `C¹` integrands, and the identification of the Itô form of the
Ornstein–Uhlenbeck solution with `ProbabilityTheory.ouPathSolution`.
`MathlibExt.Probability.ItoFormula` proves Itô's formula and
`MathlibExt.Probability.OrnsteinUhlenbeckSDE` proves that the pathwise solution driven by a
Brownian motion is an Ornstein–Uhlenbeck process. This file records what is still missing.

* `isItoApproximable_of_isProgressive`: every progressive integrand with `E ∫_0^t H² < ∞` is
  Itô-approximable (Karatzas–Shreve 1991, Lemma 3.2.4 and Proposition 3.2.6). With it, the
  isometry and the martingale property below follow from
  `ProbabilityTheory.lintegral_itoIntegral_sq` and `ProbabilityTheory.martingale_itoIntegral`.
* `itoIntegral_isometry`, `martingale_itoIntegral`: the Itô isometry and the martingale property
  for progressive integrands.

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

/-- **Density of elementary integrands.** A progressive integrand `H` with
`E ∫_0^t H_u² du < ∞` is the `L²(P ⊗ du)`-limit on `(0, t] × Ω` of elementary integrands
(Karatzas–Shreve 1991, Lemma 3.2.4 and Proposition 3.2.6). -/
public theorem_wanted isItoApproximable_of_isProgressive {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsProgressive F H) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    IsItoApproximable P F H t

/-- **Itô isometry.** For an `F`-progressive integrand `H` with `E ∫_0^t H_u² du < ∞`,
`E[(∫_0^t H dB)²] = E ∫_0^t H_u² du` (Karatzas–Shreve 1991, Section 3.2). -/
public theorem_wanted itoIntegral_isometry {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    ∫⁻ ω, ‖itoIntegral P F B H t ω‖ₑ ^ 2 ∂P =
      ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P

/-- **Martingale property.** For an `F`-progressive integrand `H` with `E ∫_0^t H_u² du < ∞`
for every `t`, the Itô integral `t ↦ ∫_0^t H dB` is an `F`-martingale (Karatzas–Shreve 1991,
Proposition 3.2.10). -/
public theorem_wanted martingale_itoIntegral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hH2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    Martingale (itoIntegral P F B H) F P

end MathlibExt.Probability.ItoCalculusWanted
