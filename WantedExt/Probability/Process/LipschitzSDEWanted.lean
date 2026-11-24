/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Probability.ItoIntegral

/-!
# Wanted: strong solutions of SDEs with Lipschitz coefficients

Itô's theorem on stochastic differential equations `dX_t = σ(X_t) dB_t + b(X_t) dt` with
Lipschitz coefficients: strong existence and pathwise uniqueness. The stochastic integral is the
repository's `L²` Itô integral `ProbabilityTheory.itoIntegral`, so the solution class is restricted
to continuous adapted processes with `E ∫_0^t X_s² ds < ∞`. The repository already solves one
linear SDE explicitly: the Langevin equation of the Ornstein–Uhlenbeck process
(`MathlibExt.Probability.OrnsteinUhlenbeckSDE`).

## References

* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 8,
  section "The Lipschitz case".
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Section 5.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExt.Probability.LipschitzSDEWanted

/-- **Strong solutions of SDEs with Lipschitz coefficients.** Let `B` be a Brownian motion with
continuous paths for a filtration `F` (adapted, with increments independent of the past), and let
`σ, b : ℝ → ℝ` be Lipschitz. For every `x`, the equation
`X_t = x + ∫_0^t σ(X_s) dB_s + ∫_0^t b(X_s) ds` has a solution `X` that is adapted, has
continuous paths and satisfies `E ∫_0^t X_s² ds < ∞` for every `t`, and any two such solutions
are indistinguishable. The stochastic integral is the `L²` Itô integral
`ProbabilityTheory.itoIntegral` of the repository, whence the square-integrability condition on
the solution class. Le Gall, GTM 274, Chapter 8, section "The Lipschitz case" (pathwise uniqueness
and strong existence); I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*,
Section 5.2. -/
theorem_wanted sde_lipschitz_existsUnique {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBcont : ∀ ω, Continuous fun t ↦ B t ω) (hBF : Adapted F B)
    (hBindep : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {σ b : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b) (x : ℝ) :
    (∃ X : ℝ≥0 → Ω → ℝ, Adapted F X ∧ (∀ ω, Continuous fun t ↦ X t ω) ∧
        (∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖X u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) ∧
        ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X t ω = x + itoIntegral P F B (fun u ω ↦ σ (X u ω)) t ω +
          ∫ u in (0 : ℝ)..t, b (X u.toNNReal ω)) ∧
      ∀ X Y : ℝ≥0 → Ω → ℝ,
        (Adapted F X ∧ (∀ ω, Continuous fun t ↦ X t ω) ∧
          (∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖X u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) ∧
          ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X t ω = x + itoIntegral P F B (fun u ω ↦ σ (X u ω)) t ω +
            ∫ u in (0 : ℝ)..t, b (X u.toNNReal ω)) →
        (Adapted F Y ∧ (∀ ω, Continuous fun t ↦ Y t ω) ∧
          (∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖Y u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) ∧
          ∀ t : ℝ≥0, ∀ᵐ ω ∂P, Y t ω = x + itoIntegral P F B (fun u ω ↦ σ (Y u ω)) t ω +
            ∫ u in (0 : ℝ)..t, b (Y u.toNNReal ω)) →
        ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω

end MathlibExt.Probability.LipschitzSDEWanted
