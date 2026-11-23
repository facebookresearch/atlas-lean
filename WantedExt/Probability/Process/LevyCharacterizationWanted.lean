/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic

/-!
# Wanted: Lévy's characterisation of Brownian motion

Lévy's theorem: a continuous martingale `M` with `M 0 = 0` whose square compensated by `t` is
again a martingale is a Brownian motion for its filtration. It is the first of the "consequences
of Itô's formula" in Le Gall's book (applied to the exponential martingales
`exp(i ξ M_t + ξ² t / 2)`), and it is what turns quadratic variation into the identification of
Brownian motion. The statement here is the square-integrable martingale form; the book states it
for continuous local martingales with `⟨M, M⟩_t = t`.

## References

* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 5,
  section "Lévy's characterization of Brownian motion".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExt.Probability.LevyCharacterizationWanted

/-- **Lévy's characterisation of Brownian motion** (square-integrable martingale form). If `M` is
an `F`-martingale with continuous paths and `M 0 = 0`, and `M_t² - t` is also an `F`-martingale,
then `M` is a Brownian motion and each increment `M t - M s` (`s ≤ t`) is independent of `F s`.
Le Gall, GTM 274, Chapter 5, section "Lévy's characterization of Brownian motion", states the
result for continuous local martingales with quadratic variation `⟨M, M⟩_t = t`; this is its
special case for martingales, where `⟨M, M⟩_t = t` means that `M_t² - t` is a martingale. -/
theorem_wanted Martingale.isBrownianReal_of_martingale_sq_sub {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P) (hcont : ∀ ω, Continuous fun t ↦ M t ω)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - t) F P) :
    IsBrownianReal M P ∧
      ∀ s t : ℝ≥0, s ≤ t →
        Indep (MeasurableSpace.comap (fun ω ↦ M t ω - M s ω) inferInstance) (F s) P

end MathlibExt.Probability.LevyCharacterizationWanted
