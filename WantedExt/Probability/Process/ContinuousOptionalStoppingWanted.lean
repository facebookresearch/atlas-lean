/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Martingale.OptionalSampling

/-!
# Wanted: the optional stopping theorem in continuous time

Mathlib's optional sampling theorem (`MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le`)
is stated for a countable time set, or for stopping times with countable range; the repository's
optional stopping results are in discrete time. The continuous-time theorem for martingales with
continuous paths, which Le Gall's book proves by approximating the stopping times from above by
dyadic ones, is recorded here.

## References

* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 3, section "Optional stopping theorems".
* J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires* (ENS lecture notes),
  Théorème 12.5.4 (the discrete-time statement).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathlibExt.Probability.ContinuousOptionalStoppingWanted

/-- **Optional stopping theorem in continuous time.** Let `M` be a real martingale indexed by
`ℝ≥0` with continuous paths, on a probability space, and let `σ ≤ τ` be stopping times bounded by
a constant `n`. Then `M_σ = E[M_τ | F_σ]` almost surely (Le Gall, *Brownian Motion, Martingales,
and Stochastic Calculus*, Chapter 3, section "Optional stopping theorems", stated there for
uniformly integrable martingales with right-continuous paths; a martingale on `[0, n]` is
uniformly integrable). -/
theorem_wanted Martingale.stoppedValue_ae_eq_condExp_of_le_of_continuous {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) {n : ℝ≥0}
    (hτn : ∀ ω, τ ω ≤ n) :
    stoppedValue M σ =ᵐ[μ] μ[stoppedValue M τ | hσ.measurableSpace]

end MathlibExt.Probability.ContinuousOptionalStoppingWanted
