/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Wanted: Girsanov's theorem for a constant drift

The simplest instance of Girsanov's theorem (equivalently, of the Cameron–Martin formula): after
the change of measure with density `exp(μ B_T - μ² T / 2)`, Brownian motion minus the drift `μ t`
has the finite-dimensional laws of Brownian motion on `[0, T]`. The general theorem (a drift
`∫_0^t H_s ds` with an exponential local martingale density, under Novikov's condition) needs
stochastic exponentials, which the repository does not have yet.

## References

* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 5,
  sections "Girsanov's theorem" and "A few applications of Girsanov's theorem".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExt.Probability.GirsanovWanted

/-- **Girsanov's theorem for a constant drift** (the Cameron–Martin formula for `h(t) = μ t`).
Let `B` be a Brownian motion, `μ` real and `T ≥ 0`, and let `Q` be the probability measure with
density `exp(μ B_T - μ² T / 2)` with respect to `P`. Under `Q`, the process `B t - μ t`,
`0 ≤ t ≤ T`, has the finite-dimensional laws of Brownian motion (Le Gall, GTM 274, Chapter 5,
sections "Girsanov's theorem" and "A few applications of Girsanov's theorem", with the drift
`∫_0^t μ ds`). -/
theorem_wanted IsBrownianReal.hasLaw_sub_drift_withDensity {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (μ : ℝ) (T : ℝ≥0)
    (I : Finset ℝ≥0) (hI : ∀ t ∈ I, t ≤ T) :
    HasLaw (fun ω ↦ I.restrict fun t ↦ B t ω - μ * t) (BrownianReal.projectiveFamily I)
      (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (μ * B T ω - μ ^ 2 * T / 2)))

end MathlibExt.Probability.GirsanovWanted
