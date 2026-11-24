/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Wanted: nowhere differentiability of Brownian paths

The Paley–Wiener–Zygmund theorem for real Brownian motion (Mathlib's `IsBrownianReal`), which the
repository does not yet prove. The proved neighbours are the existence of a continuous version
(`MathlibExt.Probability.BrownianMotionExistence`), Hölder continuity of every order `< 1/2`
(`MathlibExt.Probability.BrownianHolder`), the quadratic variation
(`MathlibExt.Probability.BrownianQuadraticVariation`) and unbounded variation
(`MathlibExt.Probability.BrownianUnboundedVariation`).

## References

* P. Mörters and Y. Peres, *Brownian Motion*, Cambridge University Press, 2010, Theorem 1.30
  (Paley, Wiener and Zygmund 1933).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExt.Probability.BrownianSamplePathsWanted

/-- **Brownian paths are nowhere differentiable** (Paley, Wiener and Zygmund). Almost surely, the
path `s ↦ B s ω` is differentiable at no time `t > 0` (Mörters and Peres, *Brownian Motion*,
Cambridge University Press, 2010, Theorem 1.30). The statement is restricted to `t > 0` because
the path is extended by `B 0` to negative times, so a two-sided derivative at `0` is not the
Brownian one. -/
theorem_wanted IsBrownianReal.ae_not_differentiableAt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ¬ DifferentiableAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) t

end MathlibExt.Probability.BrownianSamplePathsWanted
