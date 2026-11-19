/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Wanted: Doob's `L^p` inequality in continuous time

Doob's maximal inequality in `L^p` for nonnegative submartingales indexed by `ℝ≥0` with continuous
paths. The repository proves Doob's `L²` maximal inequality in discrete time
(`MathlibExt.Probability.DoobLpInequality`); the continuous-time statement follows from the
discrete one along dyadic times and monotone convergence, and it is the inequality behind the
continuity of stochastic integrals and the Burkholder–Davis–Gundy inequalities.

## References

* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 3, section "Continuous time martingales and
  supermartingales".
* J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires* (ENS lecture notes),
  Proposition 12.4.3 (the discrete-time statement).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace MathlibExt.Probability.ContinuousDoobWanted

/-- **Doob's `L^p` maximal inequality in continuous time.** Let `X` be a nonnegative
submartingale indexed by `ℝ≥0` with continuous paths, and `p > 1`. For every `t ≥ 0`,
`E[(sup_{0 ≤ s ≤ t} X s)^p] ≤ (p / (p - 1))^p E[X_t^p]` (Le Gall, *Brownian Motion, Martingales,
and Stochastic Calculus*, Chapter 3, section "Continuous time martingales and supermartingales";
the discrete-time inequality is Proposition 12.4.3 of his ENS notes). The integrals are lower
Lebesgue integrals, so the statement needs no integrability assumption on `X_t^p`. -/
theorem_wanted Submartingale.lintegral_iSup_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X : ℝ≥0 → Ω → ℝ} (hX : Submartingale X ℱ μ) (hnonneg : ∀ t ω, 0 ≤ X t ω)
    (hcont : ∀ ω, Continuous fun t ↦ X t ω) {p : ℝ} (hp : 1 < p) (t : ℝ≥0) :
    ∫⁻ ω, (⨆ s : Set.Icc (0 : ℝ≥0) t, ENNReal.ofReal (X s ω)) ^ p ∂μ ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ ω, ENNReal.ofReal (X t ω) ^ p ∂μ

end MathlibExt.Probability.ContinuousDoobWanted
