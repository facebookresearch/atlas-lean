/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.SteinLemma

/-!
# James–Stein estimation: the positive-part estimator

`MathlibExt.Probability.Statistics.SteinLemma` proves that the James–Stein estimator shrinking
towards `0` dominates `X` for `p ≥ 3` (`integral_jamesStein_risk_lt`), and that the variant
shrinking towards the grand mean dominates `X` for `N ≥ 4` (`integral_jamesSteinGrandMean_risk_lt`;
Efron 2021, Theorem 1, credited there to James and Stein 1961). This file records the classical
improvement by the positive-part estimator (Johnstone 2019 draft, equation (2.65) and
Exercise 2.12): truncating the shrinkage factor at `0` does not increase the risk.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- **The positive-part James–Stein estimator is at least as good as James–Stein.** For `p ≥ 3`
and `X ~ N(θ, I_p)`, the loss `‖δ⁺(X) - θ‖²` is integrable and `E ‖δ⁺(X) - θ‖² ≤ E ‖δ(X) - θ‖²`
for every `θ` (Johnstone, *Gaussian
estimation: Sequence and wavelet models*, draft of 16 September 2019, equation (2.65) and
Exercise 2.12, where it is stated that `δ⁺` has "even better MSE" than `δ`). -/
theorem_wanted integral_jamesSteinPlus_risk_le {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) :
    Integrable (fun x => ∑ i, (jamesSteinPlus x i - θ i) ^ 2)
        (Measure.pi fun j => gaussianReal (θ j) 1) ∧
    ∫ x, ∑ i, (jamesSteinPlus x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) ≤
      ∫ x, ∑ i, (jamesStein x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1)

end ProbabilityTheory
