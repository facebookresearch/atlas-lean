/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SDE.YamadaWatanabeApprox

/-!
# Tests for Yamada–Watanabe approximating functions

The importing example restates the approximation theorem with its hypotheses.
-/

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory.SDE

namespace MathlibExtTest.Probability.SDE.YamadaWatanabeApprox

example {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ici 0)) (_hmono : StrictMonoOn h (Set.Ici 0))
    (_h0 : h 0 = 0) (hpos : ∀ u, 0 < u → 0 < h u)
    (hosgood : ∀ ε, 0 < ε → ∫⁻ u in Set.Ioc 0 ε, ENNReal.ofReal ((h u ^ 2)⁻¹) = ⊤) :
    ∃ (a : ℕ → ℝ) (φ : ℕ → ℝ → ℝ),
      a 0 = 1 ∧ StrictAnti a ∧ (∀ n, 0 < a n) ∧ Tendsto a atTop (𝓝 0) ∧
      (∀ n, ∫ u in a (n + 1)..a n, (h u ^ 2)⁻¹ = n + 1) ∧
      (∀ n, ContDiff ℝ 2 (φ n)) ∧ (∀ n x, φ n (-x) = φ n x) ∧
      (∀ x, Tendsto (fun n => φ n x) atTop (𝓝 |x|)) ∧
      (∀ n x, |deriv (φ n) x| ≤ 1) ∧
      (∀ n x, 0 ≤ iteratedDeriv 2 (φ n) x ∧
        iteratedDeriv 2 (φ n) x ≤ 2 / ((n + 1) * h |x| ^ 2)) ∧
      (∀ n x, iteratedDeriv 2 (φ n) x ≠ 0 → a (n + 1) < |x| ∧ |x| < a n) :=
  exists_yamadaWatanabe_approx hcont _hmono _h0 hpos hosgood

#print axioms ProbabilityTheory.SDE.exists_yamadaWatanabe_approx

end MathlibExtTest.Probability.SDE.YamadaWatanabeApprox
