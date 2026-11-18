/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianHolder
public import MathlibExt.Probability.BrownianMotionExistence

/-!
# Tests for the Hölder continuity of Brownian paths

The Gaussian moment scaling at variance `0` and at `β = 2` (the variance), and non-vacuity of the
Hölder theorem at the boundary exponent `0` and at `α = 1/4` on the Brownian motion of
`exists_isBrownianReal`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathlibExtTest.Probability.BrownianHolder

/-- At variance `0` the scaled moment vanishes. -/
example (β : ℝ) (hβ : 0 < β) : ∫ x : ℝ, |x| ^ β ∂gaussianReal 0 0 = 0 := by
  rw [integral_abs_rpow_gaussianReal 0 hβ.le]
  simp [Real.zero_rpow (by positivity : β / 2 ≠ 0)]

/-- The second absolute moment of `N(0, v)` is `v` times that of `N(0, 1)`. -/
example (v : ℝ≥0) :
    ∫ x : ℝ, |x| ^ (2 : ℝ) ∂gaussianReal 0 v = v * ∫ x : ℝ, |x| ^ (2 : ℝ) ∂gaussianReal 0 1 := by
  rw [integral_abs_rpow_gaussianReal v (by norm_num)]
  norm_num

/-- Non-vacuity: some Brownian motion is a.s. `1/4`-Hölder on `[0, 1]` and bounded-oscillation
(Hölder of order `0`) on `[0, 10]`. -/
example : ∃ (μ : Measure (ℝ≥0 → ℝ)) (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
    IsProbabilityMeasure μ ∧ ∀ᵐ ω ∂μ,
      (∃ C : ℝ≥0, HolderOnWith C (1 / 4) (fun t ↦ W t ω) (Set.Icc 0 1)) ∧
      (∃ C : ℝ≥0, HolderOnWith C 0 (fun t ↦ W t ω) (Set.Icc 0 10)) := by
  obtain ⟨μ, W, hμ, -, -, hW⟩ := exists_isBrownianReal
  refine ⟨μ, W, hμ, ?_⟩
  filter_upwards [hW.ae_holderOnWith (α := 1 / 4) (by norm_num) 1,
    hW.ae_holderOnWith (α := 0) (by norm_num) 10] with ω h1 h2
  exact ⟨h1, h2⟩

end MathlibExtTest.Probability.BrownianHolder
