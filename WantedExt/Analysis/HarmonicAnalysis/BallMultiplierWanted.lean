/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Fefferman's ball multiplier theorem (statement)

The ball multiplier `T f = (𝟙_B f̂)ˇ`, with `B` the unit ball of `ℝⁿ`, is written with Mathlib's
Fourier transform `𝓕 f ξ = ∫ e^{-2πi⟪x, ξ⟫} f x dx` and its inverse `𝓕⁻`, applied to Schwartz
functions; the radius of the ball is immaterial since the multiplier problem is invariant
under dilations.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace MathlibExt.Analysis.HarmonicAnalysis.BallMultiplierWanted

/-- **Fefferman's ball multiplier theorem.** For `n ≥ 2` and `1 ≤ p < ∞` with `p ≠ 2`, the
Fourier multiplier of the unit ball of `ℝⁿ`, `T f = 𝓕⁻ (𝟙_B · 𝓕 f)`, is unbounded on `L^p`:
there is no finite `C` with `‖T f‖_p ≤ C ‖f‖_p` for all Schwartz functions `f`
(C. Fefferman, *The multiplier problem for the ball*, Ann. of Math. 94 (1971), 330–336,
Theorem 1, which states that `T` is bounded only on `L²` when `n > 1`). -/
public theorem_wanted not_exists_eLpNorm_ballMultiplier_le {n : ℕ} (_hn : 2 ≤ n)
    {p : ℝ≥0∞} (_hp1 : 1 ≤ p) (_hp : p ≠ ∞) (_hp2 : p ≠ 2) :
    ¬ ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      eLpNorm (𝓕⁻ ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1).indicator
          (𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ)))) p volume ≤
        C * eLpNorm (f : EuclideanSpace ℝ (Fin n) → ℂ) p volume

end MathlibExt.Analysis.HarmonicAnalysis.BallMultiplierWanted
