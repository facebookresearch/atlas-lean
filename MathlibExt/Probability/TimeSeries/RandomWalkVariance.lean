/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic

/-!
# Variance of a random walk

The partial sum of independent square-integrable innovations with a common
variance has variance growing linearly in the horizon:
`Var (S_h) = h * Var (ε_0)`. This is the unnormalized companion of the
sample-mean variance `Var (X̄_n) = σ² / n`
(`MathlibExt.Probability.variance_sample_mean_of_iid`); the proof is
`ProbabilityTheory.IndepFun.variance_sum` applied to the finite sum.

Only a common variance is assumed, not full identical distribution: the
common-variance hypothesis is exactly what the proof uses.

## Main results

- `randomWalk_variance`: `Var (∑_{k<h} ε_k) = h * Var (ε_0)`.
- `randomWalk_variance_four`: the numeric instance `h = 4`, `Var (ε_0) = 3`,
  giving `12`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.TimeSeries.RandomWalkVariance

/-- The variance of a random walk (partial sum of independent square-integrable
innovations with a common variance) grows linearly in the horizon:
`Var (S_h) = h * Var (ε_0)`. -/
theorem randomWalk_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℕ → Ω → ℝ) (hLp : ∀ i, MemLp (ε i) 2 μ) (hIndep : iIndepFun ε μ)
    (hVar : ∀ i, variance (ε i) μ = variance (ε 0) μ) (h : ℕ) :
    variance (fun ω => ∑ k ∈ Finset.range h, ε k ω) μ =
      (h : ℝ) * variance (ε 0) μ := by
  have hfun : (fun ω => ∑ k ∈ Finset.range h, ε k ω)
      = ∑ k ∈ Finset.range h, ε k := by
    funext ω
    exact (Finset.sum_apply ω _ _).symm
  have hPair : ((Finset.range h : Set ℕ)).Pairwise fun i j => ε i ⟂ᵢ[μ] ε j := by
    intro x _ y _ hxy
    exact hIndep.indepFun hxy
  have hsum : ∀ i ∈ Finset.range h, variance (ε i) μ = variance (ε 0) μ :=
    fun i _ => hVar i
  rw [hfun, IndepFun.variance_sum (fun i _ => hLp i) hPair,
    Finset.sum_congr rfl hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Numeric instance: horizon `4`, single-innovation variance `3`, gives `12`. -/
theorem randomWalk_variance_four {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℕ → Ω → ℝ) (hLp : ∀ i, MemLp (ε i) 2 μ) (hIndep : iIndepFun ε μ)
    (hVar : ∀ i, variance (ε i) μ = variance (ε 0) μ)
    (hVar0 : variance (ε 0) μ = 3) :
    variance (fun ω => ∑ k ∈ Finset.range 4, ε k ω) μ = 12 := by
  rw [randomWalk_variance ε hLp hIndep hVar 4, hVar0]
  norm_num

end MathlibExt.Probability.TimeSeries.RandomWalkVariance
