/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic
public import MathlibExt.Probability.RandomWalkTailMeasurability

/-!
# Variance of a random walk

The random walk `S_h = randomWalkPartialSum ε h = ∑_{k<h} ε_k` of pairwise independent
square-integrable innovations with a common variance has variance growing linearly in the
horizon: `Var (S_h) = h * Var (ε_0)`. This is the unnormalized companion of the
sample-mean variance `Var (X̄_n) = σ² / n`
(`MathlibExt.Probability.variance_sample_mean_of_iid`); the proof is
`ProbabilityTheory.IndepFun.variance_sum` applied to the finite sum. The partial sum is the
canonical `MathlibExt.Probability.RandomWalkTailMeasurability.randomWalkPartialSum` consumed by
the random-walk limsup and dichotomy results.

Only pairwise independence and a common variance are assumed, not mutual independence or
identical distribution: these are exactly what the proof uses.

## Main results

- `randomWalk_variance`: `Var (S_h) = h * Var (ε_0)` for pairwise independent innovations.
- `randomWalk_variance_of_iIndepFun`: the same for mutually independent innovations.
- `randomWalk_variance_four`: the numeric instance `h = 4`, `Var (ε_0) = 3`,
  giving `12`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.RandomWalkTailMeasurability (randomWalkPartialSum)

namespace MathlibExt.Probability.TimeSeries.RandomWalkVariance

/-- The variance of a random walk (partial sum of pairwise independent square-integrable
innovations with a common variance) grows linearly in the horizon:
`Var (S_h) = h * Var (ε_0)`. -/
theorem randomWalk_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℕ → Ω → ℝ) (hLp : ∀ i, MemLp (ε i) 2 μ)
    (hIndep : Pairwise fun i j => ε i ⟂ᵢ[μ] ε j)
    (hVar : ∀ i, variance (ε i) μ = variance (ε 0) μ) (h : ℕ) :
    variance (randomWalkPartialSum ε h) μ = (h : ℝ) * variance (ε 0) μ := by
  have hfun : randomWalkPartialSum ε h = ∑ k ∈ Finset.range h, ε k := by
    funext ω
    exact (Finset.sum_apply ω _ _).symm
  have hPair : ((Finset.range h : Set ℕ)).Pairwise fun i j => ε i ⟂ᵢ[μ] ε j :=
    fun _ _ _ _ hxy => hIndep hxy
  have hsum : ∀ i ∈ Finset.range h, variance (ε i) μ = variance (ε 0) μ :=
    fun i _ => hVar i
  rw [hfun, IndepFun.variance_sum (fun i _ => hLp i) hPair,
    Finset.sum_congr rfl hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `randomWalk_variance` for mutually independent innovations. -/
theorem randomWalk_variance_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℕ → Ω → ℝ) (hLp : ∀ i, MemLp (ε i) 2 μ) (hIndep : iIndepFun ε μ)
    (hVar : ∀ i, variance (ε i) μ = variance (ε 0) μ) (h : ℕ) :
    variance (randomWalkPartialSum ε h) μ = (h : ℝ) * variance (ε 0) μ :=
  randomWalk_variance ε hLp (fun _ _ hij => hIndep.indepFun hij) hVar h

/-- Numeric instance: horizon `4`, single-innovation variance `3`, gives `12`. -/
theorem randomWalk_variance_four {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℕ → Ω → ℝ) (hLp : ∀ i, MemLp (ε i) 2 μ)
    (hIndep : Pairwise fun i j => ε i ⟂ᵢ[μ] ε j)
    (hVar : ∀ i, variance (ε i) μ = variance (ε 0) μ)
    (hVar0 : variance (ε 0) μ = 3) :
    variance (randomWalkPartialSum ε 4) μ = 12 := by
  rw [randomWalk_variance ε hLp hIndep hVar 4, hVar0]
  norm_num

end MathlibExt.Probability.TimeSeries.RandomWalkVariance
