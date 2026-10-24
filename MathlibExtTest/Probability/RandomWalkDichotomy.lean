/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RandomWalkDichotomy

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open MathlibExt.Probability.RandomWalkDichotomy

namespace MathlibExtTest.Probability.RandomWalkDichotomy

/-- The dichotomy has the expected public signature. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ConvergesFinite μ X ∨ DriftsToTop μ X ∨ DriftsToBot μ X ∨ Oscillates μ X :=
  random_walk_dichotomy μ X hindep hident

/-- The constant-`1` walk drifts to `+∞`: its partial sums are
`Sₙ = n`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    DriftsToTop μ (fun _ _ => (1 : ℝ)) := by
  apply Filter.Eventually.of_forall
  intro ω
  have hsum : ∀ n, randomWalkPartialSum (fun _ _ => (1 : ℝ)) n ω = (n : ℝ) := by
    intro n
    simp [randomWalkPartialSum]
  simpa only [hsum] using tendsto_natCast_atTop_atTop

/-- The constant-`-1` walk drifts to `-∞`: its partial sums are
`Sₙ = -n`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    DriftsToBot μ (fun _ _ => (-1 : ℝ)) := by
  apply Filter.Eventually.of_forall
  intro ω
  have hsum : ∀ n, randomWalkPartialSum (fun _ _ => (-1 : ℝ)) n ω = -(n : ℝ) := by
    intro n
    simp [randomWalkPartialSum]
  simpa only [Function.comp_def, hsum] using
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop

/-- The zero walk converges finitely: its partial sums are identically `0`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ConvergesFinite μ (fun _ _ => (0 : ℝ)) := by
  apply Filter.Eventually.of_forall
  intro ω
  refine ⟨0, ?_⟩
  have hsum : ∀ n, randomWalkPartialSum (fun _ _ => (0 : ℝ)) n ω = (0 : ℝ) := by
    intro n
    simp [randomWalkPartialSum]
  simpa only [hsum] using tendsto_const_nhds

/-- Drifting to `+∞` and to `-∞` are mutually exclusive: at a point where
both hold, the partial sums would eventually be `≥ 1` and `≤ 0` at once. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hTop : DriftsToTop μ X) (hBot : DriftsToBot μ X) :
    False := by
  obtain ⟨ω, h1, h2⟩ := (hTop.and hBot).exists
  have e1 : ∀ᶠ n in Filter.atTop, (1 : ℝ) ≤ randomWalkPartialSum X n ω :=
    h1.eventually (eventually_ge_atTop (1 : ℝ))
  have e2 : ∀ᶠ n in Filter.atTop, randomWalkPartialSum X n ω ≤ (0 : ℝ) :=
    h2.eventually (eventually_le_atBot (0 : ℝ))
  obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
  linarith

end MathlibExtTest.Probability.RandomWalkDichotomy
