/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SqMartingaleConvergence

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace MathlibExtTest.Probability.SqMartingaleConvergence

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- The predictable quadratic variation at time `0` is `0`: the sum over
`range 0` is empty. -/
example : predictableQuadraticVariation μ ℱ f 0 = 0 := by
  funext ω
  simp [predictableQuadraticVariation]

/-- The predictable quadratic variation of a constant process is `0`: all
increments vanish. -/
example (c : ℝ) (n : ℕ) :
    predictableQuadraticVariation μ ℱ (fun _ _ => c) n = 0 := by
  funext ω
  simp [predictableQuadraticVariation]

/-- The predictable quadratic variation of the zero martingale is `0`. -/
example (n : ℕ) :
    predictableQuadraticVariation μ ℱ (0 : ℕ → Ω → ℝ) n = 0 := by
  funext ω
  simp [predictableQuadraticVariation]

/-- The main theorem restated with its exact public signature. -/
example (hmart : Martingale f ℱ μ) (hinteg : ∀ n, Integrable (fun ω => (f n ω) ^ 2) μ) :
    ∀ᵐ ω ∂μ, (∃ l, Tendsto (fun n => predictableQuadraticVariation μ ℱ f n ω) atTop (𝓝 l)) →
      ∃ l, Tendsto (fun n => f n ω) atTop (𝓝 l) :=
  hmart.ae_tendsto_of_tendsto_predictableQuadVar hinteg

/-- On the zero martingale, the predictable quadratic variation converges
(to `0`), so the main theorem gives convergence of the martingale itself. -/
example :
    ∀ᵐ ω ∂μ, (∃ l, Tendsto
        (fun n => predictableQuadraticVariation μ ℱ (0 : ℕ → Ω → ℝ) n ω) atTop (𝓝 l)) →
      ∃ l, Tendsto (fun n => (0 : ℕ → Ω → ℝ) n ω) atTop (𝓝 l) :=
  (martingale_zero ℝ ℱ μ).ae_tendsto_of_tendsto_predictableQuadVar
    (fun _ => by simp)

/-- On a constant martingale, the predictable quadratic variation is
identically `0`, hence converges, and the main theorem gives convergence
of the (constant) martingale to its constant value. -/
example (c : ℝ) :
    ∀ᵐ ω ∂μ, (∃ l, Tendsto
        (fun n => predictableQuadraticVariation μ ℱ (fun _ _ => c) n ω) atTop (𝓝 l)) →
      ∃ l, Tendsto (fun n => ((fun _ _ => c : ℕ → Ω → ℝ) n ω)) atTop (𝓝 l) :=
  (martingale_const ℱ μ c).ae_tendsto_of_tendsto_predictableQuadVar
    (fun _ => integrable_const _)

/-- The original source formula, with the sum and conditional square explicit. -/
example (n : ℕ) (ω : Ω) :
    predictableQuadraticVariation μ ℱ f n ω = (Finset.range n).sum (fun k =>
      (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω) := rfl

/-- This definition-level fixture has increments one and three, giving variation ten. -/
example (ω : Ω) :
    predictableQuadraticVariation μ ℱ (fun n _ => (n : ℝ) ^ 2) 2 ω = 10 := by
  norm_num [predictableQuadraticVariation, Finset.sum_range_succ,
    condExp_const (μ := μ) (ℱ.le 0), condExp_const (μ := μ) (ℱ.le 1)]

end MathlibExtTest.Probability.SqMartingaleConvergence
