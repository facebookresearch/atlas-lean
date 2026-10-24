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
example : predictableQuadVar μ ℱ f 0 = 0 := by
  funext ω
  simp [predictableQuadVar]

/-- The predictable quadratic variation of a constant process is `0`: all
increments vanish. -/
example (c : ℝ) (n : ℕ) :
    predictableQuadVar μ ℱ (fun _ _ => c) n = 0 := by
  funext ω
  simp [predictableQuadVar]

/-- The predictable quadratic variation of the zero martingale is `0`. -/
example (n : ℕ) :
    predictableQuadVar μ ℱ (0 : ℕ → Ω → ℝ) n = 0 := by
  funext ω
  simp [predictableQuadVar]

/-- The main theorem restated with its exact public signature. -/
example (hmart : Martingale f ℱ μ) (hinteg : ∀ n, Integrable (fun ω => (f n ω) ^ 2) μ) :
    ∀ᵐ ω ∂μ, (∃ l, Tendsto (fun n => predictableQuadVar μ ℱ f n ω) atTop (𝓝 l)) →
      ∃ l, Tendsto (fun n => f n ω) atTop (𝓝 l) :=
  hmart.ae_tendsto_of_tendsto_predictableQuadVar hinteg

/-- On the zero martingale, the predictable quadratic variation converges
(to `0`), so the main theorem gives convergence of the martingale itself. -/
example :
    ∀ᵐ ω ∂μ, (∃ l, Tendsto
        (fun n => predictableQuadVar μ ℱ (0 : ℕ → Ω → ℝ) n ω) atTop (𝓝 l)) →
      ∃ l, Tendsto (fun n => (0 : ℕ → Ω → ℝ) n ω) atTop (𝓝 l) :=
  (martingale_zero ℝ ℱ μ).ae_tendsto_of_tendsto_predictableQuadVar
    (fun _ => by simp)

/-- On a constant martingale, the predictable quadratic variation is
identically `0`, hence converges, and the main theorem gives convergence
of the (constant) martingale to its constant value. -/
example (c : ℝ) :
    ∀ᵐ ω ∂μ, (∃ l, Tendsto
        (fun n => predictableQuadVar μ ℱ (fun _ _ => c) n ω) atTop (𝓝 l)) →
      ∃ l, Tendsto (fun n => ((fun _ _ => c : ℕ → Ω → ℝ) n ω)) atTop (𝓝 l) :=
  (martingale_const ℱ μ c).ae_tendsto_of_tendsto_predictableQuadVar
    (fun _ => integrable_const _)

end MathlibExtTest.Probability.SqMartingaleConvergence
