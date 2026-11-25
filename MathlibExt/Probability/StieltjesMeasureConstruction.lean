/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Construction of measures on ℝ from Stieltjes functions

For every right-continuous, non-decreasing function `f : ℝ → ℝ` tending to
`0` at `-∞` and to `1` at `∞`, there is a unique Borel probability measure
on `ℝ` assigning each half-open interval `(a, b]` the mass `f b - f a`.

## Source

`v1/Atlas/TheoryOfProbability/code/MeasuresOnR.lean`
(`stieltjes_measure_construction`), for the book target
"Theorem (construction of measures on R)" (Lecture 2, section
"How do we produce measures on R?") in
`v1/Atlas/TheoryOfProbability/targets.yaml`. The `∃!` form
`exists_unique_probabilityMeasure_of_stieltjes` is the same statement
repackaged as unique existence; it is proved from the ported conjunction.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MathlibExt.Probability.StieltjesMeasureConstruction

/-- **Construction of measures on ℝ.** Let $f : \mathbb{R} \to \mathbb{R}$ be a Stieltjes
function, that is, non-decreasing and right-continuous, with $f(x) \to 0$ as $x \to -\infty$
and $f(x) \to 1$ as $x \to \infty$, and let $\mu_f$ be its Stieltjes measure on $\mathbb{R}$.
Then $\mu_f$ is a probability measure, $\mu_f((a, b]) = f(b) - f(a)$ for all real $a \le b$,
and every finite measure $\nu$ on $\mathbb{R}$ with $\nu((a, b]) = f(b) - f(a)$ for all real
$a \le b$ equals $\mu_f$. -/
theorem stieltjes_measure_construction (f : StieltjesFunction ℝ)
    (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    IsProbabilityMeasure f.measure ∧
    (∀ a b : ℝ, a ≤ b → f.measure (Ioc a b) = ENNReal.ofReal (f b - f a)) ∧
    (∀ ν : Measure ℝ, [IsFiniteMeasure ν] →
      (∀ a b : ℝ, a ≤ b → ν (Ioc a b) = ENNReal.ofReal (f b - f a)) →
      ν = f.measure) := by
  have hprob : IsProbabilityMeasure f.measure := f.isProbabilityMeasure hf_bot hf_top
  refine ⟨hprob, fun a b _ => f.measure_Ioc a b, ?_⟩
  intro ν _ hν
  exact MeasureTheory.Measure.ext_of_Ioc ν f.measure
    (fun {a b} hab => by rw [hν a b hab.le, f.measure_Ioc])

/-- **Construction of measures on ℝ, as unique existence.** Let
$f : \mathbb{R} \to \mathbb{R}$ be a Stieltjes function, that is, non-decreasing and
right-continuous, with $f(x) \to 0$ as $x \to -\infty$ and $f(x) \to 1$ as $x \to \infty$.
Then there is exactly one measure $\mu$ on $\mathbb{R}$ that is a probability measure and
satisfies $\mu((a, b]) = f(b) - f(a)$ for all real $a \le b$. -/
theorem exists_unique_probabilityMeasure_of_stieltjes (f : StieltjesFunction ℝ)
    (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    ∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ a b : ℝ, a ≤ b → μ (Ioc a b) = ENNReal.ofReal (f b - f a) := by
  obtain ⟨hprob, hIoc, huniq⟩ := stieltjes_measure_construction f hf_bot hf_top
  refine ⟨f.measure, ⟨hprob, hIoc⟩, ?_⟩
  intro ν ⟨hνprob, hνIoc⟩
  have _ := hνprob
  exact huniq ν hνIoc

end MathlibExt.Probability.StieltjesMeasureConstruction
