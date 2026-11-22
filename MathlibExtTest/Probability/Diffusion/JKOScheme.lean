/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Diffusion.JKOScheme

@[expose] public section

open MeasureTheory MathlibExt.Probability.Diffusion.JKOScheme

namespace MathlibExtTest.Probability.Diffusion.JKOScheme

variable {n : ℕ}

/-- On `ℝⁿ` with the Euclidean distance, the objective of the competitor `ρ = ρ₀` is `h F(ρ₀)`. -/
example (Ψ : EuclideanSpace ℝ (Fin n) → ℝ) (β h : ℝ)
    (ρ₀ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) :
    jkoObjective Ψ β h ρ₀ ρ₀ = (h : EReal) * freeEnergy Ψ β (ρ₀ : Measure _) :=
  jkoObjective_self Ψ β h ρ₀

/-- Along a JKO sequence started at an admissible density, the first step satisfies the
comparison inequality `½ W₂² + h F(ρ₁) ≤ h F(ρ₀)`. -/
example (Ψ : EuclideanSpace ℝ (Fin n) → ℝ) (β h : ℝ)
    (ρ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hρ : IsJKOSequence Ψ β h ρ)
    (h0 : IsAdmissible (ρ 0)) :
    jkoObjective Ψ β h (ρ 0) (ρ 1) ≤ (h : EReal) * freeEnergy Ψ β (ρ 0 : Measure _) :=
  (hρ 0).jkoObjective_le h0

/-- Every later state of a JKO sequence is admissible. -/
example (Ψ : EuclideanSpace ℝ (Fin n) → ℝ) (β h : ℝ)
    (ρ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hρ : IsJKOSequence Ψ β h ρ)
    (k : ℕ) : IsAdmissible (ρ (k + 1)) :=
  (hρ k).1

end MathlibExtTest.Probability.Diffusion.JKOScheme
