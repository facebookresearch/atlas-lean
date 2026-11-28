/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Distributions.Dirichlet
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.Data.Set.Card

/-!
# Pólya–Aeppli law of ancestor numbers in a Feller diffusion

The two-time branching family measure records both whole-population and sample ancestry.
-/

@[expose] public section

namespace WantedExt.Biology.PolyaAeppliFellerWanted

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

/-- The Feller branching Laplace exponent, including its critical and time-zero limits.
Its semigroup has generator `Lf(x) = x * f''(x) / 2 + α * x * f'(x)`. -/
noncomputable def fellerLaplaceExponent (α r q : ℝ) : ℝ :=
  q * Real.exp (α * r) /
    (1 + q * (if α = 0 then r / 2 else (Real.exp (α * r) - 1) / (2 * α)))

/-- The rate of surviving families per unit ancestral mass. -/
noncomputable def fellerMu (α t : ℝ) : ℝ :=
  if α = 0 then 2 / t else 2 * α * Real.exp (α * t) / (Real.exp (α * t) - 1)

/-- The Pólya–Aeppli geometric parameter, with its continuous critical limit. -/
noncomputable def fellerP (α s t : ℝ) : ℝ :=
  if α = 0 then 1 - s / t
  else (Real.exp (α * s) - Real.exp (α * t)) / (1 - Real.exp (α * t))

/-- The two-time genealogical law of the Feller diffusion started at mass `x₀`.
`X` is the mass at time `r`; `F` assigns to each ancestral mass label its descendants' mass
at time `r + s`. The first Laplace transform specifies the Feller transition from `x₀`.
The conditional Laplace functional specifies independent branching of ancestral mass,
with Lebesgue labels in `(0, X]`. Thus atoms of `F` are surviving ancestral families. -/
def IsFellerFamilyLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ≥0) (F : Ω → FiniteMeasure ℝ) (α x₀ r s : ℝ) : Prop :=
  Measurable X ∧ Measurable F ∧
  (∀ q : ℝ≥0, (∫ ω, Real.exp (-(q : ℝ) * X ω) ∂P) =
    Real.exp (-x₀ * fellerLaplaceExponent α r q)) ∧
  (∀ (f : ℝ → ℝ≥0), Measurable f → (∃ C : ℝ≥0, ∀ a, f a ≤ C) →
    ∀ B : Set ℝ≥0, MeasurableSet B →
      (∫ ω in X ⁻¹' B, Real.exp (-(∫ a, (f a : ℝ) ∂(F ω : Measure ℝ))) ∂P) =
      ∫ ω in X ⁻¹' B, Real.exp (-(∫ a in Ioc 0 (X ω : ℝ),
        fellerLaplaceExponent α s (f a))) ∂P)

/-- The labels of families with positive descendant mass. -/
def ancestorLabels (F : FiniteMeasure ℝ) : Set ℝ :=
  {a | 0 < (F : Measure ℝ) {a}}

/-- The number of ancestors of the whole population, including zero on extinction. -/
noncomputable def wholeAncestorCount (F : FiniteMeasure ℝ) : ℕ :=
  (ancestorLabels F).ncard

/-- The geometric compound Poisson law: a Poisson mixture of sums of independent shifted
geometric variables. `symm p` is success probability `1 - p`; the empty sum is zero. -/
noncomputable def polyaAeppliMeasure (ν : ℝ≥0) (p : unitInterval) : Measure ℕ :=
  Measure.sum fun l : ℕ => (poissonMeasure ν {l}) •
    Measure.map (fun m : Fin l → ℕ => ∑ i, (m i + 1))
      (Measure.pi fun _ : Fin l => geometricMeasure (unitInterval.symm p))

/-- Probability of `j` distinct ancestral labels in `n` independent draws from normalized
family mass, averaged over populations conditional on survival. -/
noncomputable def sampleAncestorProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → FiniteMeasure ℝ) (n j : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, (Measure.pi fun _ : Fin n =>
    ((F ω : Measure ℝ) univ)⁻¹ • (F ω : Measure ℝ))
      {a : Fin n → ℝ | (range a).ncard = j} ∂cond P {ω | 0 < (F ω).mass}

/-- **Pólya–Aeppli law of Feller ancestors.** For every real drift `α`, initial mass `x₀ > 0`,
and `0 < s ≤ t`, the whole-population ancestor count at time `t - s` is almost surely finite
and has the geometric compound Poisson law with parameters `ν = x₀ μ(t; α)` and
`p = (exp(α s) - exp(α t)) / (1 - exp(α t))`. At `α = 0` the parameters are `2 x₀ / t`
and `1 - s / t`. At `s = t` the founders count is Poisson with rate `x₀ μ(t; α)`.
For a positive sample size `n` and `1 ≤ j ≤ n`, the sample ancestor probability is
`n! * choose(n - 1, j - 1)` times the sum over all `k ≥ j` of
`choose(k, j) / k.ascFactorial n * P(A∞ = k | A∞ > 0)`.

The sampling argument uses Dirichlet–multinomial conjugacy as formalized by
`ProbabilityTheory.withDensity_prod_pow_dirichletMeasure`.

Source: Conrad J. Burden and Robert C. Griffiths, "Coalescence and sampling distributions for
Feller diffusions", Theoretical Population Biology 155 (2024), 67–76,
https://doi.org/10.1016/j.tpb.2023.12.001. Numbering follows arXiv:2210.12894v2,
https://arxiv.org/abs/2210.12894v2, Definition 1, Theorem 1, Lemma 1 and Theorem 2. -/
theorem_wanted feller_ancestor_laws {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ≥0) (F : Ω → FiniteMeasure ℝ)
    (α x₀ s t : ℝ) (hx₀ : 0 < x₀) (hs : 0 < s) (hst : s ≤ t)
    (hfeller : IsFellerFamilyLaw P X F α x₀ (t - s) s) :
    (∀ᵐ ω ∂P, (ancestorLabels (F ω)).Finite) ∧
    (∃ p : unitInterval, (p : ℝ) = fellerP α s t ∧
      HasLaw (fun ω => wholeAncestorCount (F ω))
        (polyaAeppliMeasure (Real.toNNReal (x₀ * fellerMu α t)) p) P) ∧
    (s = t → HasLaw (fun ω => wholeAncestorCount (F ω))
      (poissonMeasure (Real.toNNReal (x₀ * fellerMu α t))) P) ∧
    (∀ n : ℕ, 0 < n → ∀ j : ℕ, 1 ≤ j → j ≤ n →
      sampleAncestorProb P F n j =
        (n.factorial : ℝ≥0∞) * ((n - 1).choose (j - 1) : ℝ≥0∞) *
          ∑' k : ℕ, if j ≤ k then
            (k.choose j : ℝ≥0∞) / (k.ascFactorial n : ℝ≥0∞) *
              (cond P {ω | 0 < wholeAncestorCount (F ω)})
                {ω | wholeAncestorCount (F ω) = k}
          else 0)

end WantedExt.Biology.PolyaAeppliFellerWanted
