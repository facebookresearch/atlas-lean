/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GameTheory.MeanFieldGameSystem

/-!
# Wanted: uniqueness for the second-order mean field game system

The mean field game system of Lasry and Lions, in the form of Lions' Collège de France lectures
as written up by Cardaliaguet, on `ℝᵈ` (here `Fin d → ℝ`) and the time interval `[0, T]`:

* (i) `-∂ₜu - Δu + |Du|²/2 = F(x, m(t))` (Hamilton–Jacobi–Bellman, backward);
* (ii) `∂ₜm - Δm - div(m Du) = 0` (Fokker–Planck, forward);
* (iii) `m(0) = m₀`, `u(x, T) = G(x, m(T))`.

The dependence of `F` and `G` on the distribution is measured with the repository's
Wasserstein distance `W₁`.

The system and its classical solutions are defined in `MathlibExt.GameTheory.MeanFieldGameSystem`.

## References

* P. Cardaliaguet, *Notes on Mean Field Games (from P.-L. Lions' lectures at Collège de France)*,
  version of 27 September 2013, §3 (system (8), assumptions 1–3 before Theorem 3.1, conditions
  (17)–(18), Theorem 3.6).
* J.-M. Lasry and P.-L. Lions, *Mean field games*, Japan. J. Math. 2 (2007) 229–260.
-/

@[expose] public section

open _root_.MeasureTheory Set
open MathlibExt.Probability.FokkerPlanck MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
open MathlibExt.GameTheory.MeanFieldGameSystem

namespace MathlibExt.GameTheory.MeanFieldGameSystemWanted

variable {d : ℕ}

/-- **Uniqueness for the mean field game system** (Lasry–Lions; Cardaliaguet, *Notes on Mean
Field Games*, Theorem 3.6, uniqueness part). Assume the hypotheses of Cardaliaguet's
Theorem 3.1:
1. `F` and `G` are bounded by `C₀` on `ℝᵈ × P₁`;
2. they are `C₀`-Lipschitz: `|F(x₁, m₁) - F(x₂, m₂)| ≤ C₀ (|x₁ - x₂| + W₁(m₁, m₂))` on `P₁`,
   and likewise for `G`;
3. `m₀` is a probability density, Hölder continuous, with finite second moment;

and the Lasry–Lions monotonicity conditions (17) `∫ (F(x, m₁) - F(x, m₂)) d(m₁ - m₂)(x) > 0`
for `m₁ ≠ m₂` in `P₁` and (18) `∫ (G(x, m₁) - G(x, m₂)) d(m₁ - m₂)(x) ≥ 0`. Then two classical
solutions coincide on `ℝᵈ × [0, T]`. As an extra hypothesis, not in the source's statement, the
two solutions are assumed to have bounded `u` and bounded `Du` (the class in which Theorem 3.1
constructs them), so that the integrations by parts of the proof over `ℝᵈ` are justified; with
it the statement is weaker than Theorem 3.6. Norms on `ℝᵈ = Fin d → ℝ` are the sup norm, which
changes `C₀` by a dimensional factor only. The proof is the Lasry–Lions duality argument
around `MathlibExt.GameTheory.MeanFieldEquilibrium.lasryLions_identity`.

Satisfiability. For `d ≥ 1` the hypotheses hold together, for example, with
`F(x, m) = ∫ ρ(x - y) dm(y)` for a Gaussian `ρ`, `G = 0` and a Gaussian density `m₀`: `F` is
bounded, Lipschitz in `x`, and `W₁`-Lipschitz in `m` (Kantorovich–Rubinstein, `ρ` being
Lipschitz); (17) holds since `∫∫ ρ(x - y) d(m₁ - m₂)(x) d(m₁ - m₂)(y)` is, up to a positive
constant, `∫ ρ̂ |m̂₁ - m̂₂|² > 0` for `m₁ ≠ m₂` (`ρ̂ > 0`); (18) is trivial; and Cardaliaguet's
Theorem 3.1 gives a classical solution, with `|u| ≤ (1 + T) C₀` and `|Du| ≤ C₀` by its proof.
This example is argued, not formalised: the repository's only formal witness of the hypotheses
(`MathlibExtTest.GameTheory.MeanFieldGameSystem`) is in dimension `d = 0`, where (17) is vacuous
because `P₁` has a single element. -/
theorem_wanted isMFGClassicalSolution_unique
    (F G : (Fin d → ℝ) → ProbabilityMeasure (Fin d → ℝ) → ℝ) (m₀ : (Fin d → ℝ) → ℝ)
    {T : ℝ} (hT : 0 < T) (C₀ : ℝ)
    (hFb : ∀ x (μ : ProbabilityMeasure (Fin d → ℝ)),
      Integrable (fun y => ‖y‖) (μ : Measure (Fin d → ℝ)) → |F x μ| ≤ C₀)
    (hGb : ∀ x (μ : ProbabilityMeasure (Fin d → ℝ)),
      Integrable (fun y => ‖y‖) (μ : Measure (Fin d → ℝ)) → |G x μ| ≤ C₀)
    (hFL : ∀ x₁ x₂ (μ₁ μ₂ : ProbabilityMeasure (Fin d → ℝ)),
      Integrable (fun y => ‖y‖) (μ₁ : Measure (Fin d → ℝ)) →
      Integrable (fun y => ‖y‖) (μ₂ : Measure (Fin d → ℝ)) →
      |F x₁ μ₁ - F x₂ μ₂| ≤ C₀ * (‖x₁ - x₂‖ + (wasserstein 1 μ₁ μ₂).toReal))
    (hGL : ∀ x₁ x₂ (μ₁ μ₂ : ProbabilityMeasure (Fin d → ℝ)),
      Integrable (fun y => ‖y‖) (μ₁ : Measure (Fin d → ℝ)) →
      Integrable (fun y => ‖y‖) (μ₂ : Measure (Fin d → ℝ)) →
      |G x₁ μ₁ - G x₂ μ₂| ≤ C₀ * (‖x₁ - x₂‖ + (wasserstein 1 μ₁ μ₂).toReal))
    (hm₀ : (∀ x, 0 ≤ m₀ x) ∧ ∫ x, m₀ x = 1 ∧
      (∃ α ∈ Ioc (0 : ℝ) 1, ∃ C, ∀ x y, |m₀ x - m₀ y| ≤ C * ‖x - y‖ ^ α) ∧
      Integrable (fun x => ‖x‖ ^ 2 * m₀ x))
    (hFmono : ∀ μ₁ μ₂ : ProbabilityMeasure (Fin d → ℝ),
      Integrable (fun y => ‖y‖) (μ₁ : Measure (Fin d → ℝ)) →
      Integrable (fun y => ‖y‖) (μ₂ : Measure (Fin d → ℝ)) → μ₁ ≠ μ₂ →
      0 < (∫ x, (F x μ₁ - F x μ₂) ∂(μ₁ : Measure (Fin d → ℝ))) -
        ∫ x, (F x μ₁ - F x μ₂) ∂(μ₂ : Measure (Fin d → ℝ)))
    (hGmono : ∀ μ₁ μ₂ : ProbabilityMeasure (Fin d → ℝ),
      Integrable (fun y => ‖y‖) (μ₁ : Measure (Fin d → ℝ)) →
      Integrable (fun y => ‖y‖) (μ₂ : Measure (Fin d → ℝ)) →
      0 ≤ (∫ x, (G x μ₁ - G x μ₂) ∂(μ₁ : Measure (Fin d → ℝ))) -
        ∫ x, (G x μ₁ - G x μ₂) ∂(μ₂ : Measure (Fin d → ℝ)))
    {u₁ m₁ u₂ m₂ : (Fin d → ℝ) → ℝ → ℝ} {μ₁ μ₂ : ℝ → ProbabilityMeasure (Fin d → ℝ)}
    (h₁ : IsMFGClassicalSolution F G m₀ T u₁ m₁ μ₁)
    (h₂ : IsMFGClassicalSolution F G m₀ T u₂ m₂ μ₂)
    (hbd₁ : ∃ B, ∀ x, (∀ t ∈ Icc 0 T, |u₁ x t| ≤ B) ∧
      ∀ t ∈ Ioo 0 T, ‖grad (fun y => u₁ y t) x‖ ≤ B)
    (hbd₂ : ∃ B, ∀ x, (∀ t ∈ Icc 0 T, |u₂ x t| ≤ B) ∧
      ∀ t ∈ Ioo 0 T, ‖grad (fun y => u₂ y t) x‖ ≤ B) :
    ∀ x, ∀ t ∈ Icc 0 T, u₁ x t = u₂ x t ∧ m₁ x t = m₂ x t

end MathlibExt.GameTheory.MeanFieldGameSystemWanted
