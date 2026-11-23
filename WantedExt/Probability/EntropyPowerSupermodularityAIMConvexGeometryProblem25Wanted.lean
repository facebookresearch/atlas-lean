/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Entropy powers of sums of independent real variables are not supermodular (AIM, Madiman)

AIM workshop on algorithmic convex geometry, Problem 6 (M. Madiman): for independent real random
variables `X₁, X₂, X₃` with densities, is
`e^{2H(X₁+X₂+X₃)} + e^{2H(X₂)} ≥ e^{2H(X₁+X₂)} + e^{2H(X₂+X₃)}`? Madiman and Ghassemi showed that it
is not, already for log-concave variables.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Density
public import MathlibExt.Probability.Geometry.IsotropicConstant

@[expose] public section

namespace MathlibExt.Probability.EntropyPowerSupermodularityAIMConvexGeometryProblem25Wanted

/-!
Source: Problems from the AIM Workshop on Algorithmic Convex Geometry (compiled by N. Goyal),
Problem 6 (M. Madiman), https://aimath.org/WWN/convexgeometry/convexgeometry.pdf. UnsolvedMath
record UM-20001293 (`AIM-CONVEX_GEOMETRY-0025`), dataset ulamai/UnsolvedMath v1.8.0.

Real random variables take values in `ℝ¹ = EuclideanSpace ℝ (Fin 1)` so that `MathlibExt`'s
differential entropy `H(f) = -∫ f log f` of a Lebesgue density applies; `H(X)` is the entropy of the
density (`pdf`) of `X`. The claim is stated for independent `X₁, X₂, X₃` with densities whose sums
appearing in the inequality have finite entropy (integrable `f log f`), so that every `e^{2H}` is a
genuine entropy power; a refutation must then exhibit such variables. Gaussians give equality (the
list's remark).
-/

open MeasureTheory ProbabilityTheory

/-- The real random variable `X` (valued in `ℝ¹ = EuclideanSpace ℝ (Fin 1)`) has a density with
respect to Lebesgue measure whose entropy integrand `f log f` is integrable. -/
def HasFiniteEntropyDensity {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin 1)) : Prop :=
  HasPDF X P volume ∧
    Integrable (fun x => (pdf X P volume x).toReal * Real.log (pdf X P volume x).toReal) volume

/-- The differential entropy `H(X) = -∫ f log f` of the density `f` of `X`. -/
noncomputable def entropy {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin 1)) : ℝ :=
  MathlibExt.Probability.IsotropicConstant.differentialEntropy fun x => (pdf X P volume x).toReal

/-- Madiman's question (AIM algorithmic convex geometry list, Problem 6): for independent real
random variables `X₁, X₂, X₃` with densities (and finite entropies),
`e^{2H(X₁+X₂+X₃)} + e^{2H(X₂)} ≥ e^{2H(X₁+X₂)} + e^{2H(X₂+X₃)}`. -/
def entropyPowerSupermodular : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (X₁ X₂ X₃ : Ω → EuclideanSpace ℝ (Fin 1)),
    iIndepFun ![X₁, X₂, X₃] P → HasPDF X₁ P volume → HasPDF X₂ P volume → HasPDF X₃ P volume →
    HasFiniteEntropyDensity P X₂ → HasFiniteEntropyDensity P (X₁ + X₂) →
    HasFiniteEntropyDensity P (X₂ + X₃) → HasFiniteEntropyDensity P (X₁ + X₂ + X₃) →
      Real.exp (2 * entropy P (X₁ + X₂)) + Real.exp (2 * entropy P (X₂ + X₃)) ≤
        Real.exp (2 * entropy P (X₁ + X₂ + X₃)) + Real.exp (2 * entropy P X₂)

/--
Resolved false: there are independent real random variables with (log-concave) densities and
`e^{2H(X₁+X₂+X₃)} + e^{2H(X₂)} < e^{2H(X₁+X₂)} + e^{2H(X₂+X₃)}`. Madiman-Ghassemi, Proposition 4:
'There exist independent ℝ-valued random variables X, Y, Z, each with log-concave distributions,
such that e^{2h(X+Y+Z)} + e^{2h(Z)} < e^{2h(X+Z)} + e^{2h(Y+Z)}. In particular, the answer to
Question 1 is negative, already in dimension 1' (take X₁ = X, X₂ = Z, X₃ = Y); log-concave densities
and their convolutions have finite entropy. Source: Problems from the AIM Workshop on Algorithmic
Convex Geometry (compiled by N. Goyal), Problem 6 (M. Madiman),
https://aimath.org/WWN/convexgeometry/convexgeometry.pdf; resolution: M. Madiman and F. Ghassemi,
Combinatorial entropy power inequalities: a preliminary study of the Stam region, IEEE Trans.
Inform. Theory 65 (2019), no. 3, 1375-1386, arXiv:1704.01177, §IV (Discussion of a question),
Question 1 and Proposition 4, https://doi.org/10.1109/TIT.2018.2854545.
-/
public theorem_wanted entropyPowerSupermodular_refuted : ¬ entropyPowerSupermodular

end MathlibExt.Probability.EntropyPowerSupermodularityAIMConvexGeometryProblem25Wanted
