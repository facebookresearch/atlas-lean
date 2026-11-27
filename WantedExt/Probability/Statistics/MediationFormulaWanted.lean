/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The mediation formula for natural direct and indirect effects

Let `X` be an exposure, `M` a mediator and `Z` pre-exposure covariates, all with finitely many
values, and let `Y(x, m)` and `M(x)` be potential outcomes, with observed `M = M(X)` and
`Y = Y(X, M)`. The natural direct effect of changing `x₀` to `x₁` is
`NDE = E[Y(x₁, M(x₀))] - E[Y(x₀, M(x₀))]` and the natural indirect effect is
`NIE = E[Y(x₁, M(x₁))] - E[Y(x₁, M(x₀))]`, so the total effect is `NDE + NIE`.

Pearl's mediation formula identifies both from the observed law when, given `Z`, there is no
confounding of the exposure–outcome, exposure–mediator and mediator–outcome relations and the
mediator–outcome relation is not confounded by a consequence of the exposure:
`NDE = ∑_{z, m} (E[Y | x₁, m, z] - E[Y | x₀, m, z]) P(m | x₀, z) P(z)` and
`NIE = ∑_{z, m} E[Y | x₁, m, z] (P(m | x₁, z) - P(m | x₀, z)) P(z)`. Conditional independence
given `Z = z` is independence under the conditional measure `μ[|Z = z]`.

In the additive linear mediation model the natural indirect effect is the product of
coefficients; that case is already proved in
`CSLibExt.MachineLearning.GraphicalModels.LinearMediation` (`naturalIndirectEffect_eq`,
`totalEffect_eq_add`). For finite structural causal models the mediation formula is proved in
`CSLibExt.MachineLearning.GraphicalModels.MediationFormula`
(`FiniteSCM.nde_eq_mediationFormulaNDE`, `FiniteSCM.nie_eq_mediationFormulaNIE`) under the same
four no-confounding conditions and positivity; the statement here is for general potential
outcomes on an arbitrary probability space. The natural indirect effect here follows the
`TE - NDE` convention, `E[Y(x₁, M(x₁))] - E[Y(x₁, M(x₀))]`, whereas `FiniteSCM.nie` follows
Pearl (2001), `E[Y(x₀, M(x₁))] - E[Y(x₀, M(x₀))]`.

Sources: J. Pearl, "Direct and indirect effects", Proc. 17th Conf. Uncertainty in Artificial
Intelligence (2001) 411–420 (arXiv:1301.2300); T. J. VanderWeele and S. Vansteelandt,
"Conceptual issues concerning mediation, interventions and composition", Stat. Interface 2
(2009) 457–468.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace WantedExt.Probability.Statistics.MediationFormulaWanted

open MeasureTheory ProbabilityTheory

variable {Ω 𝒳 ℳ 𝒵 : Type*} [MeasurableSpace Ω]
  [Fintype 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
  [Fintype ℳ] [MeasurableSpace ℳ] [MeasurableSingletonClass ℳ]
  [Fintype 𝒵] [MeasurableSpace 𝒵] [MeasurableSingletonClass 𝒵]

/-- **Observed mediator.** The observed mediator `M = M(X)`. -/
def observedMediator (X : Ω → 𝒳) (Mpot : 𝒳 → Ω → ℳ) (ω : Ω) : ℳ :=
  Mpot (X ω) ω

/-- **Observed outcome.** The observed outcome `Y = Y(X, M(X))`. -/
def observedOutcome (X : Ω → 𝒳) (Mpot : 𝒳 → Ω → ℳ) (Ypot : 𝒳 → ℳ → Ω → ℝ) (ω : Ω) : ℝ :=
  Ypot (X ω) (observedMediator X Mpot ω) ω

/-- **Mean of a nested potential outcome.** The mean `E[Y(x, M(x'))]`. -/
noncomputable def nestedMean (μ : Measure Ω) (Mpot : 𝒳 → Ω → ℳ) (Ypot : 𝒳 → ℳ → Ω → ℝ)
    (x x' : 𝒳) : ℝ :=
  ∫ ω, Ypot x (Mpot x' ω) ω ∂μ

/-- **Observed conditional mean outcome.** The observed conditional mean
`E[Y | X = x, M = m, Z = z]`. -/
noncomputable def condMeanOutcome (μ : Measure Ω) (X : Ω → 𝒳) (Mpot : 𝒳 → Ω → ℳ)
    (Ypot : 𝒳 → ℳ → Ω → ℝ) (Z : Ω → 𝒵) (x : 𝒳) (m : ℳ) (z : 𝒵) : ℝ :=
  ∫ ω, observedOutcome X Mpot Ypot ω
    ∂(μ[|X ⁻¹' {x} ∩ observedMediator X Mpot ⁻¹' {m} ∩ Z ⁻¹' {z}])

/-- **Observed conditional mediator probability.** The observed conditional probability
`P(M = m | X = x, Z = z)`. -/
noncomputable def condProbMediator (μ : Measure Ω) (X : Ω → 𝒳) (Mpot : 𝒳 → Ω → ℳ)
    (Z : Ω → 𝒵) (m : ℳ) (x : 𝒳) (z : 𝒵) : ℝ :=
  μ.real (observedMediator X Mpot ⁻¹' {m} ∩ X ⁻¹' {x} ∩ Z ⁻¹' {z}) /
    μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z})

/-- **The mediation formula.** Let `μ` be a probability measure on `Ω`; let the
exposure `X : Ω → 𝒳`, the covariates `Z : Ω → 𝒵` and the potential mediators `M(x) : Ω → ℳ` be
measurable with finite value types having measurable singletons; and let the potential outcomes
`Y(x, m) : Ω → ℝ` be measurable and bounded (`|Y(x, m)| ≤ C`). Assume, for all `x, x', m, z`:
* positivity: `P(X = x, M = m, Z = z) > 0`;
* no exposure–outcome confounding: `Y(x, m)` is independent of `X` given `Z = z`;
* no mediator–outcome confounding: `Y(x, m)` is independent of `M(x)` given `X = x, Z = z`;
* no exposure–mediator confounding: `M(x)` is independent of `X` given `Z = z`;
* no exposure-induced mediator–outcome confounding: `Y(x, m)` is independent of `M(x')` given
  `Z = z`.

Then for all `x₀, x₁`, with `P(z) = μ(Z = z)`, the natural direct effect (NDE) and the
total-minus-direct indirect effect (`NIE = TE - NDE`, holding exposure at `x₁` rather than at
`x₀` as in Pearl 2001's `E[Y(x₀, M(x₁))] - E[Y(x₀, M(x₀))]`) satisfy
`E[Y(x₁, M(x₀))] - E[Y(x₀, M(x₀))] = ∑_{z, m} (E[Y | x₁, m, z] - E[Y | x₀, m, z]) P(m | x₀, z) P(z)`
and
`E[Y(x₁, M(x₁))] - E[Y(x₁, M(x₀))] = ∑_{z, m} E[Y | x₁, m, z] (P(m | x₁, z) - P(m | x₀, z)) P(z)`.

Sources: J. Pearl, "Direct and indirect effects", Proc. 17th Conf. Uncertainty in Artificial
Intelligence (2001) 411–420 (arXiv:1301.2300); T. J. VanderWeele and S. Vansteelandt, "Conceptual
issues concerning mediation, interventions and composition", Stat. Interface 2 (2009) 457–468. -/
public theorem_wanted mediation_formula (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → 𝒳)
    (Z : Ω → 𝒵) (Mpot : 𝒳 → Ω → ℳ) (Ypot : 𝒳 → ℳ → Ω → ℝ) (hX : Measurable X)
    (hZ : Measurable Z) (hM : ∀ x, Measurable (Mpot x)) (hY : ∀ x m, Measurable (Ypot x m))
    (C : ℝ) (hC : ∀ x m ω, |Ypot x m ω| ≤ C)
    (hpos : ∀ x m z,
      0 < μ.real (X ⁻¹' {x} ∩ observedMediator X Mpot ⁻¹' {m} ∩ Z ⁻¹' {z}))
    (hXY : ∀ x m z, IndepFun (Ypot x m) X (μ[|Z ⁻¹' {z}]))
    (hMY : ∀ x m z, IndepFun (Ypot x m) (Mpot x) (μ[|X ⁻¹' {x} ∩ Z ⁻¹' {z}]))
    (hXM : ∀ x z, IndepFun (Mpot x) X (μ[|Z ⁻¹' {z}]))
    (hcross : ∀ x x' m z, IndepFun (Ypot x m) (Mpot x') (μ[|Z ⁻¹' {z}])) (x₀ x₁ : 𝒳) :
    nestedMean μ Mpot Ypot x₁ x₀ - nestedMean μ Mpot Ypot x₀ x₀ =
        ∑ z, ∑ m, (condMeanOutcome μ X Mpot Ypot Z x₁ m z -
            condMeanOutcome μ X Mpot Ypot Z x₀ m z) *
          condProbMediator μ X Mpot Z m x₀ z * μ.real (Z ⁻¹' {z}) ∧
      nestedMean μ Mpot Ypot x₁ x₁ - nestedMean μ Mpot Ypot x₁ x₀ =
        ∑ z, ∑ m, condMeanOutcome μ X Mpot Ypot Z x₁ m z *
          (condProbMediator μ X Mpot Z m x₁ z - condProbMediator μ X Mpot Z m x₀ z) *
            μ.real (Z ⁻¹' {z})

end WantedExt.Probability.Statistics.MediationFormulaWanted
