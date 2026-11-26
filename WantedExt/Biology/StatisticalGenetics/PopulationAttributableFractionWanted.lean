/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The population attributable fraction: Levin and Miettinen formulas

The population attributable fraction is the net proportional change in population risk had the
exposure been absent, `PAF = (P(Y = 1) - P(Y(0) = 1)) / P(Y = 1) = 1 - P(Y(0) = 1) / P(Y = 1)`;
without confounding this is `(P(Y = 1) - P(Y = 1 | E = 0)) / P(Y = 1)`. It is negative when the
exposure is protective. Reading it as the fraction of observed cases that the exposure caused (and
that removing it would prevent) needs the further assumption that the exposure prevents disease in
no one (monotonicity: no protective effect at the individual level). Take finitely many strata `z`
with `P(z) > 0`, exposure probabilities `e(z) = P(E = 1 | z)` and potential risks
`r₀(z) = P(Y(0) = 1 | z)`, `r₁(z) = P(Y(1) = 1 | z)`, with consistency and exchangeability within
strata, so that `P(Y = 1 | E = e, z) = r_e(z)`.

Levin's formula `Pe (RR - 1) / (1 + Pe (RR - 1))`, with the population exposure prevalence `Pe`,
gives the PAF from the crude risk ratio when there is no confounding. Miettinen's formula
`Pc (RR - 1) / RR`, with the exposure prevalence `Pc` among cases, agrees with Levin's for the
crude risk ratio through `Pc = Pe RR / (Pe RR + 1 - Pe)`. Under confounding, Miettinen's formula
with the risk ratio standardized to the exposed gives the PAF, while Levin's formula with an
adjusted risk ratio can disagree with it: there is a confounded model in which the two differ.

Sources: M. L. Levin, "The occurrence of lung cancer in man", Acta Unio Int. Contra Cancrum 9
(1953) 531–541; O. S. Miettinen, "Proportion of disease caused or prevented by a given exposure,
trait or intervention", Am. J. Epidemiol. 99 (1974) 325–332; exposition in A. Khosravi,
M. Nazemipour, T. Shinozaki and M. A. Mansournia, "Population attributable fraction in
textbooks: Time to revise" (2021), formulas (4) and (5).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.PopulationAttributableFractionWanted

variable {𝒵 : Type*} [Fintype 𝒵]

/-- Levin's formula `Pe (RR - 1) / (1 + Pe (RR - 1))`. It is meaningful when `1 + Pe (RR - 1) ≠ 0`,
which holds for `Pe ∈ [0, 1)` and `RR ≥ 0` or for `Pe ∈ [0, 1]` and `RR > 0`; a zero denominator
gives `0` by Lean's convention `x / 0 = 0`. -/
noncomputable def levin (Pe RR : ℝ) : ℝ :=
  Pe * (RR - 1) / (1 + Pe * (RR - 1))

/-- Miettinen's formula `Pc (RR - 1) / RR`. It is meaningful for `RR ≠ 0`; at `RR = 0`, Lean's
convention `x / 0 = 0` makes the value `0`. -/
noncomputable def miettinen (Pc RR : ℝ) : ℝ :=
  Pc * (RR - 1) / RR

/-- The exposure prevalence `Pe = ∑_z P(z) e(z)`. -/
def exposurePrevalence (pz e : 𝒵 → ℝ) : ℝ :=
  ∑ z, pz z * e z

/-- The observed risk `P(Y = 1) = ∑_z P(z) (e(z) r₁(z) + (1 - e(z)) r₀(z))`. -/
def observedRisk (pz e r₀ r₁ : 𝒵 → ℝ) : ℝ :=
  ∑ z, pz z * (e z * r₁ z + (1 - e z) * r₀ z)

/-- The causal attributable fraction `1 - P(Y(0) = 1) / P(Y = 1)`, with
`P(Y(0) = 1) = ∑_z P(z) r₀(z)`: the net proportional change in population risk had the exposure been
absent (negative when the exposure is protective). It is meaningful when `P(Y = 1) > 0`; if
`P(Y = 1) = 0`, Lean's convention `x / 0 = 0` makes the quotient `0` and the value `1`. -/
noncomputable def causalPAF (pz e r₀ r₁ : 𝒵 → ℝ) : ℝ :=
  1 - (∑ z, pz z * r₀ z) / observedRisk pz e r₀ r₁

/-- The risk among the exposed, `P(Y = 1 | E = 1) = ∑_z P(z) e(z) r₁(z) / Pe`. It is meaningful when
`Pe > 0`; if `Pe = 0`, Lean's convention `x / 0 = 0` makes the value `0`. -/
noncomputable def riskExposed (pz e r₁ : 𝒵 → ℝ) : ℝ :=
  (∑ z, pz z * e z * r₁ z) / exposurePrevalence pz e

/-- The risk among the unexposed, `P(Y = 1 | E = 0) = ∑_z P(z) (1 - e(z)) r₀(z) / (1 - Pe)`. It is
meaningful when `Pe < 1`; if `Pe = 1`, Lean's convention `x / 0 = 0` makes the value `0`. -/
noncomputable def riskUnexposed (pz e r₀ : 𝒵 → ℝ) : ℝ :=
  (∑ z, pz z * (1 - e z) * r₀ z) / (1 - exposurePrevalence pz e)

/-- The crude risk ratio `P(Y = 1 | E = 1) / P(Y = 1 | E = 0)`. It is meaningful when `0 < Pe < 1`
and the risk among the unexposed is positive; a zero denominator gives `0` by Lean's convention
`x / 0 = 0`. -/
noncomputable def crudeRR (pz e r₀ r₁ : 𝒵 → ℝ) : ℝ :=
  riskExposed pz e r₁ / riskUnexposed pz e r₀

/-- The risk ratio standardized to the exposed, `∑_z P(z) e(z) r₁(z) / ∑_z P(z) e(z) r₀(z)`. It is
meaningful when `∑_z P(z) e(z) r₀(z) > 0`; a zero denominator gives `0` by Lean's convention
`x / 0 = 0`. -/
noncomputable def exposedStandardizedRR (pz e r₀ r₁ : 𝒵 → ℝ) : ℝ :=
  (∑ z, pz z * e z * r₁ z) / ∑ z, pz z * e z * r₀ z

/-- The risk ratio standardized to the total population, `∑_z P(z) r₁(z) / ∑_z P(z) r₀(z)`. It is
meaningful when `∑_z P(z) r₀(z) > 0`; a zero denominator gives `0` by Lean's convention `x / 0 = 0`.
-/
noncomputable def totalStandardizedRR (pz r₀ r₁ : 𝒵 → ℝ) : ℝ :=
  (∑ z, pz z * r₁ z) / ∑ z, pz z * r₀ z

/-- The exposure prevalence among cases, `Pc = P(E = 1 | Y = 1) = ∑_z P(z) e(z) r₁(z) / P(Y = 1)`.
It is meaningful when `P(Y = 1) > 0`; if `P(Y = 1) = 0`, Lean's convention `x / 0 = 0` makes the
value `0`. -/
noncomputable def casePrevalence (pz e r₀ r₁ : 𝒵 → ℝ) : ℝ :=
  (∑ z, pz z * e z * r₁ z) / observedRisk pz e r₀ r₁

/-- **Levin's formula without confounding** (Levin 1953; Khosravi et al. 2021). In the finite
strata model, let `P(z) > 0` with `∑_z P(z) = 1`, `0 < e(z) < 1` and `0 ≤ r₀(z), r₁(z) ≤ 1`,
let the risk among the unexposed be positive, and assume no confounding: the mean of `r₀` among
the exposed equals its mean among the unexposed,
`∑_z P(z) e(z) r₀(z) / Pe = ∑_z P(z) (1 - e(z)) r₀(z) / (1 - Pe)`. Then Levin's formula with
`Pe` and the crude risk ratio equals the causal attributable fraction.

Source: Khosravi et al. (2021), on Levin's formula "assuming no confounding". -/
public theorem_wanted levin_crudeRR_eq_causalPAF (pz e r₀ r₁ : 𝒵 → ℝ) (hpz : ∀ z, 0 < pz z)
    (hsum : ∑ z, pz z = 1) (he0 : ∀ z, 0 < e z) (he1 : ∀ z, e z < 1) (hr₀ : ∀ z, 0 ≤ r₀ z)
    (hr₀' : ∀ z, r₀ z ≤ 1) (hr₁ : ∀ z, 0 ≤ r₁ z) (hr₁' : ∀ z, r₁ z ≤ 1)
    (hunexp : 0 < riskUnexposed pz e r₀)
    (hnoconf : (∑ z, pz z * e z * r₀ z) / exposurePrevalence pz e = riskUnexposed pz e r₀) :
    levin (exposurePrevalence pz e) (crudeRR pz e r₀ r₁) = causalPAF pz e r₀ r₁

/-- **Levin equals Miettinen for the crude risk ratio** (Miettinen 1974; Khosravi et al. 2021,
(4)–(5)). For real `Pe ∈ (0, 1)` and `RR > 0`, with `Pc = Pe RR / (Pe RR + 1 - Pe)`, Levin's
formula `levin Pe RR` equals Miettinen's formula `miettinen Pc RR`. In the finite strata model
with `P(z) > 0`, `∑_z P(z) = 1`, `0 < e(z) < 1`, `0 ≤ r₀(z), r₁(z) ≤ 1` and positive risks among
the exposed and among the unexposed, the exposure prevalence among cases satisfies
`Pc = Pe RR_c / (Pe RR_c + 1 - Pe)` for the crude risk ratio `RR_c`.

Source: Khosravi et al. (2021), (4) and (5). -/
public theorem_wanted levin_eq_miettinen :
    (∀ Pe RR : ℝ, 0 < Pe → Pe < 1 → 0 < RR →
      levin Pe RR = miettinen (Pe * RR / (Pe * RR + 1 - Pe)) RR) ∧
    ∀ pz e r₀ r₁ : 𝒵 → ℝ, (∀ z, 0 < pz z) → ∑ z, pz z = 1 → (∀ z, 0 < e z) → (∀ z, e z < 1) →
      (∀ z, 0 ≤ r₀ z) → (∀ z, r₀ z ≤ 1) → (∀ z, 0 ≤ r₁ z) → (∀ z, r₁ z ≤ 1) →
      0 < riskExposed pz e r₁ → 0 < riskUnexposed pz e r₀ →
      casePrevalence pz e r₀ r₁ =
        exposurePrevalence pz e * crudeRR pz e r₀ r₁ /
          (exposurePrevalence pz e * crudeRR pz e r₀ r₁ + 1 - exposurePrevalence pz e)

/-- **Miettinen's formula under confounding** (Miettinen 1974; Khosravi et al. 2021). In the finite
strata model, let `P(z) > 0` with `∑_z P(z) = 1`, `0 < e(z) < 1` and `0 ≤ r₀(z), r₁(z) ≤ 1`, and
let `∑_z P(z) e(z) r₀(z) > 0` and `∑_z P(z) e(z) r₁(z) > 0`. With no assumption on confounding,
Miettinen's formula with the exposure prevalence among cases and the risk ratio standardized to
the exposed equals the causal attributable fraction.

Source: Khosravi et al. (2021), on plugging in the risk ratio standardized to the exposed. -/
public theorem_wanted miettinen_exposedRR_eq_causalPAF (pz e r₀ r₁ : 𝒵 → ℝ)
    (hpz : ∀ z, 0 < pz z) (hsum : ∑ z, pz z = 1) (he0 : ∀ z, 0 < e z) (he1 : ∀ z, e z < 1)
    (hr₀ : ∀ z, 0 ≤ r₀ z) (hr₀' : ∀ z, r₀ z ≤ 1) (hr₁ : ∀ z, 0 ≤ r₁ z) (hr₁' : ∀ z, r₁ z ≤ 1)
    (h₀ : 0 < ∑ z, pz z * e z * r₀ z) (h₁ : 0 < ∑ z, pz z * e z * r₁ z) :
    miettinen (casePrevalence pz e r₀ r₁) (exposedStandardizedRR pz e r₀ r₁) =
      causalPAF pz e r₀ r₁

/-- **Levin's formula with an adjusted risk ratio can disagree with the PAF.** There is a
nondegenerate confounded finite strata model with two strata, `P(z) > 0`, `∑_z P(z) = 1`,
`0 < e(z) < 1`, strictly positive risks `0 < r₀(z), r₁(z) ≤ 1` (hence positive observed and
counterfactual risks), and confounding (`e 0 ≠ e 1` and `r₀ 0 ≠ r₀ 1`), in which Levin's formula
with `Pe` and the risk ratio standardized to the total population differs from the causal
attributable fraction (Khosravi et al. 2021). This is a counterexample: it shows that the two can
disagree in one confounded model, not that they disagree in every confounded model, and it is not
a statement about the bias of an estimator.

Source: Khosravi et al. (2021), who call Levin's formula "biased in the presence of confounding
even if the adjusted RR is used"; the counterexample is derived. -/
public theorem_wanted exists_levin_totalRR_ne_causalPAF :
    ∃ pz e r₀ r₁ : Fin 2 → ℝ, (∀ z, 0 < pz z) ∧ ∑ z, pz z = 1 ∧ (∀ z, 0 < e z) ∧
      (∀ z, e z < 1) ∧ (∀ z, 0 < r₀ z) ∧ (∀ z, r₀ z ≤ 1) ∧ (∀ z, 0 < r₁ z) ∧ (∀ z, r₁ z ≤ 1) ∧
      e 0 ≠ e 1 ∧ r₀ 0 ≠ r₀ 1 ∧
      levin (exposurePrevalence pz e) (totalStandardizedRR pz r₀ r₁) ≠ causalPAF pz e r₀ r₁

end WantedExt.Biology.StatisticalGenetics.PopulationAttributableFractionWanted
