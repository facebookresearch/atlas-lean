/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Levin's formula with a population-standardized risk ratio

There is a two-stratum model with positive stratum weights summing to one, exposure probabilities
strictly between zero and one, and exposed and unexposed risks in $(0, 1]$. The exposure
probabilities and the unexposed risks both differ between strata. In this model, Levin's formula
using the population exposure prevalence and the risk ratio standardized to the total population
is $1/7$, while the causal population attributable fraction is $1/13$. Under consistency and
conditional exchangeability within strata, the stratum-specific risks give the corresponding
observed and counterfactual population risks. The example is about two population quantities,
not the bias of a statistical estimator.

## References

* Ahmad Khosravi, Maryam Nazemipour, Tomohiro Shinozaki, and Mohammad Ali Mansournia,
  *Population attributable fraction in textbooks: Time to revise*, Global Epidemiology 3 (2021),
  article 100062, equation (3) and the “Confounding adjustment” section. The two-stratum
  counterexample is derived, not an example from the article.
* M. L. Levin, *The occurrence of lung cancer in man*, Acta Unio Internationalis Contra Cancrum
  9(3) (1953), pp. 531–541, the original source of Levin's formula.
* K. J. Rothman, S. Greenland, and T. L. Lash (eds.), *Modern Epidemiology*, 3rd ed.,
  Lippincott Williams & Wilkins, 2008, cited by Khosravi et al. on confounding.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.PopulationAttributableFractionWanted

variable {𝒵 : Type*} [Fintype 𝒵]

/-- Levin's formula `Pe (RR - 1) / (1 + Pe (RR - 1))`. It is meaningful when `1 + Pe (RR - 1) ≠ 0`,
which holds for `Pe ∈ [0, 1)` and `RR ≥ 0` or for `Pe ∈ [0, 1]` and `RR > 0`; a zero denominator
gives `0` by Lean's convention `x / 0 = 0`. -/
noncomputable def levin (Pe RR : ℝ) : ℝ :=
  Pe * (RR - 1) / (1 + Pe * (RR - 1))

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

/-- The risk ratio standardized to the total population, `∑_z P(z) r₁(z) / ∑_z P(z) r₀(z)`. It is
meaningful when `∑_z P(z) r₀(z) > 0`; a zero denominator gives `0` by Lean's convention `x / 0 = 0`.
-/
noncomputable def totalStandardizedRR (pz r₀ r₁ : 𝒵 → ℝ) : ℝ :=
  (∑ z, pz z * r₁ z) / ∑ z, pz z * r₀ z

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
theorem exists_levin_totalRR_ne_causalPAF :
    ∃ pz e r₀ r₁ : Fin 2 → ℝ, (∀ z, 0 < pz z) ∧ ∑ z, pz z = 1 ∧ (∀ z, 0 < e z) ∧
      (∀ z, e z < 1) ∧ (∀ z, 0 < r₀ z) ∧ (∀ z, r₀ z ≤ 1) ∧ (∀ z, 0 < r₁ z) ∧ (∀ z, r₁ z ≤ 1) ∧
      e 0 ≠ e 1 ∧ r₀ 0 ≠ r₀ 1 ∧
      levin (exposurePrevalence pz e) (totalStandardizedRR pz r₀ r₁) ≠ causalPAF pz e r₀ r₁ := by
  let pz : Fin 2 → ℝ := ![1 / 2, 1 / 2]
  let e : Fin 2 → ℝ := ![1 / 4, 3 / 4]
  let r₀ : Fin 2 → ℝ := ![1 / 4, 1 / 2]
  let r₁ : Fin 2 → ℝ := ![1 / 2, 1 / 2]
  have hLevin : levin (exposurePrevalence pz e) (totalStandardizedRR pz r₀ r₁) = 1 / 7 := by
    norm_num [levin, exposurePrevalence, totalStandardizedRR, Fin.sum_univ_two, pz, e, r₀, r₁]
  have hPAF : causalPAF pz e r₀ r₁ = 1 / 13 := by
    norm_num [causalPAF, observedRisk, Fin.sum_univ_two, pz, e, r₀, r₁]
  refine ⟨pz, e, r₀, r₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    fin_cases z <;> norm_num [pz]
  · norm_num [Fin.sum_univ_two, pz]
  · intro z
    fin_cases z <;> norm_num [e]
  · intro z
    fin_cases z <;> norm_num [e]
  · intro z
    fin_cases z <;> norm_num [r₀]
  · intro z
    fin_cases z <;> norm_num [r₀]
  · intro z
    fin_cases z <;> norm_num [r₁]
  · intro z
    fin_cases z <;> norm_num [r₁]
  · norm_num [e]
  · norm_num [r₀]
  · rw [hLevin, hPAF]
    norm_num

end WantedExt.Biology.StatisticalGenetics.PopulationAttributableFractionWanted
