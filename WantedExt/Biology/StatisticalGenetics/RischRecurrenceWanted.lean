/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Risch's recurrence-risk ratios under a multiplicative multilocus model

For a binary trait with prevalence `K` and relatives of type `R` (sibs, parent–offspring,
second-degree relatives, …), the recurrence risk `K_R` is the probability that a relative of an
affected individual is affected, and Risch's recurrence-risk ratio is `λ_R = K_R / K`. At one
locus with penetrance `f`, `K K_R - K² = 2φ_R V_A + Δ_R V_D`, the covariance between relatives
of the penetrance, so `λ_R - 1 = (2φ_R V_A + Δ_R V_D) / K²`; with no dominance variance,
`λ_R - 1` halves with each degree of relationship (Risch 1990). That one-locus covariance is
proved on main as `MathlibExt.Biology.StatisticalGenetics.CovarianceRelatives.LocusModel.relCov_eq`
in `Domains.Biology.StatisticalGenetics.CovarianceRelatives`.

Recorded here: the missing multilocus part. Under a multiplicative model (penetrance the product
of locus penetrances, genotypes of a relative pair independent across loci) `λ_R` is the product
of the locus ratios `λ_{R,i}` (derived from the definitions), and when every locus halves
`λ - 1` from first- to second-degree relatives, the product decreases faster: `λ_1 - 1` is at
least twice `λ_2 - 1`, strictly so when two loci contribute (the abstract's "for a
multiplicative (epistasis) model, `λ_R - 1` decreases more rapidly"). Risch's linkage-power
analysis is not formalized.

Sources: N. Risch, "Linkage strategies for genetically complex traits. I. Multilocus models",
Am. J. Hum. Genet. 46 (1990) 222–228 (abstract; the body formulas are restated from the
definitions).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.RischRecurrenceWanted

open Finset

/-- Prevalence `K = ∑_g π(g) f(g)` of a trait with penetrance `f` under the genotype law `π`. -/
noncomputable def prevalence {G : Type*} [Fintype G] (π f : G → ℝ) : ℝ := ∑ g, π g * f g

/-- Probability `∑_{g,h} J(g, h) f(g) f(h)` that both members of a relative pair are affected,
for the joint genotype law `J` of the pair and penetrance `f` (phenotypes conditionally
independent given genotypes). -/
noncomputable def pairAffected {G : Type*} [Fintype G] (J : G → G → ℝ) (f : G → ℝ) : ℝ :=
  ∑ g, ∑ h, J g h * f g * f h

/-- **Risch's recurrence-risk ratio** `λ_R = K_R / K = P(both affected) / K²`, where
`K = prevalence π f`. The intended domain is a positive prevalence `K > 0`. If `K = 0` the
denominator vanishes and the value is `0`, since Lean's division is total (`x / 0 = 0`). -/
noncomputable def recurrenceRatio {G : Type*} [Fintype G] (π : G → ℝ) (J : G → G → ℝ)
    (f : G → ℝ) : ℝ :=
  pairAffected J f / prevalence π f ^ 2

/-- `J` is the joint genotype law of a relative pair whose members each have genotype law `π`:
a probability law on pairs with both marginals equal to `π`. -/
def IsPairLaw {G : Type*} [Fintype G] (π : G → ℝ) (J : G → G → ℝ) : Prop :=
  (∀ g, 0 ≤ π g) ∧ ∑ g, π g = 1 ∧ (∀ g h, 0 ≤ J g h) ∧
    (∀ g, ∑ h, J g h = π g) ∧ ∀ h, ∑ g, J g h = π h

/-- **Multiplicative model: `λ_R` is the product of the locus ratios** (Risch 1990; derived):
for finitely many loci `i` with genotype laws `π i`, relative-pair laws `J i` and penetrances
`f i` with values in `[0, 1]` and positive locus prevalences, the multilocus model with genotype
law `∏ᵢ π i (gᵢ)`, pair law `∏ᵢ J i (gᵢ) (hᵢ)` (loci independent) and penetrance
`∏ᵢ f i (gᵢ)` has `λ_R = ∏ᵢ λ_{R,i}`.

Source: Risch (1990). -/
public theorem_wanted recurrenceRatio_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, Fintype (G i)] (π : ∀ i, G i → ℝ) (J : ∀ i, G i → G i → ℝ)
    (f : ∀ i, G i → ℝ) (hJ : ∀ i, IsPairLaw (π i) (J i))
    (hf : ∀ i g, 0 ≤ f i g ∧ f i g ≤ 1) (hK : ∀ i, 0 < prevalence (π i) (f i)) :
    recurrenceRatio (fun g : ∀ i, G i => ∏ i, π i (g i))
        (fun g h : ∀ i, G i => ∏ i, J i (g i) (h i)) (fun g => ∏ i, f i (g i)) =
      ∏ i, recurrenceRatio (π i) (J i) (f i)

/-- **Under a multiplicative model `λ - 1` more than halves per degree** (Risch 1990, abstract):
if each locus has `λ_{1,i} ≥ 1` for first-degree relatives and halves `λ - 1` for second-degree
relatives, `λ_{2,i} - 1 = (λ_{1,i} - 1) / 2` (one locus, no dominance variance), then the
multilocus ratios `∏ λ_{1,i}` and `∏ λ_{2,i}` satisfy `∏ λ_{1,i} - 1 ≥ 2 (∏ λ_{2,i} - 1)`, with
strict inequality as soon as two distinct loci have `λ_{1,i} > 1`.

Source: Risch (1990), abstract. -/
public theorem_wanted prod_sub_one_ge_two_mul {ι : Type*} [Fintype ι] (lam₁ lam₂ : ι → ℝ)
    (h₁ : ∀ i, 1 ≤ lam₁ i) (hhalf : ∀ i, lam₂ i - 1 = (lam₁ i - 1) / 2) :
    2 * (∏ i, lam₂ i - 1) ≤ ∏ i, lam₁ i - 1 ∧
      ((∃ i j, i ≠ j ∧ 1 < lam₁ i ∧ 1 < lam₁ j) → 2 * (∏ i, lam₂ i - 1) < ∏ i, lam₁ i - 1)

end WantedExt.Biology.StatisticalGenetics.RischRecurrenceWanted
