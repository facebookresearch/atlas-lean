/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Risch's recurrence-risk ratios under a multiplicative multilocus model

This module defines prevalence, pair-affected probability, recurrence-risk ratio and
relative-pair laws, and proves that the multilocus recurrence-risk ratio is the product
of the locus ratios under multiplicative penetrance and independence across loci.

Source: N. Risch, "Linkage strategies for genetically complex traits. I. Multilocus models",
Am. J. Hum. Genet. 46 (1990) 222–228.
-/

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
public theorem recurrenceRatio_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, Fintype (G i)] (π : ∀ i, G i → ℝ) (J : ∀ i, G i → G i → ℝ)
    (f : ∀ i, G i → ℝ) (hJ : ∀ i, IsPairLaw (π i) (J i))
    (hf : ∀ i g, 0 ≤ f i g ∧ f i g ≤ 1) (hK : ∀ i, 0 < prevalence (π i) (f i)) :
    recurrenceRatio (fun g : ∀ i, G i => ∏ i, π i (g i))
        (fun g h : ∀ i, G i => ∏ i, J i (g i) (h i)) (fun g => ∏ i, f i (g i)) =
      ∏ i, recurrenceRatio (π i) (J i) (f i) := by
  classical
  have hw : ∀ i g, 0 ≤ π i g * f i g :=
    fun i g => mul_nonneg ((hJ i).1 g) (hf i g).1
  have hex : ∀ i, ∃ g, 0 < π i g * f i g := by
    intro i
    obtain ⟨g, _, hg⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun g _ => hw i g)).mp (hK i)
    exact ⟨g, hg⟩
  choose g hg using hex
  have hKpi : 0 < prevalence (fun g : ∀ i, G i => ∏ i, π i (g i))
      (fun g => ∏ i, f i (g i)) := by
    unfold prevalence
    simp only [← Finset.prod_mul_distrib]
    exact Finset.sum_pos'
      (fun x _ => Finset.prod_nonneg fun i _ => hw i (x i))
      ⟨g, Finset.mem_univ _, Finset.prod_pos fun i _ => hg i⟩
  unfold recurrenceRatio
  apply (div_eq_iff (pow_ne_zero 2 hKpi.ne')).2
  simp only [prevalence, pairAffected, Finset.prod_div_distrib,
    Finset.prod_pow, Fintype.prod_sum, Finset.prod_mul_distrib]
  exact (div_mul_cancel₀ _ (pow_ne_zero 2 hKpi.ne')).symm

end WantedExt.Biology.StatisticalGenetics.RischRecurrenceWanted
