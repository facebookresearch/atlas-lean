/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.ReadMixtureContamination

@[expose] public section

open Domains.Biology.StatisticalGenetics.ReadMixtureContamination
open MathlibExt.Biology.PopulationGenetics
open scoped NNReal ENNReal

namespace DomainsTest.Biology.StatisticalGenetics.ReadMixtureContamination

/-! ### Base calls (Table 1 of Jun et al. 2012)

A site with reference allele `A` (`0`) and alternative allele `C` (`1`); its genotypes `0, 1, 2`
are `AA`, `AC` and `CC`. -/

/-- The site `A/C` covered by `n` reads, each of phred quality `10`. -/
noncomputable abbrev acSite (n : ℕ) : Site := ⟨0, 1, by decide, n, fun _ => 10⟩

/-- An `AA` homozygote is called `A` without an error. -/
example : callProb (acSite 1) 0 false 0 = 1 := by
  norm_num [callProb, alleleCallProb, acSite]

/-- On an error an `AA` homozygote is called `C` with probability `1/3`. -/
example : callProb (acSite 1) 0 true 1 = 1 / 3 := by
  norm_num [callProb, alleleCallProb, acSite]

/-- On an error an `AC` heterozygote is called `A` with probability `1/6`. -/
example : callProb (acSite 1) 1 true 0 = 1 / 6 := by
  norm_num [callProb, alleleCallProb, acSite]

/-- Without an error an `AC` heterozygote is called `C` with probability `1/2`. -/
example : callProb (acSite 1) 1 false 1 = 1 / 2 := by
  norm_num [callProb, alleleCallProb, acSite]

/-- On an error an `AC` heterozygote is called neither `A` nor `C` with probability `2/3`. -/
example : callProb (acSite 1) 1 true 2 + callProb (acSite 1) 1 true 3 = 2 / 3 := by
  norm_num [callProb, alleleCallProb, acSite]

/-- A call of phred quality `10` is an error with probability `1/10`. -/
theorem phredErrorProb_ten : phredErrorProb 10 = 1 / 10 := by
  rw [phredErrorProb, NNReal.coe_ofNat, show -(10 : ℝ) / 10 = -1 by norm_num, Real.rpow_neg_one]
  norm_num

/-- A call of phred quality `20` is an error with probability `1/100`. -/
example : phredErrorProb 20 = 1 / 100 := by
  rw [phredErrorProb, NNReal.coe_ofNat, show -(20 : ℝ) / 10 = ((-2 : ℤ) : ℝ) by norm_num,
    Real.rpow_intCast]
  norm_num

/-! ### Hardy–Weinberg genotype law -/

/-- A population whose parents are all heterozygous: the allele frequencies are `1/2`. -/
noncomputable def allHet : PMF (Bool × Bool) := PMF.pure (true, false)

theorem gamete_allHet (a : Bool) : HardyWeinberg.gamete allHet a = 2⁻¹ := by
  rw [HardyWeinberg.gamete_apply]
  cases a <;> simp [allHet, PMF.pure_apply]

theorem hwGenotype_allHet_zero : (hwGenotype allHet 0).toReal = 1 / 4 := by
  rw [hwGenotype_zero, gamete_allHet]
  norm_num

theorem hwGenotype_allHet_one : (hwGenotype allHet 1).toReal = 1 / 2 := by
  rw [hwGenotype_one, gamete_allHet, gamete_allHet, ENNReal.toReal_mul, ENNReal.toReal_mul]
  norm_num

theorem hwGenotype_allHet_two : (hwGenotype allHet 2).toReal = 1 / 4 := by
  rw [hwGenotype_two, gamete_allHet]
  norm_num

/-! ### Likelihoods at one site -/

/-- Two reads at the `A/C` site, called `A` and `C`. -/
def twoCalls : ∀ _ : Unit, Fin (acSite 2).depth → Fin 4 := fun _ => ![0, 1]

/-- With two reads the sequence-only likelihood depends on `α`: `L(0) = 223/1800`. -/
theorem likelihood_twoCalls_zero : likelihood (fun _ : Unit => acSite 2) (fun _ => allHet)
    twoCalls 0 = 223 / 1800 := by
  simp only [likelihood, likelihoodWithPriors, Finset.univ_unique, Finset.prod_singleton,
    Fin.sum_univ_three, Fin.prod_univ_two, Fintype.sum_bool, hwGenotype_allHet_zero,
    hwGenotype_allHet_one, hwGenotype_allHet_two]
  norm_num [twoCalls, callProb, alleleCallProb, errorProb, acSite, phredErrorProb_ten]

/-- With two reads the sequence-only likelihood depends on `α`: `L(1/2) = 41/240`. -/
theorem likelihood_twoCalls_half : likelihood (fun _ : Unit => acSite 2) (fun _ => allHet)
    twoCalls (1 / 2) = 41 / 240 := by
  simp only [likelihood, likelihoodWithPriors, Finset.univ_unique, Finset.prod_singleton,
    Fin.sum_univ_three, Fin.prod_univ_two, Fintype.sum_bool, hwGenotype_allHet_zero,
    hwGenotype_allHet_one, hwGenotype_allHet_two]
  norm_num [twoCalls, callProb, alleleCallProb, errorProb, acSite, phredErrorProb_ten]

example : likelihood (fun _ : Unit => acSite 2) (fun _ => allHet) twoCalls 0 ≠
    likelihood (fun _ : Unit => acSite 2) (fun _ => allHet) twoCalls (1 / 2) := by
  rw [likelihood_twoCalls_zero, likelihood_twoCalls_half]
  norm_num

/-- The reflection `L(1 - α) = L(α)` on the two-read data. -/
example (α : ℝ) : likelihood (fun _ : Unit => acSite 2) (fun _ => allHet) twoCalls (1 - α) =
    likelihood (fun _ : Unit => acSite 2) (fun _ => allHet) twoCalls α :=
  likelihood_one_sub _ _ _ _

/-- One read at the `A/C` site, called `C`. -/
def oneCall : ∀ _ : Unit, Fin (acSite 1).depth → Fin 4 := fun _ => ![1]

/-- With one read every `α` has the same likelihood, here `7/15`. -/
example (α : ℝ) : likelihood (fun _ : Unit => acSite 1) (fun _ => allHet) oneCall α = 7 / 15 := by
  rw [likelihood_eq_prod_of_depth_le_one _ _ _ (fun _ => le_rfl)]
  simp only [Finset.univ_unique, Finset.prod_singleton, Fin.sum_univ_three,
    Fintype.sum_bool, hwGenotype_allHet_zero, hwGenotype_allHet_one, hwGenotype_allHet_two]
  norm_num [oneCall, callProb, alleleCallProb, errorProb, acSite, phredErrorProb_ten]

/-- The masses of all two-base calls sum to one for every real `α`. -/
example (α : ℝ) : ∑ b : (∀ _ : Unit, Fin (acSite 2).depth → Fin 4),
    likelihood (fun _ : Unit => acSite 2) (fun _ => allHet) b α = 1 :=
  sum_likelihood _ _ _

/-! ### Array genotypes break the reflection

The target's array genotype is `AA` with no genotyping error, the contaminant has the
Hardy–Weinberg law of allele frequencies `1/2`, and the one read is called `C`. Then
`L(α) = (1 - α)/30 + 7α/15`, so `L(0) ≠ L(1)`. -/

theorem arrayLikelihood_oneCall (α : ℝ) :
    arrayLikelihood (fun _ : Unit => acSite 1) (fun _ => allHet) (fun _ => 0) (fun _ => 0)
      oneCall α = (1 - α) / 30 + 7 * α / 15 := by
  simp only [arrayLikelihood, likelihoodWithPriors, arrayGenotypeProb, Finset.univ_unique,
    Finset.prod_singleton, Fin.sum_univ_three, Fintype.sum_bool,
    hwGenotype_allHet_zero, hwGenotype_allHet_one, hwGenotype_allHet_two]
  norm_num [oneCall, callProb, alleleCallProb, errorProb, acSite, phredErrorProb_ten,
    genotypeGivenArray, genotypingErrorProb]
  ring

example : arrayLikelihood (fun _ : Unit => acSite 1) (fun _ => allHet) (fun _ => 0) (fun _ => 0)
      oneCall (1 - 0) ≠
    arrayLikelihood (fun _ : Unit => acSite 1) (fun _ => allHet) (fun _ => 0) (fun _ => 0)
      oneCall 0 := by
  rw [arrayLikelihood_oneCall, arrayLikelihood_oneCall]
  norm_num

/-- The array-genotype prior: with genotyping-error probability `r`, an array genotype `AA` gives
the true genotypes `AA, AC, CC` the probabilities `1 - r, r/2, r/2`. -/
example (r : ℝ) : arrayGenotypeProb 0 r 0 = 1 - r ∧ arrayGenotypeProb 0 r 1 = r / 2 ∧
    arrayGenotypeProb 0 r 2 = r / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [arrayGenotypeProb, genotypeGivenArray, genotypingErrorProb] <;> ring

end DomainsTest.Biology.StatisticalGenetics.ReadMixtureContamination
