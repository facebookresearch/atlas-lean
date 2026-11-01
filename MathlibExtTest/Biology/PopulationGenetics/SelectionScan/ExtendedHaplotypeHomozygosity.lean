/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.SelectionScan.ExtendedHaplotypeHomozygosity
public import Mathlib.Tactic.NormNum

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory
open MathlibExt.Biology.PopulationGenetics.SelectionScan

namespace MathlibExtTest.Biology.PopulationGenetics.SelectionScan.ExtendedHaplotypeHomozygosity

/-! ### A concrete four-haplotype sample

Four haplotypes over the alleles `Bool`. All four carry `false` at the core-adjacent site
`0`; at site `1` only haplotype `3` carries `true`; all later sites are `false`. So the
windows of radius `1` are all equal, and the windows of radius `2` split the sample into
`{0, 1, 2}` and `{3}`. -/

/-- The test sample: `hap i k` is the allele of haplotype `i` at the site `k` steps from the
core. -/
def hap : Fin 4 → ℕ → Bool := fun i k => decide (k = 1 ∧ i = 3)

example : concordantPairs hap Finset.univ 1 = 12 := by decide

example : concordantPairs hap Finset.univ 2 = 6 := by decide

/-- Radius `1`: every pair of the four haplotypes still shares its window, so `EHH = 1`. -/
example : ehh hap Finset.univ 1 = 1 := by
  have h : concordantPairs hap Finset.univ 1 = 12 := by decide
  rw [ehh, h]
  norm_num

/-- Radius `2`: the sample splits into a class of three and a singleton, so `EHH = 1/2`. -/
example : ehh hap Finset.univ 2 = 1 / 2 := by
  have h : concordantPairs hap Finset.univ 2 = 6 := by decide
  rw [ehh, h]
  norm_num

/-- Boundary: at radius `0` the EHH of a sample of at least two haplotypes is `1`. -/
example : ehh hap Finset.univ 0 = 1 :=
  ehh_zero_window hap (by decide)

/-- Monotonicity on the concrete sample. -/
example : ehh hap Finset.univ 2 ≤ ehh hap Finset.univ 1 :=
  ehh_antitone hap Finset.univ (by norm_num)

/-- The homozygosity form agrees with the pair-counting definition. -/
example : ehh hap Finset.univ 2
    = (∑ t ∈ Finset.univ.image (window hap 2),
        ((Finset.univ.filter fun i => window hap 2 i = t).card : ℝ) *
          (((Finset.univ.filter fun i => window hap 2 i = t).card : ℝ) - 1)) /
      (((Finset.univ : Finset (Fin 4)).card : ℝ) *
        (((Finset.univ : Finset (Fin 4)).card : ℝ) - 1)) :=
  ehh_eq_sum_counts hap Finset.univ 2

/-! ### Junk values outside the domain `2 ≤ #C` -/

example : ehh hap ∅ 2 = 0 := ehh_eq_zero_of_card_le_one hap (by simp) 2

example : ehh hap {0} 2 = 0 := ehh_eq_zero_of_card_le_one hap (by decide) 2

/-! ### Relative EHH

`C = {0, 1}` is a perfectly homozygous pair at radius `2`; in `D = {0, 1, 3}` only the pair
`(0, 1)` shares its window, so `EHH(D) = 1/3` and the relative EHH is `3`. -/

example : ehh hap {0, 1} 2 = 1 := by
  have h : concordantPairs hap {0, 1} 2 = 2 := by decide
  rw [ehh, h]
  norm_num [show ({0, 1} : Finset (Fin 4)).card = 2 by decide]

example : ehh hap {0, 1, 3} 2 = 1 / 3 := by
  have h : concordantPairs hap {0, 1, 3} 2 = 2 := by decide
  rw [ehh, h]
  norm_num [show ({0, 1, 3} : Finset (Fin 4)).card = 3 by decide]

example : rehh hap {0, 1} {0, 1, 3} 2 = 3 := by
  have hC : ehh hap {0, 1} 2 = 1 := by
    have h : concordantPairs hap {0, 1} 2 = 2 := by decide
    rw [ehh, h]
    norm_num [show ({0, 1} : Finset (Fin 4)).card = 2 by decide]
  have hD : ehh hap {0, 1, 3} 2 = 1 / 3 := by
    have h : concordantPairs hap {0, 1, 3} 2 = 2 := by decide
    rw [ehh, h]
    norm_num [show ({0, 1, 3} : Finset (Fin 4)).card = 3 by decide]
  rw [rehh, hC, hD]
  norm_num

example : 1 < rehh hap {0, 1} {0, 1, 3} 2 := by
  have hD : ehh hap {0, 1, 3} 2 = 1 / 3 := by
    have h : concordantPairs hap {0, 1, 3} 2 = 2 := by decide
    rw [ehh, h]
    norm_num [show ({0, 1, 3} : Finset (Fin 4)).card = 3 by decide]
  have hC : ehh hap {0, 1} 2 = 1 := by
    have h : concordantPairs hap {0, 1} 2 = 2 := by decide
    rw [ehh, h]
    norm_num [show ({0, 1} : Finset (Fin 4)).card = 2 by decide]
  rw [one_lt_rehh_iff hap {0, 1} {0, 1, 3} (by rw [hD]; norm_num), hC, hD]
  norm_num

/-! ### The neutral no-recombination probability -/

/-- At the core itself no recombination can separate the pair. -/
example (ρ t : ℝ) : pairNoRecomb ρ 0 t = 1 := by
  simp [pairNoRecomb]

/-- With `ρ d = 1` the average over an exponential pair coalescence time is `1/2`. -/
example : ∫ t, pairNoRecomb 1 1 t ∂(expMeasure 1) = 1 / 2 := by
  rw [integral_pairNoRecomb (by norm_num) (by norm_num)]
  norm_num

/-- The bound is strictly below `1` at a positive distance, and decays in the distance. -/
example : pairNoRecomb 1 2 1 ≤ pairNoRecomb 1 1 1 :=
  pairNoRecomb_antitone (by norm_num) (by norm_num) (by norm_num)

#print axioms ehh_antitone
#print axioms ehh_eq_sum_counts
#print axioms integral_pairNoRecomb

end MathlibExtTest.Biology.PopulationGenetics.SelectionScan.ExtendedHaplotypeHomozygosity
