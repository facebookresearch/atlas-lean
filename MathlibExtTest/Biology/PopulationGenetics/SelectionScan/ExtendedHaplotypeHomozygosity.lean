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

`C = {0, 1}` and `D = {2, 3, 4}` are disjoint complementary carrier groups in a
five-haplotype sample: `C` carries one core allele, `D` carries the other. In `C` the pair
shares its window, so the core-labelled EHH is `1`; in `D` only the pair `(2, 3)` shares its
window, so the core-labelled EHH is `1/3` and the relative EHH is `3`. -/

/-- Five-haplotype sample for relative EHH: only haplotype `4` differs at site `1`. -/
def hap5 : Fin 5 → ℕ → Bool := fun i k => decide (k = 1 ∧ i = 4)

/-- Core alleles for the five-haplotype sample: `{0, 1}` carry one allele, `{2, 3, 4}`
carry the other. -/
def core5 : Fin 5 → Bool := fun i => decide (2 ≤ i)

example : ehhCore core5 hap5 {0, 1} 2 = 1 := by
  have h : concordantPairsCore core5 hap5 {0, 1} 2 = 2 := by decide
  rw [ehhCore, h]
  norm_num [show ({0, 1} : Finset (Fin 5)).card = 2 by decide]

example : ehhCore core5 hap5 {2, 3, 4} 2 = 1 / 3 := by
  have h : concordantPairsCore core5 hap5 {2, 3, 4} 2 = 2 := by decide
  rw [ehhCore, h]
  norm_num [show ({2, 3, 4} : Finset (Fin 5)).card = 3 by decide]

example : rehh core5 hap5 {0, 1} {2, 3, 4} 2 = 3 := by
  have hC : ehhCore core5 hap5 {0, 1} 2 = 1 := by
    have h : concordantPairsCore core5 hap5 {0, 1} 2 = 2 := by decide
    rw [ehhCore, h]
    norm_num [show ({0, 1} : Finset (Fin 5)).card = 2 by decide]
  have hD : ehhCore core5 hap5 {2, 3, 4} 2 = 1 / 3 := by
    have h : concordantPairsCore core5 hap5 {2, 3, 4} 2 = 2 := by decide
    rw [ehhCore, h]
    norm_num [show ({2, 3, 4} : Finset (Fin 5)).card = 3 by decide]
  rw [rehh, hC, hD]
  norm_num

example : 1 < rehh core5 hap5 {0, 1} {2, 3, 4} 2 := by
  have hD : ehhCore core5 hap5 {2, 3, 4} 2 = 1 / 3 := by
    have h : concordantPairsCore core5 hap5 {2, 3, 4} 2 = 2 := by decide
    rw [ehhCore, h]
    norm_num [show ({2, 3, 4} : Finset (Fin 5)).card = 3 by decide]
  have hC : ehhCore core5 hap5 {0, 1} 2 = 1 := by
    have h : concordantPairsCore core5 hap5 {0, 1} 2 = 2 := by decide
    rw [ehhCore, h]
    norm_num [show ({0, 1} : Finset (Fin 5)).card = 2 by decide]
  rw [one_lt_rehh_iff core5 hap5 {0, 1} {2, 3, 4} (by rw [hD]; norm_num), hC, hD]
  norm_num

/-- Cross-core pairs are never concordant: two haplotypes with identical (constant) windows
but different core alleles have core-labelled EHH `0`, where plain `ehh` would give `1`. -/
example : ehhCore (fun i : Fin 4 => decide (i = 0)) (fun _ _ => false)
    ({0, 1} : Finset (Fin 4)) 2 = 0 := by
  have h : concordantPairsCore (fun i : Fin 4 => decide (i = 0)) (fun _ _ => false)
      ({0, 1} : Finset (Fin 4)) 2 = 0 := by decide
  rw [ehhCore, h]
  norm_num [show ({0, 1} : Finset (Fin 4)).card = 2 by decide]

/-- With a constant core allele, core-labelled EHH agrees with plain EHH on the same sample. -/
example : ehhCore (fun _ : Fin 4 => false) (fun _ _ => false)
    ({0, 1} : Finset (Fin 4)) 2 = 1 := by
  have h : concordantPairsCore (fun _ : Fin 4 => false) (fun _ _ => false)
      ({0, 1} : Finset (Fin 4)) 2 = 2 := by decide
  rw [ehhCore, h]
  norm_num [show ({0, 1} : Finset (Fin 4)).card = 2 by decide]

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
