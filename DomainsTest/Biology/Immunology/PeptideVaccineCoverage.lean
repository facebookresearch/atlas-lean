/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Immunology.PeptideVaccineCoverage
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Tests for the population coverage of a peptide set at a hit threshold.

A population with two HLA haplotypes over four alleles, and three candidate peptides:

| haplotype | frequency | alleles |
|---|---|---|
| `0` | 3/5 | `A` (`0`), `C` (`2`) |
| `1` | 2/5 | `B` (`1`), `C` (`2`) |

| peptide | displayed by |
|---|---|
| `0` | `A`, `B` |
| `1` | `C` |
| `2` | `B` |

* the alleles carried: the heterozygous genotype `(0, 1)` carries three distinct alleles, as both
  of its haplotypes carry `C`, and each homozygous genotype two;
* ground truth from the definition, for the peptide set `V = {0, 1}`: the homozygous genotypes have
  two hits each and the heterozygous ones three, so the curve is `1` up to the threshold `2`,
  `2 * (3/5) * (2/5) = 12/25` at `3` — the two ordered pairs of a heterozygous genotype, as random
  mating weights it — and `0` beyond;
* the theorems on these data: the curve starts at `1`, is non-increasing, and lies in `[0, 1]`;
* monotonicity in the peptide set: adding the peptide `2`, displayed by `B`, raises the coverage at
  the threshold `3` from `12/25` to `16/25`;
* a model that displays nothing covers no one above the threshold `0`. -/

open Domains.Biology.Immunology.PeptideVaccineCoverage

namespace DomainsTest.Biology.Immunology.PeptideVaccineCoverage

/-- The alleles of the two haplotypes: `{A, C}` and `{B, C}`. -/
def alleles : Fin 2 → Finset (Fin 4) := ![{0, 2}, {1, 2}]

/-- The immunogenicity model: peptide `0` is displayed by `A` and `B`, peptide `1` by `C`, and
peptide `2` by `B`. -/
def displays : Fin 3 → Fin 4 → Bool := ![![true, true, false, false], ![false, false, true, false],
  ![false, true, false, false]]

/-- The haplotype frequencies. -/
noncomputable def freq : Fin 2 → ℝ := ![3 / 5, 2 / 5]

/-- The candidate peptide set of the vaccine. -/
def V : Finset (Fin 3) := {0, 1}

/-- The peptide set augmented with the peptide `2`. -/
def W : Finset (Fin 3) := {0, 1, 2}

theorem freq_nonneg (h : Fin 2) : 0 ≤ freq h := by fin_cases h <;> norm_num [freq]

theorem sum_freq : ∑ h, freq h = 1 := by norm_num [freq, Fin.sum_univ_two]

/-! ### The alleles a genotype carries -/

/-- The heterozygous genotype carries three distinct alleles: both haplotypes carry `C`. -/
example : alleles 0 ∪ alleles 1 = {0, 1, 2} := by decide

/-- A homozygous genotype carries the two alleles of its haplotype. -/
example : alleles 0 ∪ alleles 0 = {0, 2} := by decide

/-! ### Ground truth from the definition -/

/-- With the peptide set `V`, a homozygous genotype has two hits and a heterozygous one three. -/
theorem hits_V (g : Fin 2 × Fin 2) :
    ((V ×ˢ (alleles g.1 ∪ alleles g.2)).filter fun pa => displays pa.1 pa.2).card =
      if g.1 = g.2 then 2 else 3 := by
  decide +revert

/-- With the augmented set `W`, the genotype `(1, 1)` gains the hit `(2, B)` and the heterozygous
genotypes gain it too. -/
theorem hits_W (g : Fin 2 × Fin 2) :
    ((W ×ˢ (alleles g.1 ∪ alleles g.2)).filter fun pa => displays pa.1 pa.2).card =
      if g = (0, 0) then 2 else if g = (1, 1) then 3 else 4 := by
  decide +revert

/-- Every individual has at least two hits from `V`. -/
example : populationCoverage alleles displays freq V 2 = 1 := by
  simp only [populationCoverage, hits_V, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num [freq]

/-- Only the heterozygous genotypes reach three hits from `V`, and random mating gives them
`2 * (3/5) * (2/5)`. -/
example : populationCoverage alleles displays freq V 3 = 12 / 25 := by
  simp only [populationCoverage, hits_V, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num [freq]

/-- No one has four hits from `V`. -/
example : populationCoverage alleles displays freq V 4 = 0 := by
  simp only [populationCoverage, hits_V, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num [freq]

/-! ### The theorems on these data -/

/-- The curve starts at `1`. -/
example : populationCoverage alleles displays freq V 0 = 1 := populationCoverage_zero sum_freq

example : Antitone (populationCoverage alleles displays freq V) :=
  populationCoverage_antitone freq_nonneg

example (n : ℕ) : 0 ≤ populationCoverage alleles displays freq V n :=
  populationCoverage_nonneg freq_nonneg

example (n : ℕ) : populationCoverage alleles displays freq V n ≤ 1 :=
  populationCoverage_le_one freq_nonneg sum_freq

/-! ### Monotonicity in the peptide set -/

/-- The augmented set covers `16/25` at the threshold `3`: the heterozygous genotypes, as before,
and now the homozygous genotype of the haplotype carrying `B`. -/
example : populationCoverage alleles displays freq W 3 = 16 / 25 := by
  simp only [populationCoverage, hits_W, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num [freq]

/-- Adding the peptide `2` raises the coverage at the threshold `3`, as `populationCoverage_mono`
allows. -/
example :
    populationCoverage alleles displays freq V 3 ≤ populationCoverage alleles displays freq W 3 :=
  populationCoverage_mono freq_nonneg (by decide)

/-! ### A model that displays nothing -/

/-- With no peptide displayed by any allele, no one is covered above the threshold `0`. -/
example (n : ℕ) (hn : 0 < n) :
    populationCoverage alleles (fun _ _ => false) freq V n = 0 := by
  simp [populationCoverage, hn.ne']

end DomainsTest.Biology.Immunology.PeptideVaccineCoverage
