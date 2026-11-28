/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.BigOperators

/-!
# Population coverage of a peptide set at a hit threshold

A peptide vaccine is scored by how many of its peptides a random individual of a population is
predicted to display (Liu, Carter and Gifford, 2021). An individual is a diploid HLA genotype,
a pair of haplotypes drawn from a population with known haplotype frequencies, and carries the
alleles of both of its haplotypes, so that a locus homozygous in the pair contributes one allele
and a heterozygous locus two. A pair (peptide, HLA allele) is a **hit** for a genotype `g` when
`g` carries the allele and the peptide is predicted to be displayed by it, and `H V g` is the
number of distinct hits of a candidate peptide set `V`. For a threshold `n`, the **population
coverage** of `V` is

  `P V n = ∑ g, Pr g * 1{n ≤ H V g}`,

the probability that an individual has at least `n` hits. The insufficient-coverage curve of the
source is its complement one step up, `1 - P V (n + 1)`, the fraction of individuals with at most
`n` hits.

## Conventions

* An individual is a pair of haplotypes `g : Haplotype × Haplotype`, drawn independently from the
  haplotype frequencies `freq`, so that `Pr g = freq g.1 * freq g.2`. Summing over ordered pairs
  gives each genotype the probability random mating gives it: `freq i * freq i` for the homozygous
  genotype of `i`, and `2 * (freq i * freq j)` for the genotype of `i ≠ j`, whose two ordered pairs
  have the same hits.
* `alleles h` is the finite set of HLA alleles of the haplotype `h`, one per locus of the class
  modelled. The genotype `g` carries `alleles g.1 ∪ alleles g.2`, a union, so an allele homozygous
  in `g` is carried once and offers one hit per peptide.
* `displays p a` is the prediction that the allele `a` displays the peptide `p` immunogenically.
  The hits of `g` are the pairs of `V ×ˢ (alleles g.1 ∪ alleles g.2)` it holds for, counted as
  distinct pairs: a peptide displayed by two of the carried alleles is two hits, as is an allele
  that displays two peptides of `V`.
* The definition asks nothing of `freq`; each result assumes what it uses, nonnegative frequencies
  or frequencies summing to `1`.
* The coverage is a prediction, conditional on the immunogenicity model `displays` and on the
  estimated haplotype frequencies, not an observed immune response.

## Main definition

* `populationCoverage alleles displays freq V n`: the fraction of the population predicted to have
  at least `n` distinct peptide–HLA hits from the peptide set `V`.

## Main results

* `populationCoverage_zero`: every individual has at least `0` hits, so the curve starts at `1`.
* `populationCoverage_antitone`: the curve is non-increasing in the threshold.
* `populationCoverage_mono`: it is monotone in the peptide set, so adding peptides to a vaccine
  never lowers its predicted coverage.
* `populationCoverage_nonneg` and `populationCoverage_le_one`: the curve is a probability.

## References

* G. Liu, B. Carter, D. K. Gifford, "Predicted cellular immunity population coverage gaps for
  SARS-CoV-2 subunit vaccines and their augmentation by compact peptide sets", *Cell Systems* 12
  (2021), 102–107, <https://doi.org/10.1016/j.cels.2020.11.010>: STAR Methods, "EvalVax subunit
  vaccine evaluation".
-/

@[expose] public section

namespace Domains.Biology.Immunology.PeptideVaccineCoverage

variable {Peptide Allele Haplotype : Type*} [DecidableEq Allele] [Fintype Haplotype]
  {alleles : Haplotype → Finset Allele} {displays : Peptide → Allele → Bool} {freq : Haplotype → ℝ}
  {V W : Finset Peptide} {n : ℕ}

/-- The **population coverage** of a candidate peptide set `V` at the hit threshold `n`
(Liu, Carter and Gifford, 2021): the probability

  `P V n = ∑ g, Pr g * 1{n ≤ H V g}`

that an individual of the population has at least `n` distinct peptide–HLA hits from `V`.

An individual is a diploid HLA genotype `g : Haplotype × Haplotype`, a pair of haplotypes drawn
from the haplotype frequencies `freq`, so that `Pr g = freq g.1 * freq g.2`; summing over ordered
pairs gives a heterozygous genotype twice the product of its haplotype frequencies and a
homozygous one the square of its own, as random mating does. The genotype carries the alleles
`alleles g.1 ∪ alleles g.2` of its two haplotypes, a homozygous allele once, and its hits
`H V g` are the distinct pairs `(p, a)` of a peptide `p ∈ V` and a carried allele `a` with
`displays p a`, the prediction that `a` displays `p` immunogenically.

The curve starts at `P V 0 = 1` (`populationCoverage_zero`) and is non-increasing in `n`
(`populationCoverage_antitone`), and `1 - P V (n + 1)` is the source's insufficient coverage, the
fraction of individuals with at most `n` hits. It is monotone in the peptide set
(`populationCoverage_mono`): augmenting a vaccine never lowers its predicted coverage. The value
is a prediction conditional on `displays` and on the estimated frequencies `freq`. -/
noncomputable def populationCoverage (alleles : Haplotype → Finset Allele)
    (displays : Peptide → Allele → Bool) (freq : Haplotype → ℝ) (V : Finset Peptide) (n : ℕ) :
    ℝ :=
  ∑ g : Haplotype × Haplotype with
    n ≤ ((V ×ˢ (alleles g.1 ∪ alleles g.2)).filter fun pa => displays pa.1 pa.2).card,
    freq g.1 * freq g.2

/-- Every individual has at least `0` hits, so a coverage curve of frequencies summing to `1`
starts at `1`. -/
theorem populationCoverage_zero (hfreq : ∑ h, freq h = 1) :
    populationCoverage alleles displays freq V 0 = 1 := by
  rw [populationCoverage, Finset.filter_true_of_mem fun g _ => Nat.zero_le _,
    Fintype.sum_prod_type, ← Fintype.sum_mul_sum, hfreq, mul_one]

/-- The individuals with at least `m` hits are among those with at least `n` hits when `n ≤ m`, so
a coverage curve of nonnegative frequencies is non-increasing in the threshold: a vaccine covers no
more of the population at a stricter threshold. -/
theorem populationCoverage_antitone (hfreq : ∀ h, 0 ≤ freq h) :
    Antitone (populationCoverage alleles displays freq V) := fun _ _ hnm =>
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.monotone_filter_right _ fun _ _ hg => le_trans hnm hg)
    fun g _ _ => mul_nonneg (hfreq g.1) (hfreq g.2)

/-- Extra peptides can only add hits, so a coverage curve of nonnegative frequencies is monotone in
the peptide set: augmenting a vaccine never lowers its predicted coverage at any threshold. -/
theorem populationCoverage_mono (hfreq : ∀ h, 0 ≤ freq h) (hVW : V ⊆ W) :
    populationCoverage alleles displays freq V n ≤ populationCoverage alleles displays freq W n :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.monotone_filter_right _ fun _ _ hg => le_trans hg (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.product_subset_product hVW Finset.Subset.rfl))))
    fun g _ _ => mul_nonneg (hfreq g.1) (hfreq g.2)

/-- A coverage curve of nonnegative frequencies is nonnegative. -/
theorem populationCoverage_nonneg (hfreq : ∀ h, 0 ≤ freq h) :
    0 ≤ populationCoverage alleles displays freq V n :=
  Finset.sum_nonneg fun g _ => mul_nonneg (hfreq g.1) (hfreq g.2)

/-- A coverage curve of nonnegative frequencies summing to `1` is at most `1`: it is the
probability of a set of individuals. -/
theorem populationCoverage_le_one (hfreq₀ : ∀ h, 0 ≤ freq h) (hfreq : ∑ h, freq h = 1) :
    populationCoverage alleles displays freq V n ≤ 1 :=
  (populationCoverage_antitone hfreq₀ (Nat.zero_le n)).trans_eq (populationCoverage_zero hfreq)

end Domains.Biology.Immunology.PeptideVaccineCoverage
