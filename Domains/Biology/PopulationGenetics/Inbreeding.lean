/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Ring

/-!
# Genotype frequencies under inbreeding

At a single diploid locus, two copies in an individual are identical by descent with probability
`F`, in which case they carry one shared draw from the base allele frequencies `p`. With
probability `1 - F` they carry two independent draws, as in the Hardy–Weinberg model. This assumes
no mutation or differential viability or fertility between the base population and the draw.

## Reference

* J. Felsenstein, *Theoretical Evolutionary Genetics*, December 2019, §V.2, equations (V-2) and
  (V-3), and §V.14, equations (V-46) and (V-47). <https://felsenst.github.io/pgbook/pgbook.pdf>
-/

@[expose] public section

open scoped BigOperators

namespace Domains.Biology.PopulationGenetics.Inbreeding

variable {ι : Type*} [DecidableEq ι]

/-- The mass of an ordered genotype `(i, j)` is a mixture of the shared-allele law (weight `F`)
and the independent-alleles law (weight `1 - F`). For this to be a probability model, the allele
frequencies `p` must be nonnegative and sum to `1`, and `F` must belong to `[0, 1]`. -/
noncomputable def orderedGenotypeFrequency (p : ι → ℝ) (F : ℝ) (i j : ι) : ℝ :=
  F * (if i = j then p i else 0) + (1 - F) * (p i * p j)

/-- **Genotype frequencies of an inbred individual.** The mixture of shared and independent
allele draws gives a nonnegative, normalized genotype law. A homozygote has mass
`F * p i + (1 - F) * p i ^ 2`. A heterozygote has mass `2 * (1 - F) * p i * p j` after
summing both orders. A uniformly chosen copy has allele frequencies `p`; the total mass of
unequal pairs is `(1 - F) * (1 - ∑ i, p i ^ 2)`. If two distinct alleles exhaust the base
frequencies, their three genotype masses reduce to `x ^ 2 + F * x * y`, `2 * x * y * (1 - F)`
and `y ^ 2 + F * x * y`, where `x` is the first allele's frequency and `y = 1 - x`. -/
theorem genotypeFrequencies [Fintype ι] (p : ι → ℝ) (F : ℝ)
    (hp₀ : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) (hF₀ : 0 ≤ F) (hF₁ : F ≤ 1) :
    let g := orderedGenotypeFrequency p F
    (∀ i j, 0 ≤ g i j) ∧
    (∑ i, ∑ j, g i j) = 1 ∧
    (∀ i, g i i = F * p i + (1 - F) * p i ^ 2) ∧
    (∀ i j, i ≠ j → g i j + g j i = 2 * (1 - F) * p i * p j) ∧
    (∀ i, ((∑ j, g i j) + (∑ j, g j i)) / 2 = p i) ∧
    (∑ i, ∑ j ∈ Finset.univ.erase i, g i j) = (1 - F) * (1 - ∑ i, p i ^ 2) ∧
    (∀ i j, i ≠ j → p i + p j = 1 →
      let x := p i
      let y := 1 - x
      g i i = x ^ 2 + F * x * y ∧
      g i j + g j i = 2 * x * y * (1 - F) ∧
      g j j = y ^ 2 + F * x * y) := by
  let g := orderedGenotypeFrequency p F
  have hnonneg (i j : ι) : 0 ≤ g i j :=
    add_nonneg (mul_nonneg hF₀ (by by_cases hij : i = j <;> simp [hij, hp₀]))
      (mul_nonneg (sub_nonneg.mpr hF₁) (mul_nonneg (hp₀ i) (hp₀ j)))
  have hrow (i : ι) : ∑ j, g i j = p i := by
    simp only [g, orderedGenotypeFrequency, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hd : (∑ j : ι, if i = j then p i else 0) = p i := by simp
    rw [hd, hp]
    ring
  have hsymm (i j : ι) : g i j = g j i := by
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [g, orderedGenotypeFrequency, ite_eq_right hij, ite_eq_right (Ne.symm hij),
        mul_comm (p i) (p j)]
  have hhom (i : ι) : g i i = F * p i + (1 - F) * p i ^ 2 := by
    simp [g, orderedGenotypeFrequency, pow_two]
  have hhet (i j : ι) (hij : i ≠ j) : g i j + g j i = 2 * (1 - F) * p i * p j := by
    rw [hsymm j i]
    simp only [g, orderedGenotypeFrequency, ite_eq_right hij, mul_zero, zero_add]
    ring
  have htotal : ∑ i, ∑ j, g i j = 1 := by
    simp only [hrow, hp]
  refine ⟨hnonneg, htotal, hhom, hhet, ?_, ?_, ?_⟩
  · intro i
    have hcol : ∑ j, g j i = p i := by
      simpa only [hsymm _ i] using hrow i
    rw [hrow, hcol]
    ring
  · change (∑ i, ∑ j ∈ Finset.univ.erase i, g i j) = _
    have hoff (i : ι) : ∑ j ∈ Finset.univ.erase i, g i j = p i - g i i := by
      apply eq_sub_of_add_eq
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i), hrow]
    simp only [hoff, hhom, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp]
    ring
  · intro i j hij hpij
    have hj : p j = 1 - p i := eq_sub_of_add_eq (by simpa only [add_comm] using hpij)
    change g i i = p i ^ 2 + F * p i * (1 - p i) ∧
      g i j + g j i = 2 * p i * (1 - p i) * (1 - F) ∧
      g j j = (1 - p i) ^ 2 + F * p i * (1 - p i)
    rw [hhom i, hhet i j hij, hhom j, hj]
    exact ⟨by ring, by ring, by ring⟩

end Domains.Biology.PopulationGenetics.Inbreeding
