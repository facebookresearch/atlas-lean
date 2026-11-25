/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Inbreeding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Domains.Biology.PopulationGenetics.Inbreeding

/-! A full-support triallelic distribution `(1/2, 1/3, 1/6)` and an asymmetric biallelic
restriction `(1/3, 2/3)` separate the diagonal and independent contributions. -/

private noncomputable def triallelic (a : Fin 3) : ℝ :=
  if a = 0 then 1 / 2 else if a = 1 then 1 / 3 else 1 / 6

private lemma triallelic_nonneg (a : Fin 3) : 0 ≤ triallelic a := by
  fin_cases a <;> norm_num [triallelic]

private lemma sum_triallelic : ∑ a, triallelic a = 1 := by
  norm_num [Fin.sum_univ_succ, triallelic]

-- The shared copy and independent draws both contribute on the diagonal. Off the diagonal,
-- each ordered pair has only the independent contribution, and an unordered pair takes both.
example : orderedGenotypeFrequency triallelic (1 / 4) 0 0 = 5 / 16 ∧
    orderedGenotypeFrequency triallelic (1 / 4) 0 1 = 1 / 8 ∧
    orderedGenotypeFrequency triallelic (1 / 4) 1 0 = 1 / 8 := by
  norm_num [orderedGenotypeFrequency, triallelic]

example : (∑ i, ∑ j ∈ Finset.univ.erase i, orderedGenotypeFrequency triallelic (1 / 4) i j) =
    11 / 24 := by
  have h := (genotypeFrequencies triallelic (1 / 4) triallelic_nonneg sum_triallelic
    (by norm_num) (by norm_num)).2.2.2.2.2.1
  rw [h]
  norm_num [Fin.sum_univ_succ, triallelic]

example : ((∑ j, orderedGenotypeFrequency triallelic (1 / 4) 2 j) +
    (∑ j, orderedGenotypeFrequency triallelic (1 / 4) j 2)) / 2 = 1 / 6 := by
  have h := (genotypeFrequencies triallelic (1 / 4) triallelic_nonneg sum_triallelic
    (by norm_num) (by norm_num)).2.2.2.2.1 2
  simpa [triallelic] using h

-- At `F = 0` equal alleles can occur without identity by descent. At `F = 1`, only the
-- shared-copy term remains, so no heterozygote can occur.
example : orderedGenotypeFrequency triallelic 0 0 0 = 1 / 4 ∧
    orderedGenotypeFrequency triallelic 0 0 2 = 1 / 12 ∧
    orderedGenotypeFrequency triallelic 1 0 0 = 1 / 2 ∧
    orderedGenotypeFrequency triallelic 1 0 2 = 0 := by
  norm_num [orderedGenotypeFrequency, triallelic]

private noncomputable def biallelic (a : Fin 3) : ℝ :=
  if a = 0 then 1 / 3 else if a = 1 then 2 / 3 else 0

-- Two alleles exhaust the mass, even when the type includes a third, absent allele.
example : orderedGenotypeFrequency biallelic (1 / 2) 0 0 = 2 / 9 ∧
    orderedGenotypeFrequency biallelic (1 / 2) 0 1 +
      orderedGenotypeFrequency biallelic (1 / 2) 1 0 = 2 / 9 ∧
    orderedGenotypeFrequency biallelic (1 / 2) 1 1 = 5 / 9 := by
  have hnonneg (a : Fin 3) : 0 ≤ biallelic a := by
    fin_cases a <;> norm_num [biallelic]
  have hsum : ∑ a, biallelic a = 1 := by
    norm_num [Fin.sum_univ_succ, biallelic]
  have h := (genotypeFrequencies biallelic (1 / 2) hnonneg hsum (by norm_num) (by norm_num))
  have htwo := h.2.2.2.2.2.2 0 1 (by decide) (by norm_num [biallelic])
  norm_num [biallelic] at htwo
  exact htwo
