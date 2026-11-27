/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.FounderSampling
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.FounderSampling
open scoped BigOperators

namespace MathlibExtTest.Biology.PopulationGenetics.FounderSampling

/-! ### Three-allele examples

`p₃ = (1/2, 1/2, 0)` and `q₃ = (2/3, 1/6, 1/6)` have the same heterozygosity
`1 - ∑ pᵢ² = 1/2`, but a founder sample of `3` gene copies retains different
expected allelic richness: `7/4` versus `65/36`. Heterozygosity alone does not
determine retained richness. -/

/-- Frequencies `(1/2, 1/2, 0)` on three alleles. -/
noncomputable def p₃ : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

/-- Frequencies `(2/3, 1/6, 1/6)` on three alleles. -/
noncomputable def q₃ : Fin 3 → ℝ := ![2 / 3, 1 / 6, 1 / 6]

theorem sum_p₃ : ∑ a, p₃ a = 1 := by
  norm_num [p₃, Fin.sum_univ_three]

theorem sum_q₃ : ∑ a, q₃ a = 1 := by
  norm_num [q₃, Fin.sum_univ_three]

example : expectedRichness p₃ 3 = 7 / 4 := by
  rw [expectedRichness_eq p₃ sum_p₃ 3]
  norm_num [p₃, Fin.sum_univ_three]

example : expectedRichness q₃ 3 = 65 / 36 := by
  rw [expectedRichness_eq q₃ sum_q₃ 3]
  norm_num [q₃, Fin.sum_univ_three]

/-- Allele `0` at frequency `1/2` is lost from `3` founder copies with
probability `(1/2)³ = 1/8`; the absent allele `2` is lost with probability `1`. -/
example : probAbsent p₃ 3 0 = 1 / 8 ∧ probAbsent p₃ 3 2 = 1 := by
  constructor
  · rw [probAbsent_eq p₃ sum_p₃ 3 0]
    norm_num [p₃]
  · rw [probAbsent_eq p₃ sum_p₃ 3 2]
    norm_num [p₃]

example : expectedRichness p₃ 0 = 0 := expectedRichness_zero p₃

example : expectedRichness p₃ 2 ≤ expectedRichness p₃ 3 := by
  have hp : ∀ i, 0 ≤ p₃ i := by
    intro i
    fin_cases i <;> norm_num [p₃]
  exact expectedRichness_mono p₃ hp sum_p₃ 2

end MathlibExtTest.Biology.PopulationGenetics.FounderSampling
