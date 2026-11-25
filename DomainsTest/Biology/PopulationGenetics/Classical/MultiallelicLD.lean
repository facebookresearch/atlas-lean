/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Classical.MultiallelicLD
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.Classical.MultiallelicLD

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.MultiallelicLD

/-- A concrete `3 × 2` haplotype-frequency table, in units of `1/12`. -/
noncomputable def x32 : Fin 3 × Fin 2 → ℝ :=
  fun g => ![![1 / 12, 3 / 12], ![2 / 12, 1 / 12], ![4 / 12, 1 / 12]] g.1 g.2

theorem sum_x32 : ∑ g, x32 g = 1 := by
  norm_num [x32, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two]

/-- In this example `D 0 0 = 1/12 - (1/3) * (7/12) = -1/9`. -/
example : linkageDiseq x32 0 0 = -1 / 9 := by
  norm_num [linkageDiseq, x32, Fin.sum_univ_three, Fin.sum_univ_two]

/-- One named-operator recombination step at `r = 1/3` multiplies
`D 0 0 = -1/9` by `2/3`, giving `-2/27`. -/
example : linkageDiseq (recombine (1 / 3) x32) 0 0 = -2 / 27 := by
  rw [linkageDiseq_recombine _ _ sum_x32]
  norm_num [linkageDiseq, x32, Fin.sum_univ_three, Fin.sum_univ_two]

/-- The first-locus disequilibria sum to zero for the concrete table. -/
example : ∑ i, linkageDiseq x32 i 0 = 0 :=
  sum_linkageDiseq_fst x32 sum_x32 0

/-- A concrete biallelic haplotype-frequency table. -/
noncomputable def xBool : Bool × Bool → ℝ
  | (true, true) => 2 / 5
  | (true, false) => 1 / 10
  | (false, true) => 1 / 5
  | (false, false) => 3 / 10

theorem sum_xBool : ∑ g, xBool g = 1 := by
  norm_num [xBool, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The biallelic instance gives `D_AB = 1/10`. -/
example : linkageDiseq xBool true true = 1 / 10 := by
  rw [linkageDiseq_bool sum_xBool]
  norm_num [MathlibExt.Biology.PopulationGenetics.Linkage.linkageDiseq, xBool]

/-- One generation at `r = 1/2` moves the `AB` frequency to `7/20`. -/
example : recombine (1 / 2) xBool (true, true) = 7 / 20 := by
  have h := congrFun (recombine_bool (1 / 2) xBool) (true, true)
  rw [h]
  norm_num [MathlibExt.Biology.PopulationGenetics.Linkage.recombine,
    MathlibExt.Biology.PopulationGenetics.Linkage.alleleFreqFst,
    MathlibExt.Biology.PopulationGenetics.Linkage.alleleFreqSnd,
    xBool, Fintype.sum_bool]

end MathlibExtTest.Biology.PopulationGenetics.Classical.MultiallelicLD
