/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.FisherMultilocus
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for Fisher's decomposition over independent loci

Two biallelic loci on Falconer's scale: the multilocus components are the sums of the one-locus
closed forms; the frequency normalization is load-bearing for the mean.
-/

@[expose] public section

open MathlibExt.Biology.StatisticalGenetics.FisherDecomposition
open Domains.Biology.StatisticalGenetics.FisherMultilocus

namespace DomainsTest.Biology.StatisticalGenetics.FisherMultilocus

/-- Allele frequencies `1/2` at locus `0` and `1/4` at locus `1`. -/
noncomputable def q : Fin 2 → ℝ := ![1 / 2, 1 / 4]

/-- Frequencies at two biallelic loci. -/
noncomputable def pTwo : ∀ _ : Fin 2, Bool → ℝ := fun l => biallelicFreq (q l)

/-- Genotypic values: locus `0` additive (`a = 1`, `d = 0`), locus `1` dominant (`a = 1`,
`d = 1`). -/
noncomputable def GTwo : ∀ _ : Fin 2, Bool → Bool → ℝ := fun l => biallelicValue 1 ((l : ℕ) : ℝ)

theorem sum_pTwo : ∀ l, ∑ a, pTwo l a = 1 := by
  intro l
  simp only [pTwo, biallelicFreq, Fintype.sum_bool, ite_true, Bool.false_eq_true,
    ite_false]
  ring

theorem GTwo_symm : ∀ l i j, GTwo l i j = GTwo l j i := by
  intro l i j
  cases i <;> cases j <;> rfl

/-- `V_A = 2 (1/2)(1/2) 1 ^ 2 + 2 (1/4)(3/4) (1 + 1/2) ^ 2 = 1/2 + 27/32`. -/
example : multiAddVar pTwo GTwo = 1 / 2 + 27 / 32 := by
  rw [multiAddVar_eq_sum sum_pTwo]
  norm_num [Fin.sum_univ_two, pTwo, GTwo, addVar_biallelic, q]

/-- `V_D = 0 + (2 (1/4)(3/4)) ^ 2 = 9/64`. -/
example : multiDomVar pTwo GTwo = 9 / 64 := by
  rw [multiDomVar_eq_sum sum_pTwo]
  norm_num [Fin.sum_univ_two, pTwo, GTwo, domVar_biallelic, q]

/-- Full sibs: `V_A / 2 + V_D / 4`. -/
example : covFullSibsMulti pTwo GTwo = (1 / 2 + 27 / 32) / 2 + 9 / 64 / 4 := by
  rw [covFullSibsMulti_eq sum_pTwo GTwo_symm, multiAddVar_eq_sum sum_pTwo,
    multiDomVar_eq_sum sum_pTwo]
  norm_num [Fin.sum_univ_two, pTwo, GTwo, addVar_biallelic, domVar_biallelic, q]

/-- Without normalized frequencies the mean is not the sum of the one-locus means. -/
example : multiMean (A := fun _ : Fin 2 => Bool) (fun _ _ => 1) (fun _ _ _ => 1) ≠
    ∑ _ : Fin 2, meanValue (fun _ : Bool => (1 : ℝ)) (fun _ _ => 1) := by
  norm_num [multiMean, genoFreq, totalValue, meanValue, Fin.sum_univ_two,
    Fintype.sum_bool, Fintype.card_pi]

end DomainsTest.Biology.StatisticalGenetics.FisherMultilocus
