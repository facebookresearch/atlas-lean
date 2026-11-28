/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Omics.AlleleSpecificReporter

/-! # Regressions for the negative-binomial test of allele-specific reporter activity -/

set_option autoImplicit false

namespace Domains.Biology.Omics.AlleleSpecificReporter.Tests

open MeasureTheory ProbabilityTheory Real Finset

/-- `32` plasmids: the first `16` carry the alternative allele, the other `16` the reference
allele; the plasmid counts are `1` and `2` alternately. -/
private def tested : Design (Fin 32) where
  carriesAlt i := decide (i.val < 16)
  plasmidCount i := i.val % 2 + 1
  plasmidCount_pos _ := Nat.succ_pos _

/-- The same plasmids with every allele label flipped. -/
private def flipped : Design (Fin 32) where
  carriesAlt i := !decide (i.val < 16)
  plasmidCount i := i.val % 2 + 1
  plasmidCount_pos _ := Nat.succ_pos _

/-- `30` plasmids, `15` per allele: one plasmid short of the threshold. -/
private def short : Design (Fin 30) where
  carriesAlt i := decide (i.val < 15)
  plasmidCount _ := 1
  plasmidCount_pos _ := Nat.one_pos

-- Sixteen plasmids per allele are tested; fifteen are not.
example : tested.IsTested := by decide

example : ¬ short.IsTested := by decide

-- More than fifteen plasmids of one allele do not suffice.
example : ¬ (⟨fun _ => true, fun _ => 1, fun _ => Nat.one_pos⟩ : Design (Fin 40)).IsTested := by
  decide

/-- A twofold allelic effect: `β₀ = 0`, `β₁ = log 2`, `θ = 1`. -/
private noncomputable def twofold : Parameters where
  β₀ := 0
  β₁ := log 2
  θ := 1
  θ_pos := one_pos

/-- No allelic effect: `β₀ = log 3`, `β₁ = 0`, `θ = 2`. -/
private noncomputable def null : Parameters where
  β₀ := log 3
  β₁ := 0
  θ := 2
  θ_pos := two_pos

-- Plasmid `1` carries the alternative allele and has plasmid count `2`: its mean RNA count is
-- `2 · exp (log 2) = 4`, and so is the expected RNA count of the model.
example : tested.mean twofold 1 = 4 := by
  rw [← div_mul_cancel₀ (tested.mean twofold 1)
      (Nat.cast_ne_zero.2 (tested.plasmidCount_pos 1).ne'), tested.mean_div_plasmidCount]
  norm_num [twofold, Design.alleleIndicator, tested, exp_log]

example : ∫ y, (y 1 : ℝ) ∂tested.countLaw twofold = tested.mean twofold 1 :=
  tested.integral_countLaw twofold 1

-- `β₀` is the log expression per plasmid of the reference allele (plasmid `16`), and `β₁` the log
-- fold change between plasmid `0` (alternative) and plasmid `16` (reference).
example : log (tested.mean twofold 16 / tested.plasmidCount 16) = 0 :=
  tested.log_mean_div_plasmidCount_of_ref twofold (by decide)

example :
    log (tested.mean twofold 0 / tested.plasmidCount 0 /
      (tested.mean twofold 16 / tested.plasmidCount 16)) = log 2 :=
  tested.log_foldChange twofold (by decide) (by decide)

-- The regression equation at plasmid `17` (reference allele, plasmid count `2`).
example : log (∫ y, (y 17 : ℝ) ∂tested.countLaw null) = log 3 + log 2 := by
  rw [tested.log_integral_countLaw]
  norm_num [null, tested]

-- The likelihood is the product of the fragment masses: with one plasmid of count `1`,
-- `β₀ = β₁ = 0` and `θ = 1`, the law of its RNA count is geometric with `P(0) = 1 / 2`.
example :
    (Design.countLaw ⟨fun _ => false, fun _ => 1, fun _ => Nat.one_pos⟩
      ⟨0, 0, 1, one_pos⟩ : Measure (Fin 1 → ℕ)).real {fun _ => 0} = 1 / 2 := by
  rw [Design.countLaw_real_singleton, Fin.prod_univ_one]
  norm_num [Design.mean, Design.offset, negBinomialReal]

-- Under `H₀`, flipping every allele label leaves the law of the RNA counts unchanged.
example : tested.countLaw null = flipped.countLaw null :=
  tested.countLaw_eq_of_β₁_eq_zero flipped rfl rfl

-- With `β₁ ≠ 0` the law of the RNA counts separates the two labellings: the mean RNA count of
-- plasmid `0` doubles when it carries the alternative allele.
example : tested.countLaw twofold ≠ flipped.countLaw twofold := by
  intro h
  have h0 := congrArg (fun ν => ∫ y, (y 0 : ℝ) ∂ν) h
  simp only [Design.integral_countLaw, Design.mean, Design.alleleIndicator, Design.offset] at h0
  norm_num [twofold, tested, flipped] at h0

/-- The SNP `tested` with its threshold check. -/
private def testedSNP : {D : Design (Fin 32) // D.IsTested} := ⟨tested, by decide⟩

-- The null law lies in `H₀` and not in `H₁`; the twofold law lies in `H₁` and not in `H₀`.
example : tested.countLaw null ∈ (allelicActivityTest testedSNP).1 :=
  (countLaw_mem_allelicActivityTest_fst_iff testedSNP null).2 rfl

example : tested.countLaw null ∉ (allelicActivityTest testedSNP).2 := fun h =>
  (countLaw_mem_allelicActivityTest_snd_iff testedSNP null).1 h rfl

example : tested.countLaw twofold ∉ (allelicActivityTest testedSNP).1 := by
  rw [show tested = testedSNP.1 from rfl, countLaw_mem_allelicActivityTest_fst_iff]
  norm_num [twofold]

example : tested.countLaw twofold ∈ (allelicActivityTest testedSNP).2 := by
  rw [show tested = testedSNP.1 from rfl, countLaw_mem_allelicActivityTest_snd_iff]
  norm_num [twofold]

example : Disjoint (allelicActivityTest testedSNP).1 (allelicActivityTest testedSNP).2 :=
  disjoint_allelicActivityTest testedSNP

end Domains.Biology.Omics.AlleleSpecificReporter.Tests
