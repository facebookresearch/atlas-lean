/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.StatisticalGenetics.KinshipIBD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Biology.StatisticalGenetics.KinshipIBD`

Kinship values are computed from the gene-dropping definitions through Malécot's recursion
under gene dropping (`Pedigree.geneDropKinship_*`, `Pedigree.inbreeding_*`), not through the
bridge theorems of `KinshipIBD`. -/

open MeasureTheory
open MathlibExt.Biology.StatisticalGenetics.Kinship
open MathlibExt.Biology.StatisticalGenetics.Relatedness

namespace MathlibExtTest.KinshipIBD

/-! ### Fixtures -/

/-- The empty pedigree. -/
def empty : Pedigree 0 where
  parents i := i.elim0
  parents_lt i := i.elim0

/-- Two unrelated founders. -/
def twoFounders : Pedigree 2 where
  parents := ![none, none]
  parents_lt := by
    intro i g h k
    fin_cases i <;> simp at h

/-- Founders `0, 1` and their child `2`. -/
def trio : Pedigree 3 where
  parents := ![none, none, some ![0, 1]]
  parents_lt := by
    intro i g h k
    fin_cases i <;> simp at h
    subst h; fin_cases k <;> decide

/-- Founders `0, 1` and their children `2, 3` (full sibs). -/
def sibs : Pedigree 4 where
  parents := ![none, none, some ![0, 1], some ![0, 1]]
  parents_lt := by
    intro i g h k
    fin_cases i <;> simp at h <;> subst h <;> fin_cases k <;> decide

/-- Ancestors precede descendants, so a later individual is not an ancestor. -/
theorem not_isAncestor {n : ℕ} (P : Pedigree n) {a b : Fin n} (h : b ≤ a) :
    ¬ P.IsAncestor a b := fun hab => absurd (hab.lt (P := P)) (not_lt.mpr h)

variable {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)

/-! ### The weights and the measure -/

example : Pedigree.alleleWeight p 1 = p := by simp [Pedigree.alleleWeight]

example : Pedigree.alleleWeight p 0 = 1 - p := by simp [Pedigree.alleleWeight]

/-- With no individuals the sample space has one outcome, of weight `1`. -/
example (x : Pedigree.GeneDropSpace 0) : Pedigree.geneDropWeight p x = 1 := by
  simp [Pedigree.geneDropWeight]

example (x : Pedigree.GeneDropSpace 0) :
    Pedigree.geneDropPMF p hp0.le hp1.le x = 1 := by
  simp [Pedigree.geneDropPMF, Pedigree.geneDropWeight]

example : IsProbabilityMeasure (Pedigree.geneDropMeasure (n := 2) p hp0.le hp1.le) :=
  inferInstance

/-- The model exists on the empty pedigree. -/
example : (empty.ibdModel p hp0 hp1).p = p := rfl

/-! ### Alleles follow their founder copy -/

/-- A founder copy carries its own founder allele. -/
example (ω : Pedigree.Coins 2) (A : Fin 2 × Fin 2 → Fin 2) :
    twoFounders.geneDropAllele (0, 1) (ω, A) = ((A (0, 1) : ℕ) : ℝ) := by
  simp only [Pedigree.geneDropAllele]
  rw [twoFounders.origin_of_parents_eq_none (c := (0, 1)) rfl]

/-- The paternal copy of the child carries the allele of the father's copy chosen by the coin. -/
example (ω : Pedigree.Coins 3) (A : Fin 3 × Fin 2 → Fin 2) (hω : ω 2 0 = 1) :
    trio.geneDropAllele (2, 0) (ω, A) = ((A (0, 1) : ℕ) : ℝ) := by
  simp only [Pedigree.geneDropAllele]
  rw [trio.origin_of_parents_eq_some (c := (2, 0)) (g := ![0, 1]) rfl, hω]
  change ((A (trio.origin ω (0, 1)) : ℕ) : ℝ) = _
  rw [trio.origin_of_parents_eq_none (c := (0, 1)) rfl]

/-! ### Ground truth from the gene-dropping definitions

These values are computed from `Pedigree.ibd` (its filter definition) and Malécot's recursion
under gene dropping, independently of `KinshipIBD`. -/

/-- Distinct founders have gene-dropping kinship `0`. -/
private theorem twoFounders_phi01 : twoFounders.geneDropKinship 0 1 = 0 :=
  twoFounders.geneDropKinship_of_parents_eq_none (by decide) (not_isAncestor _ (by decide)) rfl

/-- A founder has gene-dropping self-kinship `1/2`. -/
private theorem twoFounders_phi00 : twoFounders.geneDropKinship 0 0 = 1 / 2 := by
  rw [twoFounders.geneDropKinship_self, twoFounders.inbreeding_of_parents_eq_none rfl]
  norm_num

private theorem trio_phi00 : trio.geneDropKinship 0 0 = 1 / 2 := by
  rw [trio.geneDropKinship_self, trio.inbreeding_of_parents_eq_none rfl]; norm_num

private theorem trio_phi01 : trio.geneDropKinship 0 1 = 0 :=
  trio.geneDropKinship_of_parents_eq_none (by decide) (not_isAncestor _ (by decide)) rfl

/-- Parent and child have gene-dropping kinship `1/4`. -/
private theorem trio_phi02 : trio.geneDropKinship 0 2 = 1 / 4 := by
  rw [trio.geneDropKinship_of_parents_eq_some (g := ![0, 1]) (by decide)
    (not_isAncestor _ (by decide)) rfl]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, trio_phi00,
    trio_phi01]
  norm_num

/-- The child of unrelated founders has gene-dropping inbreeding `0`. -/
private theorem trio_F2 : trio.inbreeding 2 = 0 := by
  rw [trio.inbreeding_of_parents_eq_some (g := ![0, 1]) rfl]
  exact trio_phi01

/-- Copies of the two founders are never IBD (from the filter definition of `ibd`). -/
private theorem trio_ibd_founders (a c : Fin 2) : trio.ibd (0, a) (1, c) = 0 := by
  simp only [Pedigree.ibd]
  rw [Finset.filter_false_of_mem fun ω _ => by
    rw [trio.origin_of_parents_eq_none (c := (0, a)) rfl,
      trio.origin_of_parents_eq_none (c := (1, c)) rfl]
    simp]
  simp

private theorem trio_ibd_0001 : trio.ibd (0, 0) (0, 1) = 0 :=
  trio.inbreeding_of_parents_eq_none (i := 0) rfl

/-- IBD probabilities between the father's copies and the child's copies. -/
private theorem trio_ibd_0020 : trio.ibd (0, 0) (2, 0) = 1 / 2 := by
  rw [trio.ibd_of_parents_eq_some (g := ![0, 1]) (by decide) (not_isAncestor _ (by decide)) rfl]
  simp only [Matrix.cons_val_zero, trio.ibd_self, trio_ibd_0001]
  norm_num

private theorem trio_ibd_0120 : trio.ibd (0, 1) (2, 0) = 1 / 2 := by
  rw [trio.ibd_of_parents_eq_some (g := ![0, 1]) (by decide) (not_isAncestor _ (by decide)) rfl]
  simp only [Matrix.cons_val_zero, trio.ibd_self, trio.ibd_comm (0, 1) (0, 0), trio_ibd_0001]
  norm_num

private theorem trio_ibd_0a21 (a : Fin 2) : trio.ibd (0, a) (2, 1) = 0 := by
  rw [trio.ibd_of_parents_eq_some (g := ![0, 1]) (by decide) (not_isAncestor _ (by decide)) rfl]
  have h0 : trio.ibd (0, a) ((![0, 1] : Fin 2 → Fin 3) 1, 0) = 0 := trio_ibd_founders a 0
  have h1 : trio.ibd (0, a) ((![0, 1] : Fin 2 → Fin 3) 1, 1) = 0 := trio_ibd_founders a 1
  rw [h0, h1]
  norm_num

private theorem sibs_phi00 : sibs.geneDropKinship 0 0 = 1 / 2 := by
  rw [sibs.geneDropKinship_self, sibs.inbreeding_of_parents_eq_none rfl]; norm_num

private theorem sibs_phi11 : sibs.geneDropKinship 1 1 = 1 / 2 := by
  rw [sibs.geneDropKinship_self, sibs.inbreeding_of_parents_eq_none rfl]; norm_num

private theorem sibs_phi01 : sibs.geneDropKinship 0 1 = 0 :=
  sibs.geneDropKinship_of_parents_eq_none (by decide) (not_isAncestor _ (by decide)) rfl

private theorem sibs_phi20 : sibs.geneDropKinship 2 0 = 1 / 4 := by
  rw [sibs.geneDropKinship_comm, sibs.geneDropKinship_of_parents_eq_some (g := ![0, 1])
    (by decide) (not_isAncestor _ (by decide)) rfl]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sibs_phi00,
    sibs_phi01]
  norm_num

private theorem sibs_phi21 : sibs.geneDropKinship 2 1 = 1 / 4 := by
  rw [sibs.geneDropKinship_comm, sibs.geneDropKinship_of_parents_eq_some (g := ![0, 1])
    (by decide) (not_isAncestor _ (by decide)) rfl]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sibs_phi11,
    sibs.geneDropKinship_comm 1 0, sibs_phi01]
  norm_num

/-- Full sibs have gene-dropping kinship `1/4`. -/
private theorem sibs_phi23 : sibs.geneDropKinship 2 3 = 1 / 4 := by
  rw [sibs.geneDropKinship_of_parents_eq_some (g := ![0, 1]) (by decide)
    (not_isAncestor _ (by decide)) rfl]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sibs_phi20,
    sibs_phi21]
  norm_num

/-- Full sibs have tabular kinship `1/4` (Malécot's tabular recursion). -/
private theorem sibs_kinship23 : sibs.kinship 2 3 = 1 / 4 := by
  have h0 : sibs.kinship 0 0 = 1 / 2 := sibs.kinship_self_of_parents_eq_none rfl
  have h01 : sibs.kinship 0 1 = 0 := sibs.kinship_of_lt_of_parents_eq_none (by decide) rfl
  have h1 : sibs.kinship 1 1 = 1 / 2 := sibs.kinship_self_of_parents_eq_none rfl
  have h20 : sibs.kinship 2 0 = 1 / 4 := by
    rw [sibs.kinship_of_gt_of_parents_eq_some (g := ![0, 1]) (by decide) rfl]
    norm_num [h0, sibs.kinship_comm 1 0, h01]
  have h21 : sibs.kinship 2 1 = 1 / 4 := by
    rw [sibs.kinship_of_gt_of_parents_eq_some (g := ![0, 1]) (by decide) rfl]
    norm_num [h01, h1]
  rw [sibs.kinship_of_lt_of_parents_eq_some (g := ![0, 1]) (by decide) rfl]
  norm_num [h20, h21]

/-! ### Moments of the gene-dropping measure, computed directly

These use only the moment theorems `integral_geneDropAllele` and
`integral_geneDropAllele_mul` and the ground-truth IBD values above. -/

/-- Alleles of distinct founder copies are uncorrelated: `𝔼[a a'] = p²`. -/
example : ∫ x, twoFounders.geneDropAllele (0, 0) x * twoFounders.geneDropAllele (1, 0) x
    ∂(Pedigree.geneDropMeasure p hp0.le hp1.le) = p ^ 2 := by
  have h : twoFounders.ibd (0, 0) (1, 0) = 0 := by
    simp only [Pedigree.ibd]
    rw [Finset.filter_false_of_mem fun ω _ => by
      rw [twoFounders.origin_of_parents_eq_none (c := (0, 0)) rfl,
        twoFounders.origin_of_parents_eq_none (c := (1, 0)) rfl]
      decide]
    simp
  rw [twoFounders.integral_geneDropAllele_mul, h]
  ring

/-- The parent-offspring GRM moment `𝔼[A_{0,2}] = 1/2`, expanded by hand into first and second
allele moments (no GRM or kinship theorem is used). -/
example : ∫ x, (trio.ibdModel p hp0 hp1).grm 0 2 x
    ∂(Pedigree.geneDropMeasure p hp0.le hp1.le) = 1 / 2 := by
  set μ := Pedigree.geneDropMeasure (n := 3) p hp0.le hp1.le
  set G := trio.geneDropAllele
  change ∫ x, (G (0, 0) x + G (0, 1) x - 2 * p) * (G (2, 0) x + G (2, 1) x - 2 * p) /
      (2 * p * (1 - p)) ∂μ = 1 / 2
  have hexp : (fun x => (G (0, 0) x + G (0, 1) x - 2 * p) * (G (2, 0) x + G (2, 1) x - 2 * p))
      = fun x => G (0, 0) x * G (2, 0) x + G (0, 0) x * G (2, 1) x + G (0, 1) x * G (2, 0) x +
        G (0, 1) x * G (2, 1) x - 2 * p * G (0, 0) x - 2 * p * G (0, 1) x -
        2 * p * G (2, 0) x - 2 * p * G (2, 1) x + 4 * p ^ 2 := by
    funext x; ring
  rw [integral_div, hexp]
  rw [integral_add .of_finite .of_finite, integral_sub .of_finite .of_finite,
    integral_sub .of_finite .of_finite, integral_sub .of_finite .of_finite,
    integral_sub .of_finite .of_finite, integral_add .of_finite .of_finite,
    integral_add .of_finite .of_finite, integral_add .of_finite .of_finite]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul, G, μ,
    trio.integral_geneDropAllele, trio.integral_geneDropAllele_mul, trio_ibd_0020,
    trio_ibd_0120, trio_ibd_0a21]
  have hp : p * (1 - p) ≠ 0 := mul_ne_zero hp0.ne' (sub_pos.mpr hp1).ne'
  field_simp
  ring

/-! ### The bridge theorems of `KinshipIBD`

These apply the bridge theorems and compare against the ground truth above. -/

example : (twoFounders.ibdModel p hp0 hp1).kinship 0 1 = 0 := by
  rw [twoFounders.ibdModel_kinship, twoFounders_phi01]

example : (twoFounders.ibdModel p hp0 hp1).kinship 0 0 = 1 / 2 := by
  rw [twoFounders.ibdModel_kinship, twoFounders_phi00]

example : (trio.ibdModel p hp0 hp1).kinship 2 0 = 1 / 4 := by
  rw [trio.ibdModel_kinship, trio.geneDropKinship_comm, trio_phi02]

example : (trio.ibdModel p hp0 hp1).inbreeding 2 = 0 := by
  rw [trio.ibdModel_inbreeding, trio_F2]

/-- The GRM corollary agrees with the hand expansion above. -/
example : ∫ x, (trio.ibdModel p hp0 hp1).grm 0 2 x
    ∂(Pedigree.geneDropMeasure p hp0.le hp1.le) = 1 / 2 := by
  rw [trio.integral_grm_ibdModel, trio_phi02]
  norm_num

example : (sibs.ibdModel p hp0 hp1).kinship 2 3 = 1 / 4 := by
  rw [sibs.ibdModel_kinship, sibs_phi23]

/-- The tabular-kinship bridge, checked against the tabular recursion. -/
example : (sibs.ibdModel p hp0 hp1).kinship 2 3 = 1 / 4 := by
  rw [sibs.ibdModel_kinship_eq_kinship, sibs_kinship23]

end MathlibExtTest.KinshipIBD
