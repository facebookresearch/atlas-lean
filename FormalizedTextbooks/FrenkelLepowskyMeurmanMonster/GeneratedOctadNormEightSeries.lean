/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightSource

/-! Counting the eight actual coordinate residues by certified source histograms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Bounded source solutions on the eight section coordinates. -/
def GeneratedOctadNormEightBounded (b : ZMod 2) :=
  {a : Fin 8 → Fin 17 //
    (∀ i, (leechNormEightCoordinate (a i) : ZMod 4) = 2 * (b.val : ZMod 4)) ∧
    (∑ i, (leechNormEightCoordinate (a i)).natAbs ^ 2) = 64 ∧
    ((∑ i, leechNormEightCoordinate (a i) : ℤ) : ZMod 8) = 0}

/-- Abstract finite assignments, without expanding their enumeration. -/
@[instance_reducible] def generatedOctadAssignmentFintype : Fintype (Fin 8 → Fin 17) :=
  Fintype.ofFinite _
attribute [local instance] generatedOctadAssignmentFintype

instance (b : ZMod 2) : Fintype (GeneratedOctadNormEightBounded b) := by
  unfold GeneratedOctadNormEightBounded
  infer_instance

/-- The eighth power enumerates exactly all eight coordinate assignments. -/
theorem generatedOctadNormEight_series_expand (b : ZMod 2) :
    leechNormEightCoordinateSeries false b ^ 8 =
      ∑ a : Fin 8 → Fin 17,
        if (∀ i, (leechNormEightCoordinate (a i) : ZMod 4) = 2 * (b.val : ZMod 4)) then
          AddMonoidAlgebra.single
            ((∑ i, (leechNormEightCoordinate (a i)).natAbs ^ 2),
              ((∑ i, leechNormEightCoordinate (a i) : ℤ) : ZMod 8)) 1 else 0 := by
  classical
  have he : leechNormEightCoordinateSeries false b ^ 8 =
      ∏ _i : Fin 8, leechNormEightCoordinateSeries false b := by simp
  rw [he]
  unfold leechNormEightCoordinateSeries
  simp only [Bool.toNat_false, Nat.cast_zero, zero_add]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  by_cases ha : ∀ i, (leechNormEightCoordinate (a i) : ZMod 4) = 2 * (b.val : ZMod 4)
  · rw [ite_eq_left ha]
    simp only [ha, ite_true]
    rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
    congr 1
    apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Int.cast_sum]
  · rw [ite_eq_right ha]
    obtain ⟨i, hi⟩ := not_forall.mp ha
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

/-- The norm and sum-residue coefficient counts precisely these bounded solutions. -/
theorem generatedOctadNormEight_series_count (b : ZMod 2) :
    (leechNormEightCoordinateSeries false b ^ 8).coeff (64, 0) =
      Nat.card (GeneratedOctadNormEightBounded b) := by
  classical
  unfold GeneratedOctadNormEightBounded
  rw [generatedOctadNormEight_series_expand, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : ∀ i, (leechNormEightCoordinate (a i) : ZMod 4) = 2 * (b.val : ZMod 4)
  · simp [ha, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Prod.mk.injEq, eq_comm]
  · simp only [ha, ite_false, false_and, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- The two certified source histogram entries are 1136 and 1024. -/
theorem generatedOctadNormEight_histogram :
    leechNormEightCountTable false 0 8 64 0 = 1136 ∧
      leechNormEightCountTable false 1 8 64 0 = 1024 := by
  decide +kernel

/-- The residue-zero solutions number 1136. -/
theorem generatedOctadNormEightBounded_zero_card :
    Nat.card (GeneratedOctadNormEightBounded 0) = 1136 := by
  rw [← generatedOctadNormEight_series_count,
    leechNormEightCountTable_sound false 0 8 (by decide) 64 (by decide) 0]
  exact generatedOctadNormEight_histogram.1

/-- The residue-two solutions number 1024. -/
theorem generatedOctadNormEightBounded_one_card :
    Nat.card (GeneratedOctadNormEightBounded 1) = 1024 := by
  rw [← generatedOctadNormEight_series_count,
    leechNormEightCountTable_sound false 1 8 (by decide) 64 (by decide) 0]
  exact generatedOctadNormEight_histogram.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
