/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOrthogonalOctadWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

/-! Transport of original Golay word counts to the canonical octad labels,
and actual physical sign counts for root-perpendicular shortest vectors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Filtering the canonical octad labels counts the same actual original Golay words. -/
theorem generatedFeasibleOctadLabel_filter_card (P : Fin 4096 → Prop) [DecidablePred P] :
    (Finset.univ.filter fun o : Fin 759 => P (golayOctadLabel o)).card =
      (golayOctads.filter P).card := by
  apply Finset.card_bij (fun o _ => golayOctadLabel o)
  · intro o ho
    exact Finset.mem_filter.mpr
      ⟨(golayOctads.orderIsoOfFin golayOctads_card o).property,
        (Finset.mem_filter.mp ho).2⟩
  · intro o _ p _ he
    apply (golayOctads.orderIsoOfFin golayOctads_card).injective
    exact Subtype.ext he
  · intro d hd
    let x : golayOctads := ⟨d, (Finset.mem_filter.mp hd).1⟩
    let o := (golayOctads.orderIsoOfFin golayOctads_card).symm x
    have ho : golayOctadLabel o = d := congrArg Subtype.val
      ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply x)
    exact ⟨o, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho ▸ (Finset.mem_filter.mp hd).2⟩,
      ho⟩

/-- Canonical octad labels omitting both physical root coordinates. -/
def generatedFeasibleOctadOutsideLabels : Finset (Fin 759) :=
  Finset.univ.filter fun o =>
    (golayEncodedMask (golayOctadLabel o).val).testBit 0 = false ∧
      (golayEncodedMask (golayOctadLabel o).val).testBit 1 = false

/-- Canonical octad labels containing both physical root coordinates. -/
def generatedFeasibleOctadContainingLabels : Finset (Fin 759) :=
  Finset.univ.filter fun o =>
    (golayEncodedMask (golayOctadLabel o).val).testBit 0 = true ∧
      (golayEncodedMask (golayOctadLabel o).val).testBit 1 = true

/-- The actual canonical outside-pair octad catalogue has 330 labels. -/
theorem generatedFeasibleOctadOutsideLabels_card :
    generatedFeasibleOctadOutsideLabels.card = 330 := by
  rw [generatedFeasibleOctadOutsideLabels]
  rw [generatedFeasibleOctadLabel_filter_card (fun d : Fin 4096 =>
    (golayEncodedMask d.val).testBit 0 = false ∧
      (golayEncodedMask d.val).testBit 1 = false)]
  have he : golayOctads.filter (fun d => (golayEncodedMask d.val).testBit 0 = false ∧
      (golayEncodedMask d.val).testBit 1 = false) = generatedFeasibleOctadsOutsideRootPair := by
    ext d
    simp only [golayOctads, generatedFeasibleOctadsOutsideRootPair, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [he, generatedFeasibleOctadsOutsideRootPair_card]

/-- The actual canonical containing-pair octad catalogue has 77 labels. -/
theorem generatedFeasibleOctadContainingLabels_card :
    generatedFeasibleOctadContainingLabels.card = 77 := by
  rw [generatedFeasibleOctadContainingLabels]
  rw [generatedFeasibleOctadLabel_filter_card (fun d : Fin 4096 =>
    (golayEncodedMask d.val).testBit 0 = true ∧
      (golayEncodedMask d.val).testBit 1 = true)]
  have he : golayOctads.filter (fun d => (golayEncodedMask d.val).testBit 0 = true ∧
      (golayEncodedMask d.val).testBit 1 = true) =
      generatedFeasibleOctadsContainingRootPair := by
    ext d
    simp only [golayOctads, generatedFeasibleOctadsContainingRootPair, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [he, generatedFeasibleOctadsContainingRootPair_card]

/-- Each original local octad sign is its genuine shortest-vector physical coordinate. -/
theorem generatedFeasibleOctad_local_coordinate (o : Fin 759) (e : Fin 64) (k : Fin 8) :
    griessShortIntegral (Sum.inr (Sum.inl (o, e))) (golayOctadCoordinate o k) =
      if (trialityEvenMask e).testBit k.val then -2 else 2 := by
  simp only [griessShortIntegral, golayOctadCoordinate_mem,
    ite_true, griessOctadSignMask_local]

/-- For an octad containing the root pair, its actual physical coordinates agree in
exactly 32 of the original canonical sign patterns. -/
theorem generatedFeasibleOctadContaining_physical_count (o : Fin 759)
    (ho : o ∈ generatedFeasibleOctadContainingLabels) :
    (Finset.univ.filter fun e : Fin 64 =>
      griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
        griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1).card = 32 := by
  have h := (Finset.mem_filter.mp ho).2
  obtain ⟨i, hi⟩ := golayOctadCoordinate_surjective o 0 h.1
  obtain ⟨j, hj⟩ := golayOctadCoordinate_surjective o 1 h.2
  have hij : i ≠ j := by
    intro he
    have ht : (0 : Fin 24) = 1 := hi.symm.trans
      ((congrArg (golayOctadCoordinate o) he).trans hj)
    exact (by decide : (0 : Fin 24) ≠ 1) ht
  have he : (Finset.univ.filter fun e : Fin 64 =>
      griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
        griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1) =
      Finset.univ.filter (fun e : Fin 64 =>
        (trialityEvenMask e).testBit i.val = (trialityEvenMask e).testBit j.val) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hi, ← hj, generatedFeasibleOctad_local_coordinate,
      generatedFeasibleOctad_local_coordinate]
    cases (trialityEvenMask e).testBit i.val <;>
      cases (trialityEvenMask e).testBit j.val <;> decide
  rw [he]
  exact generatedFeasibleOctadEqualSigns_card i j hij

/-- An octad omitting both root coordinates is perpendicular in every original sign pattern. -/
theorem generatedFeasibleOctadOutside_physical_count (o : Fin 759)
    (ho : o ∈ generatedFeasibleOctadOutsideLabels) :
    (Finset.univ.filter fun e : Fin 64 =>
      griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
        griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1).card = 64 := by
  have h := (Finset.mem_filter.mp ho).2
  have he : (Finset.univ.filter fun e : Fin 64 =>
      griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
        griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1) = Finset.univ := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, griessShortIntegral,
      Fin.val_zero, Fin.val_one, h.1, h.2, Bool.false_eq_true, ite_false, eq_self]
  rw [he]
  decide

/-- Every octad contributes exactly its actual outside-pair or containing-pair sign count. -/
theorem generatedFeasibleOctad_physical_count (o : Fin 759) :
    (Finset.univ.filter fun e : Fin 64 =>
      griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
        griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1).card =
      (if o ∈ generatedFeasibleOctadOutsideLabels then 64 else 0) +
        (if o ∈ generatedFeasibleOctadContainingLabels then 32 else 0) := by
  by_cases h0 : (golayEncodedMask (golayOctadLabel o).val).testBit 0 = true <;>
    by_cases h1 : (golayEncodedMask (golayOctadLabel o).val).testBit 1 = true
  · have hi : o ∈ generatedFeasibleOctadContainingLabels :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0, h1⟩
    have hn : o ∉ generatedFeasibleOctadOutsideLabels := by
      intro ho
      have hf := (Finset.mem_filter.mp ho).2.1
      rw [h0] at hf
      cases hf
    rw [generatedFeasibleOctadContaining_physical_count o hi, ite_eq_right hn, ite_eq_left hi]
  · have he : (Finset.univ.filter fun e : Fin 64 =>
        griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
          griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1) = ∅ := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        griessShortIntegral, Fin.val_zero, Fin.val_one, h0, h1, Bool.false_eq_true,
        ite_true, ite_false]
      split <;> norm_num
    rw [he]
    simp only [Finset.card_empty, generatedFeasibleOctadOutsideLabels,
      generatedFeasibleOctadContainingLabels, Finset.mem_filter, Finset.mem_univ,
      h0, h1, Bool.true_eq_false, Bool.false_eq_true, false_and, and_false,
      ite_false, zero_add]
  · have he : (Finset.univ.filter fun e : Fin 64 =>
        griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
          griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1) = ∅ := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        griessShortIntegral, Fin.val_zero, Fin.val_one, h0, h1, Bool.false_eq_true,
        ite_true, ite_false]
      split <;> norm_num
    rw [he]
    simp only [Finset.card_empty, generatedFeasibleOctadOutsideLabels,
      generatedFeasibleOctadContainingLabels, Finset.mem_filter, Finset.mem_univ,
      h0, h1, Bool.true_eq_false, Bool.false_eq_true, false_and, and_false,
      ite_false, zero_add]
  · have hf0 : (golayEncodedMask (golayOctadLabel o).val).testBit 0 = false :=
      Bool.eq_false_iff.mpr h0
    have hf1 : (golayEncodedMask (golayOctadLabel o).val).testBit 1 = false :=
      Bool.eq_false_iff.mpr h1
    have hi : o ∈ generatedFeasibleOctadOutsideLabels :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf0, hf1⟩
    have hn : o ∉ generatedFeasibleOctadContainingLabels := by
      intro ho
      exact h0 (Finset.mem_filter.mp ho).2.1
    rw [generatedFeasibleOctadOutside_physical_count o hi, ite_eq_left hi, ite_eq_right hn]

/-- Every canonical octad short label satisfying actual physical root orthogonality. -/
def generatedFeasibleOrthogonalOctadLabels : Finset (Fin 759 × Fin 64) :=
  Finset.univ.filter fun z =>
    griessShortIntegral (Sum.inr (Sum.inl z)) 0 =
      griessShortIntegral (Sum.inr (Sum.inl z)) 1

/-- The entire actual perpendicular octad short catalogue has 23,584 labels. -/
theorem generatedFeasibleOrthogonalOctadLabels_card :
    generatedFeasibleOrthogonalOctadLabels.card = 23584 := by
  have hc : generatedFeasibleOrthogonalOctadLabels.card =
      ∑ z : Fin 759 × Fin 64, if griessShortIntegral (Sum.inr (Sum.inl z)) 0 =
        griessShortIntegral (Sum.inr (Sum.inl z)) 1 then (1 : ℕ) else 0 := by
    simpa only [generatedFeasibleOrthogonalOctadLabels, Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun z : Fin 759 × Fin 64 =>
        griessShortIntegral (Sum.inr (Sum.inl z)) 0 =
          griessShortIntegral (Sum.inr (Sum.inl z)) 1) Finset.univ).symm
  rw [hc, Fintype.sum_prod_type]
  simp only [Finset.sum_boole, Nat.cast_id]
  simp_rw [generatedFeasibleOctad_physical_count]
  rw [Finset.sum_add_distrib]
  have hw (s : Finset (Fin 759)) (n : ℕ) :
      (∑ o : Fin 759, if o ∈ s then n else 0) = s.card * n := by
    simp
  rw [hw, hw, generatedFeasibleOctadOutsideLabels_card,
    generatedFeasibleOctadContainingLabels_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
