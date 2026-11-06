/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSelectedShortGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSelectedOctadIntersectionData

/-! Exact selected-square bins in the complete original perpendicular short catalogue. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Every original root-perpendicular preferred pair in a given actual selected-square bin. -/
def generatedFeasibleContainingSelectedPairLabels (k : Fin 4) : Finset (Fin 2 × Fin 276) :=
  generatedFeasibleOrthogonalPairLabels.filter fun z =>
    generatedFeasibleContainingSelectedShortSquare (Sum.inl z) =
      generatedFeasibleContainingSelectedShortValues k

/-- Every original root-perpendicular preferred octad in the same actual bin. -/
def generatedFeasibleContainingSelectedOctadLabels (k : Fin 4) : Finset (Fin 759 × Fin 64) :=
  generatedFeasibleOrthogonalOctadLabels.filter fun z =>
    generatedFeasibleContainingSelectedShortSquare (Sum.inr (Sum.inl z)) =
      generatedFeasibleContainingSelectedShortValues k

/-- Every original root-perpendicular preferred odd label in the same actual bin. -/
def generatedFeasibleContainingSelectedOddLabels (k : Fin 4) : Finset (Fin 2048 × Fin 24) :=
  generatedFeasibleOrthogonalOddLabels.filter fun z =>
    generatedFeasibleContainingSelectedShortSquare (Sum.inr (Sum.inr z)) =
      generatedFeasibleContainingSelectedShortValues k

/-- The selected-square bin in the complete original preferred short catalogue. -/
def generatedFeasibleContainingSelectedShortLabels (k : Fin 4) : Finset GriessShortIndex :=
  generatedFeasibleOrthogonalShortLabels.filter fun r =>
    generatedFeasibleContainingSelectedShortSquare r =
      generatedFeasibleContainingSelectedShortValues k

/-- Both genuine axis phases over every original preferred short label in the bin. -/
def generatedFeasibleContainingSelectedSignedShortLabels (k : Fin 4) :
    Finset (GriessShortIndex × ZMod 2) :=
  generatedFeasibleContainingSelectedShortLabels k ×ˢ Finset.univ

private theorem filter_disj_sum {α β : Type*}
    (s : Finset α) (t : Finset β) (P : α ⊕ β → Prop) [DecidablePred P] :
    (s.disjSum t).filter P =
      (s.filter fun a => P (Sum.inl a)).disjSum (t.filter fun b => P (Sum.inr b)) := by
  ext x
  cases x <;> simp

/-- The entire actual bin partitions into its three original coordinate families. -/
theorem generatedFeasibleContainingSelectedShortLabels_partition (k : Fin 4) :
    generatedFeasibleContainingSelectedShortLabels k =
      (generatedFeasibleContainingSelectedPairLabels k).disjSum
        ((generatedFeasibleContainingSelectedOctadLabels k).disjSum
          (generatedFeasibleContainingSelectedOddLabels k)) := by
  unfold generatedFeasibleContainingSelectedShortLabels generatedFeasibleOrthogonalShortLabels
  rw [filter_disj_sum, filter_disj_sum]
  rfl

/-- The pair address equivalence transports the complete physical count faithfully. -/
theorem generatedFeasibleContainingSelectedPairLabels_card (k : Fin 4) :
    (generatedFeasibleContainingSelectedPairLabels k).card =
      (![240, 0, 192, 31] : Fin 4 → ℕ) k := by
  have hc : (generatedFeasibleContainingSelectedPairLabels k).card =
      ∑ z : Fin 2 × Fin 276,
        if griessShortIntegral (Sum.inl z) 0 = griessShortIntegral (Sum.inl z) 1 ∧
          generatedFeasibleContainingSelectedShortSquare (Sum.inl z) =
            generatedFeasibleContainingSelectedShortValues k then (1 : ℕ) else 0 := by
    rw [generatedFeasibleContainingSelectedPairLabels, generatedFeasibleOrthogonalPairLabels,
      Finset.filter_filter]
    exact (Finset.sum_boole (R := ℕ) _ Finset.univ).symm
  rw [hc]
  have hs (z : Fin 2 × Fin 276) :=
    generatedFeasibleContainingSelectedShortSquare_pair z.1 z.2
  simp_rw [hs]
  let e := Equiv.prodCongr (Equiv.refl (Fin 2)) griessCoordinatePairEquiv
  have h := Equiv.sum_comp e (fun z : Fin 2 × griessCoordinatePairs =>
    if ((4 * (if (0 : Fin 24) = z.2.val.1 then (1 : ℤ) else 0) +
        (if z.1 = 0 then -4 else 4) * (if (0 : Fin 24) = z.2.val.2 then 1 else 0)) =
      (4 * (if (1 : Fin 24) = z.2.val.1 then (1 : ℤ) else 0) +
        (if z.1 = 0 then -4 else 4) * (if (1 : Fin 24) = z.2.val.2 then 1 else 0))) ∧
      16 * (if z.2.val.1.val < 8 then (1 : ℤ) else 0) +
        16 * (if z.2.val.2.val < 8 then 1 else 0) =
          generatedFeasibleContainingSelectedShortValues k then (1 : ℕ) else 0)
  change _ = generatedFeasibleContainingSelectedPairPhysicalCount k at h
  exact h.trans (generatedFeasibleContainingSelectedPairPhysicalCount_eq k)

/-- Actual exceptional positions with the prescribed selected square in the original odd family. -/
def generatedFeasibleContainingSelectedOddPositions (k : Fin 4) : Finset (Fin 24) :=
  ((Finset.univ.erase 0).erase 1).filter fun j =>
    (8 + 8 * (if j.val < 8 then 1 else 0) : ℤ) =
      generatedFeasibleContainingSelectedShortValues k

private theorem generatedFeasibleContainingSelectedOddPositions_card (k : Fin 4) :
    (generatedFeasibleContainingSelectedOddPositions k).card = (![0, 16, 6, 0] : Fin 4 → ℕ) k := by
  have h : ∀ k : Fin 4, (generatedFeasibleContainingSelectedOddPositions k).card =
      (![0, 16, 6, 0] : Fin 4 → ℕ) k := by decide +kernel
  exact h k

/-- The odd bin uses all original equal-first-sign codes and its exact exceptional positions. -/
theorem generatedFeasibleContainingSelectedOddLabels_product (k : Fin 4) :
    generatedFeasibleContainingSelectedOddLabels k =
      generatedFeasibleOddEqualSignCodes ×ˢ generatedFeasibleContainingSelectedOddPositions k := by
  ext z
  have hs := generatedFeasibleContainingSelectedShortSquare_odd z.1 z.2
  simp only [generatedFeasibleContainingSelectedOddLabels, generatedFeasibleOrthogonalOddLabels,
    Finset.mem_filter, Finset.mem_product, generatedFeasibleContainingSelectedOddPositions,
    hs]
  tauto

/-- Complete preferred odd contributions, with all original Golay codes retained. -/
theorem generatedFeasibleContainingSelectedOddLabels_card (k : Fin 4) :
    (generatedFeasibleContainingSelectedOddLabels k).card =
      (![0, 16384, 6144, 0] : Fin 4 → ℕ) k := by
  rw [generatedFeasibleContainingSelectedOddLabels_product, Finset.card_product,
    generatedFeasibleOddEqualSignCodes_card, generatedFeasibleContainingSelectedOddPositions_card]
  fin_cases k <;> norm_num

/-- Original octad signs do not affect its genuine selected support square. -/
theorem generatedFeasibleContainingSelectedShortSquare_octad_weight (o : Fin 759) (e : Fin 64) :
    generatedFeasibleContainingSelectedShortSquare (Sum.inr (Sum.inl (o, e))) =
      4 * (generatedFeasibleContainingOctadSelectedWeight o : ℤ) := by
  simpa only [generatedFeasibleContainingOctadSelectedWeight,
    generatedFeasibleContainingCodeSelectedWeight, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero] using
      generatedFeasibleContainingSelectedShortSquare_octad o e

private theorem selected_octad_weight_iff (n : ℕ) (k : Fin 4) :
    4 * (n : ℤ) = generatedFeasibleContainingSelectedShortValues k ↔
      n = (![0, 2, 4, 8] : Fin 4 → ℕ) k := by
  fin_cases k
  · change 4 * (n : ℤ) = 0 ↔ n = 0
    omega
  · change 4 * (n : ℤ) = 8 ↔ n = 2
    omega
  · change 4 * (n : ℤ) = 16 ↔ n = 4
    omega
  · change 4 * (n : ℤ) = 32 ↔ n = 8
    omega

private theorem code_selected_positive (d : Fin 4096)
    (hd : (golayEncodedMask d.val).testBit 0 = true) :
    1 ≤ generatedFeasibleContainingCodeSelectedWeight d := by
  have h := Finset.single_le_sum (fun i _ =>
    Nat.zero_le (if i.val < 8 ∧ (golayEncodedMask d.val).testBit i.val then 1 else 0))
      (Finset.mem_univ (0 : Fin 24))
  simpa [generatedFeasibleContainingCodeSelectedWeight, hd] using h

private theorem code_selected_missing_zero (d : Fin 4096)
    (hd : (golayEncodedMask d.val).testBit 0 = false) :
    generatedFeasibleContainingCodeSelectedWeight d ≤ 7 := by
  have h (i : Fin 24) :
      (if i.val < 8 ∧ (golayEncodedMask d.val).testBit i.val then (1 : ℕ) else 0) ≤
        (if i.val < 8 ∧ i ≠ 0 then 1 else 0) := by
    by_cases hi : i = 0
    · subst i
      simp [hd]
    · by_cases hlt : i.val < 8
      · cases (golayEncodedMask d.val).testBit i.val <;> simp [hi, hlt]
      · simp [hlt]
  have hs : (∑ i : Fin 24, if i.val < 8 ∧ i ≠ 0 then (1 : ℕ) else 0) = 7 := by
    decide +kernel
  exact (Finset.sum_le_sum (fun i _ => h i)).trans hs.le

private theorem selected_incident_four_card (k : Fin 4) :
    (generatedFeasibleOctadContainingLabels.filter fun o =>
      generatedFeasibleContainingOctadSelectedWeight o = (![0, 2, 4, 8] : Fin 4 → ℕ) k).card =
        (![0, 16, 60, 1] : Fin 4 → ℕ) k := by
  fin_cases k
  · apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro o ho hzero
    have hp := code_selected_positive (golayOctadLabel o) (Finset.mem_filter.mp ho).2.1
    change generatedFeasibleContainingCodeSelectedWeight (golayOctadLabel o) = 0 at hzero
    omega
  · exact generatedFeasibleContainingSelectedIncidentOctads_card 0
  · exact generatedFeasibleContainingSelectedIncidentOctads_card 1
  · exact generatedFeasibleContainingSelectedIncidentOctads_card 2

private theorem selected_outside_four_card (k : Fin 4) :
    (generatedFeasibleOctadOutsideLabels.filter fun o =>
      generatedFeasibleContainingOctadSelectedWeight o = (![0, 2, 4, 8] : Fin 4 → ℕ) k).card =
        (![30, 240, 60, 0] : Fin 4 → ℕ) k := by
  fin_cases k
  · exact generatedFeasibleContainingSelectedOutsideOctads_card 0
  · exact generatedFeasibleContainingSelectedOutsideOctads_card 1
  · exact generatedFeasibleContainingSelectedOutsideOctads_card 2
  · apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro o ho height
    have hp := code_selected_missing_zero (golayOctadLabel o) (Finset.mem_filter.mp ho).2.1
    change generatedFeasibleContainingCodeSelectedWeight (golayOctadLabel o) = 8 at height
    omega

private theorem selected_product_fiber_card {α β : Type*} [Fintype α] [Fintype β]
    (P : α → β → Prop) [∀ a, DecidablePred (P a)] (Q : α → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun z : α × β => P z.1 z.2 ∧ Q z.1).card =
      ∑ a : α, if Q a then (Finset.univ.filter (P a)).card else 0 := by
  have hc : (Finset.univ.filter fun z : α × β => P z.1 z.2 ∧ Q z.1).card =
      ∑ z : α × β, if P z.1 z.2 ∧ Q z.1 then (1 : ℕ) else 0 := by
    simpa only [Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun z : α × β => P z.1 z.2 ∧ Q z.1) Finset.univ).symm
  rw [hc, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : Q a
  · simpa only [ha, and_true, ite_true, Nat.cast_id] using
      Finset.sum_boole (R := ℕ) (P a) Finset.univ
  · simp [ha]

private theorem selected_weighted_sum {α : Type*} [Fintype α] [DecidableEq α]
    (C D : Finset α) (Q : α → Prop) [DecidablePred Q] (a b : ℕ) :
    (∑ i : α, if Q i then
      (if i ∈ C then a else 0) + (if i ∈ D then b else 0) else 0) =
        a * (C.filter Q).card + b * (D.filter Q).card := by
  have hp (i : α) : (if Q i then
      (if i ∈ C then a else 0) + (if i ∈ D then b else 0) else 0) =
        a * (if i ∈ C ∧ Q i then 1 else 0) + b * (if i ∈ D ∧ Q i then 1 else 0) := by
    by_cases hq : Q i <;> by_cases hc : i ∈ C <;> by_cases hd : i ∈ D <;> simp [hq, hc, hd]
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hc : (∑ i : α, if i ∈ C ∧ Q i then (1 : ℕ) else 0) = (C.filter Q).card := by
    have he : Finset.univ.filter (fun i : α => i ∈ C ∧ Q i) = C.filter Q := by
      ext i
      simp
    simpa only [Nat.cast_id, he] using
      Finset.sum_boole (R := ℕ) (fun i : α => i ∈ C ∧ Q i) Finset.univ
  have hd : (∑ i : α, if i ∈ D ∧ Q i then (1 : ℕ) else 0) = (D.filter Q).card := by
    have he : Finset.univ.filter (fun i : α => i ∈ D ∧ Q i) = D.filter Q := by
      ext i
      simp
    simpa only [Nat.cast_id, he] using
      Finset.sum_boole (R := ℕ) (fun i : α => i ∈ D ∧ Q i) Finset.univ
  rw [hc, hd]

/-- Every preferred octad contributes through its actual original support and all genuine signs.
-/
theorem generatedFeasibleContainingSelectedOctadLabels_card (k : Fin 4) :
    (generatedFeasibleContainingSelectedOctadLabels k).card =
      (![1920, 15872, 5760, 32] : Fin 4 → ℕ) k := by
  rw [generatedFeasibleContainingSelectedOctadLabels, generatedFeasibleOrthogonalOctadLabels,
    Finset.filter_filter]
  have hs (z : Fin 759 × Fin 64) :=
    generatedFeasibleContainingSelectedShortSquare_octad_weight z.1 z.2
  simp_rw [hs, selected_octad_weight_iff]
  rw [selected_product_fiber_card (fun o e =>
    griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
      griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1)
    (fun o => generatedFeasibleContainingOctadSelectedWeight o =
      (![0, 2, 4, 8] : Fin 4 → ℕ) k)]
  simp_rw [generatedFeasibleOctad_physical_count]
  rw [selected_weighted_sum, selected_outside_four_card, selected_incident_four_card]
  fin_cases k <;> norm_num

/-- The complete original preferred bins have 2160, 32256, 12096 and sixty-three labels. -/
theorem generatedFeasibleContainingSelectedShortLabels_card (k : Fin 4) :
    (generatedFeasibleContainingSelectedShortLabels k).card =
      (![2160, 32256, 12096, 63] : Fin 4 → ℕ) k := by
  rw [generatedFeasibleContainingSelectedShortLabels_partition,
    Finset.card_disjSum, Finset.card_disjSum, generatedFeasibleContainingSelectedPairLabels_card,
    generatedFeasibleContainingSelectedOctadLabels_card,
    generatedFeasibleContainingSelectedOddLabels_card]
  fin_cases k <;> norm_num

/-- Both genuine phases give the exact original signed bins 4320, 64512, 24192 and 126. -/
theorem generatedFeasibleContainingSelectedSignedShortLabels_card (k : Fin 4) :
    (generatedFeasibleContainingSelectedSignedShortLabels k).card =
      (![4320, 64512, 24192, 126] : Fin 4 → ℕ) k := by
  rw [generatedFeasibleContainingSelectedSignedShortLabels, Finset.card_product,
    generatedFeasibleContainingSelectedShortLabels_card]
  have hphase : (Finset.univ : Finset (ZMod 2)).card = 2 := by decide
  rw [hphase]
  fin_cases k <;> norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
