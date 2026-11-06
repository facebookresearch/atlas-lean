/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientZeroTools
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadCoordinates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadIntegralSpanData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadStabilizerProjection
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOrthogonalOctadCoordinates

/-! The octad local family: exactly 4440 actual signed-short axes are orthogonal to the
actual octad prototype, the actual triality image of the signed octad axis on the
coordinates 8–15. These are 56 + 480 pair addresses and 64 + 3840 octad addresses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The coordinates of the prototype octad, as a decidable predicate. -/
def generatedFeasibleAmbientOctadSupport (i : Fin 24) : Prop := 8 ≤ i.val ∧ i.val < 16

instance (i : Fin 24) : Decidable (generatedFeasibleAmbientOctadSupport i) := by
  unfold generatedFeasibleAmbientOctadSupport
  infer_instance

private theorem octad_mask_testBit (i : Fin 24) :
    (golayEncodedMask (golayOctadLabel generatedOctadBasisOctad).val).testBit i.val =
      decide (generatedFeasibleAmbientOctadSupport i) := by
  rw [generatedOctadBasisOctad_mask]
  revert i
  decide

private theorem octad_label : golayOctadLabel generatedOctadBasisOctad = 3 :=
  congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨3, by decide +kernel⟩)

/-- The real indicator of the prototype octad. -/
noncomputable def generatedFeasibleAmbientOctadInd (i : Fin 24) : ℝ :=
  if generatedFeasibleAmbientOctadSupport i then 1 else 0

/-- The pairing with the octad prototype in terms of the octad indicator. -/
theorem generatedFeasibleAmbient_octad_form (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c) (generatedOctadLocalAxis 0 0) =
      2 * ∑ i, generatedFeasibleAmbientOctadInd i * griessShortVector r i ^ 2 -
        8 * qSign c * (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1 r := by
  rw [generatedFeasibleAmbient_axis_form]
  have hm := generatedAxis_triality_octad_matrix generatedOctadBasisOctad 0 0
  change (griessConwayEncode (generatedOctadLocalAxis 0 0)).1 = _ at hm
  rw [hm, generatedFeasibleAmbient_diagonal_contraction]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [generatedFeasibleAmbientOctadInd, octad_mask_testBit, decide_eq_true_eq]

/-- The integral prototype coordinates: two on the octad and zero elsewhere. -/
private theorem proto_integral (i : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) i =
      if generatedFeasibleAmbientOctadSupport i then 2 else 0 := by
  simp only [griessShortIntegral, octad_mask_testBit, generatedOctadBasisOctad_sign_mask,
    decide_eq_true_eq]
  have h0 : trialityEvenMask 0 * 256 = 0 := by decide
  rw [h0]
  simp

/-- Pair addresses: the pairing is `4(ind a + ind b) - 8 qSign c σ ind a ind b`. -/
private theorem pair_form (s : Fin 2) (p : Fin 276) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inl (s, p)) c) (generatedOctadLocalAxis 0 0) =
      4 * (generatedFeasibleAmbientOctadInd (griessCoordinatePair p).1 +
          generatedFeasibleAmbientOctadInd (griessCoordinatePair p).2) -
        8 * qSign c * ((if s = 0 then 1 else -1) *
          (generatedFeasibleAmbientOctadInd (griessCoordinatePair p).1 *
            generatedFeasibleAmbientOctadInd (griessCoordinatePair p).2)) := by
  rw [generatedFeasibleAmbient_octad_form]
  have hab := griessCoordinatePair_ne p
  have hsum : ∑ i, generatedFeasibleAmbientOctadInd i *
      griessShortVector (Sum.inl (s, p)) i ^ 2 =
      2 * (generatedFeasibleAmbientOctadInd (griessCoordinatePair p).1 +
        generatedFeasibleAmbientOctadInd (griessCoordinatePair p).2) := by
    have hu (i : Fin 24) : griessShortVector (Sum.inl (s, p)) i ^ 2 =
        2 * ((if i = (griessCoordinatePair p).1 then 1 else 0) +
          (if i = (griessCoordinatePair p).2 then 1 else 0)) := by
      rw [generatedFeasibleAmbient_shortVector_sq]
      simp only [griessShortIntegral]
      by_cases h1 : i = (griessCoordinatePair p).1 <;>
        by_cases h2 : i = (griessCoordinatePair p).2
      · exact absurd (h1.symm.trans h2) hab
      · simp [h1, hab]
        norm_num
      · simp [h2, hab.symm]
        norm_num
      · simp [h1, h2]
    simp only [hu, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hs := generatedAxis_triality_octad_pair_coordinate generatedOctadBasisOctad 0 0 s p
  change (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1 (Sum.inl (s, p)) = _ at hs
  rw [hsum, hs, mul_assoc 2, generatedFeasibleAmbient_shortVector_mul, proto_integral,
    proto_integral]
  simp only [generatedFeasibleAmbientOctadInd]
  split_ifs <;> norm_num

/-- The decidable form of orthogonality at pair addresses. -/
private def pairZero (s : Fin 2) (a b : Fin 24) (c : ZMod 2) : Prop :=
  (generatedFeasibleAmbientOctadSupport a ∧ generatedFeasibleAmbientOctadSupport b ∧
      (c = 0 ↔ s = 0)) ∨
    (¬ generatedFeasibleAmbientOctadSupport a ∧ ¬ generatedFeasibleAmbientOctadSupport b)

private instance (s : Fin 2) (a b : Fin 24) (c : ZMod 2) : Decidable (pairZero s a b c) := by
  unfold pairZero
  infer_instance

private theorem pair_zero_iff (s : Fin 2) (p : Fin 276) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inl (s, p)) c) (generatedOctadLocalAxis 0 0) = 0 ↔
      pairZero s (griessCoordinatePair p).1 (griessCoordinatePair p).2 c := by
  rw [pair_form]
  unfold pairZero generatedFeasibleAmbientOctadInd
  rcases (show c = 0 ∨ c = 1 by fin_cases c <;> simp) with rfl | rfl <;>
  fin_cases s <;>
  by_cases ha : generatedFeasibleAmbientOctadSupport (griessCoordinatePair p).1 <;>
  by_cases hb : generatedFeasibleAmbientOctadSupport (griessCoordinatePair p).2 <;>
  simp [ha, hb] <;> norm_num

/-- Exactly 536 actual pair addresses are orthogonal to the octad prototype. -/
private theorem pair_card :
    (Finset.univ.filter fun q : (Fin 2 × Fin 276) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inl q.1) q.2) (generatedOctadLocalAxis 0 0) = 0).card =
      536 := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [pair_zero_iff]
  have he (s : Fin 2) : (∑ p : Fin 276, ∑ c : ZMod 2,
      if pairZero s (griessCoordinatePair p).1 (griessCoordinatePair p).2 c then 1 else 0) =
      ∑ q ∈ griessCoordinatePairs, ∑ c : ZMod 2, if pairZero s q.1 q.2 c then 1 else 0 := by
    rw [← Finset.sum_coe_sort griessCoordinatePairs]
    exact Fintype.sum_equiv griessCoordinatePairEquiv _ _ fun _ => rfl
  simp_rw [he]
  decide +kernel

/-- Squares of octad short coordinates: four on the octad support and zero elsewhere. -/
private theorem octad_short_sq (o : Fin 759) (e : Fin 64) (i : Fin 24) :
    griessShortVector (Sum.inr (Sum.inl (o, e))) i ^ 2 =
      if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then 1 / 2 else 0 := by
  rw [generatedFeasibleAmbient_shortVector_sq]
  simp only [griessShortIntegral]
  split_ifs <;> norm_num

private theorem ind_sum : ∑ i, generatedFeasibleAmbientOctadInd i = 8 := by
  have h : (Finset.univ.filter generatedFeasibleAmbientOctadSupport).card = 8 := by
    decide
  simp only [generatedFeasibleAmbientOctadInd]
  rw [Finset.sum_boole, h]
  norm_num

/-- Octad addresses on the prototype octad: the pairing is `8 - 8 qSign c S` with `S² = 1`. -/
private theorem same_octad_form (e : Fin 64) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) c)
        (generatedOctadLocalAxis 0 0) =
      8 - 8 * qSign c * (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1
        (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) := by
  rw [generatedFeasibleAmbient_octad_form]
  have hsum : ∑ i, generatedFeasibleAmbientOctadInd i *
      griessShortVector (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) i ^ 2 = 4 := by
    simp_rw [octad_short_sq, octad_mask_testBit, decide_eq_true_eq]
    have he (i : Fin 24) : generatedFeasibleAmbientOctadInd i *
        (if generatedFeasibleAmbientOctadSupport i then (1 : ℝ) / 2 else 0) =
          generatedFeasibleAmbientOctadInd i / 2 := by
      simp only [generatedFeasibleAmbientOctadInd]
      split_ifs <;> norm_num
    simp_rw [he, ← Finset.sum_div, ind_sum]
    norm_num
  rw [hsum]
  ring

/-- Octad addresses on another octad: the pairing is the size of the intersection. -/
private theorem other_octad_form (o : Fin 759) (e : Fin 64) (c : ZMod 2)
    (ho : o ≠ generatedOctadBasisOctad) :
    griessForm (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c) (generatedOctadLocalAxis 0 0) =
      ∑ i, generatedFeasibleAmbientOctadInd i *
        (if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then 1 else 0) := by
  rw [generatedFeasibleAmbient_octad_form]
  have hs := generatedAxis_triality_octad_other_coordinate generatedOctadBasisOctad o 0 e 0 ho
  change (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1 _ = 0 at hs
  rw [hs, mul_zero, sub_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [octad_short_sq]
  split_ifs <;> ring

/-- An octad disjoint from the prototype octad. -/
private def disjointLabel (d : Fin 4096) : Prop :=
  ∀ i : Fin 24, ¬ (generatedFeasibleAmbientOctadSupport i ∧
    (golayEncodedMask d.val).testBit i.val = true)

private instance (d : Fin 4096) : Decidable (disjointLabel d) := by
  unfold disjointLabel
  infer_instance

private theorem other_octad_zero_iff (o : Fin 759) (e : Fin 64) (c : ZMod 2)
    (ho : o ≠ generatedOctadBasisOctad) :
    griessForm (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c) (generatedOctadLocalAxis 0 0) =
      0 ↔ disjointLabel (golayOctadLabel o) := by
  rw [other_octad_form o e c ho, Finset.sum_eq_zero_iff_of_nonneg]
  · unfold disjointLabel generatedFeasibleAmbientOctadInd
    apply forall_congr'
    intro i
    simp only [Finset.mem_univ, true_implies]
    split_ifs <;> simp_all
  · intro i _
    unfold generatedFeasibleAmbientOctadInd
    split_ifs <;> norm_num

private theorem sign_sum_one (S : ℝ) (hS : S ^ 2 = 1) :
    (∑ c : ZMod 2, if 8 - 8 * qSign c * S = 0 then 1 else 0) = 1 := by
  have h : (S - 1) * (S + 1) = 0 := by linear_combination hS
  rcases mul_eq_zero.mp h with h1 | h1
  · have hS1 : S = 1 := by linarith
    subst hS1
    have he (c : ZMod 2) : (8 - 8 * qSign c * 1 = 0) ↔ c = 0 := by
      rw [← qSign_eq_one_iff]
      constructor <;> intro h <;> linarith
    simp_rw [he]
    rw [Finset.sum_ite_eq']
    simp
  · have hS1 : S = -1 := by linarith
    subst hS1
    have he (c : ZMod 2) : (8 - 8 * qSign c * -1 = 0) ↔ c = 1 := by
      fin_cases c <;> simp [qSign]
    simp_rw [he]
    rw [Finset.sum_ite_eq']
    simp

private theorem octad_sum_label (F : Fin 4096 → ℕ) :
    ∑ o : Fin 759, F (golayOctadLabel o) = ∑ d ∈ golayOctads, F d := by
  rw [← Finset.sum_coe_sort golayOctads]
  exact Fintype.sum_equiv (golayOctads.orderIsoOfFin golayOctads_card).toEquiv _ _
    fun _ => rfl

set_option maxRecDepth 100000 in
-- The final kernel sum runs over all 759 actual octad labels.
/-- Exactly 3904 actual octad addresses are orthogonal to the octad prototype. -/
private theorem octad_card :
    (Finset.univ.filter fun q : (Fin 759 × Fin 64) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inl q.1)) q.2)
        (generatedOctadLocalAxis 0 0) = 0).card = 3904 := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hg (o : Fin 759) : (∑ e : Fin 64, ∑ c : ZMod 2,
      if griessForm (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)
        (generatedOctadLocalAxis 0 0) = 0 then 1 else 0) =
      (fun d : Fin 4096 => if d = 3 then 64 else if disjointLabel d then 128 else 0)
        (golayOctadLabel o) := by
    by_cases ho : o = generatedOctadBasisOctad
    · subst ho
      simp only [octad_label, ite_true]
      simp_rw [same_octad_form]
      have hsq (e : Fin 64) := generatedAxis_triality_octad_same_coordinate_square
        generatedOctadBasisOctad 0 e 0
      change ∀ e, (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1 _ ^ 2 = 1 at hsq
      simp_rw [sign_sum_one _ (hsq _)]
      simp
    · have hl : golayOctadLabel o ≠ 3 := by
        rw [← octad_label]
        exact fun h => ho (golayOctadLabel_injective h)
      simp only [hl, ite_false]
      simp_rw [other_octad_zero_iff o _ _ ho]
      split_ifs <;> simp
  simp_rw [hg]
  rw [octad_sum_label
    (fun d : Fin 4096 => if d = 3 then 64 else if disjointLabel d then 128 else 0)]
  decide +kernel

/-- Odd addresses are never orthogonal to the octad prototype. -/
private theorem odd_ne (d : Fin 2048) (j : Fin 24) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inr (Sum.inr (d, j))) c) (generatedOctadLocalAxis 0 0) ≠
      0 := by
  rw [generatedFeasibleAmbient_octad_form]
  have hs := generatedAxis_triality_octad_odd_coordinate generatedOctadBasisOctad 0 0 d j
  change (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1 _ = 0 at hs
  rw [hs, mul_zero, sub_zero]
  have hpos : 0 < ∑ i, generatedFeasibleAmbientOctadInd i *
      griessShortVector (Sum.inr (Sum.inr (d, j))) i ^ 2 := by
    have hnn (i : Fin 24) : 0 ≤ generatedFeasibleAmbientOctadInd i *
        griessShortVector (Sum.inr (Sum.inr (d, j))) i ^ 2 := by
      unfold generatedFeasibleAmbientOctadInd
      split_ifs <;> positivity
    have h8 : 0 < generatedFeasibleAmbientOctadInd 8 *
        griessShortVector (Sum.inr (Sum.inr (d, j))) 8 ^ 2 := by
      have hi : generatedFeasibleAmbientOctadInd 8 = 1 := by
        simp [generatedFeasibleAmbientOctadInd, generatedFeasibleAmbientOctadSupport]
      rw [hi, one_mul, generatedFeasibleAmbient_shortVector_sq]
      have hu : griessShortIntegral (Sum.inr (Sum.inr (d, j))) 8 ≠ 0 := by
        simp only [griessShortIntegral]
        split_ifs <;> norm_num
      positivity
    exact lt_of_lt_of_le h8 (Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ 8))
  linarith

private theorem odd_card :
    (Finset.univ.filter fun q : (Fin 2048 × Fin 24) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inr q.1)) q.2)
        (generatedOctadLocalAxis 0 0) = 0).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  exact odd_ne q.1.1 q.1.2 q.2

set_option maxRecDepth 1000000 in
-- Kernel checking of the three-family split unfolds the finite address type deeply.
private theorem total_card :
    (Finset.univ.filter fun p : GriessShortIndex × ZMod 2 =>
      griessForm (conwayShortAxis p.1 p.2) (generatedOctadLocalAxis 0 0) = 0).card = 4440 := by
  have h := generatedFeasibleAmbient_short_filter_card (fun r c =>
    griessForm (conwayShortAxis r c) (generatedOctadLocalAxis 0 0) = 0)
  rw [pair_card, octad_card, odd_card] at h
  exact h

/-- Exactly 4440 actual signed-short axes are orthogonal to the actual octad prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_octad :
    generatedFeasibleAmbientAxisZeroCount (generatedOctadLocalAxis 0 0) = 4440 := by
  rw [generatedFeasibleAmbientAxisZeroCount_eq_card]
  exact total_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
