/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientZeroTools
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddCoordinates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddTensorFixed
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawFormula

/-! The odd local family: exactly 506 actual signed-short axes are orthogonal to the
actual odd prototype, the actual triality image of the preferred odd signed-short axis.
They are the pair addresses avoiding the distinguished coordinate zero, one sign each. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual odd prototype in raw coordinates is the raw triality formula applied to the
preferred odd signed-short axis. -/
private theorem odd_encode : griessConwayEncode generatedOddAxis =
    generatedAxisGlobalRawTrialityFormula (conwayShortAxisRaw (Sum.inr (Sum.inr (0, 0))) 0) := by
  rw [generatedOddAxis, generatedAxisGlobalRawTrialityFormula_actual, conwayShortAxis_encode]

/-- Pair coordinates of the odd prototype come from the outer square of the odd vector. -/
private theorem odd_pair_coordinate (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedOddAxis).2.1 (Sum.inl (s, p)) =
      (if s = 0 then 1 else -1) *
        (2 * griessShortVector (Sum.inr (Sum.inr (0, 0))) (griessCoordinatePair p).1 *
          griessShortVector (Sum.inr (Sum.inr (0, 0))) (griessCoordinatePair p).2) := by
  rw [odd_encode]
  fin_cases s <;>
    simp [generatedAxisGlobalRawTrialityFormula, generatedAxisGlobalRawTrialityShort,
      conwayShortAxisRaw, Matrix.vecMulVec_apply, mul_assoc]

/-- The odd prototype has no octad coordinates. -/
private theorem odd_octad_coordinate (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedOddAxis).2.1 (Sum.inr (Sum.inl (o, e))) = 0 := by
  rw [odd_encode]
  simp [generatedAxisGlobalRawTrialityFormula, generatedAxisGlobalRawTrialityShort,
    conwayShortAxisRaw]

/-- The odd prototype has no odd coordinates. -/
private theorem odd_odd_coordinate (d : Fin 2048) (j : Fin 24) :
    (griessConwayEncode generatedOddAxis).2.1 (Sum.inr (Sum.inr (d, j))) = 0 := by
  rw [odd_encode]
  simp [generatedAxisGlobalRawTrialityFormula, generatedAxisGlobalRawTrialityShort,
    conwayShortAxisRaw]

/-- The pairing with the odd prototype. -/
theorem generatedFeasibleAmbient_odd_form (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c) generatedOddAxis =
      2 * ∑ i, (1 / 4 + if i = 0 then (2 : ℝ) else 0) * griessShortVector r i ^ 2 -
        8 * qSign c * (griessConwayEncode generatedOddAxis).2.1 r := by
  rw [generatedFeasibleAmbient_axis_form]
  have hm := generatedAxis_triality_odd_matrix 0 0 0
  change (griessConwayEncode generatedOddAxis).1 = _ at hm
  rw [hm, generatedFeasibleAmbient_diagonal_contraction]

/-- The diagonal weight sum is at least one for every actual short vector. -/
private theorem weight_sum_ge (r : GriessShortIndex) :
    1 ≤ ∑ i, (1 / 4 + if i = 0 then (2 : ℝ) else 0) * griessShortVector r i ^ 2 := by
  have hn : ∑ i, griessShortVector r i ^ 2 = 4 := by
    simpa only [sq] using griessShortVector_norm_sq r
  calc (1 : ℝ) = 1 / 4 * ∑ i, griessShortVector r i ^ 2 := by rw [hn]; norm_num
    _ = ∑ i, 1 / 4 * griessShortVector r i ^ 2 := Finset.mul_sum _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      split_ifs <;> norm_num

/-- The preferred odd integral vector: minus three at coordinate zero and one elsewhere. -/
private theorem proto_integral (i : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inr (0, 0))) i = if i = 0 then -3 else 1 := by
  have h0 : golayEncodedMask 0 = 0 := by decide
  simp [griessShortIntegral, h0]

/-- Pair addresses: avoiding coordinate zero gives `2 - 2 qSign c σ`, otherwise `10 ± 6`. -/
private theorem pair_form (s : Fin 2) (p : Fin 276) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inl (s, p)) c) generatedOddAxis =
      if (griessCoordinatePair p).1 = 0 then
        10 - 8 * qSign c * ((if s = 0 then 1 else -1) * (-3 / 4))
      else 2 - 8 * qSign c * ((if s = 0 then 1 else -1) * (1 / 4)) := by
  rw [generatedFeasibleAmbient_odd_form, odd_pair_coordinate]
  have hab := griessCoordinatePair_ne p
  have hlt : (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
    (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  have hb0 : (griessCoordinatePair p).2 ≠ 0 := by
    intro h
    rw [h] at hlt
    exact absurd hlt (Fin.not_lt_zero _)
  have hsum : ∑ i, (1 / 4 + if i = 0 then (2 : ℝ) else 0) *
      griessShortVector (Sum.inl (s, p)) i ^ 2 =
      2 * ((1 / 4 + if (griessCoordinatePair p).1 = 0 then (2 : ℝ) else 0) +
        (1 / 4 + if (griessCoordinatePair p).2 = 0 then (2 : ℝ) else 0)) := by
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
    split_ifs <;> norm_num
  rw [hsum, mul_assoc 2, generatedFeasibleAmbient_shortVector_mul, proto_integral,
    proto_integral]
  simp only [hb0, ite_false]
  split_ifs <;> norm_num

/-- The decidable form of orthogonality at pair addresses. -/
private def pairZero (s : Fin 2) (a : Fin 24) (c : ZMod 2) : Prop :=
  a ≠ 0 ∧ (c = 0 ↔ s = 0)

private instance (s : Fin 2) (a : Fin 24) (c : ZMod 2) : Decidable (pairZero s a c) := by
  unfold pairZero
  infer_instance

private theorem pair_zero_iff (s : Fin 2) (p : Fin 276) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inl (s, p)) c) generatedOddAxis = 0 ↔
      pairZero s (griessCoordinatePair p).1 c := by
  rw [pair_form]
  unfold pairZero
  rcases (show c = 0 ∨ c = 1 by fin_cases c <;> simp) with rfl | rfl <;>
  fin_cases s <;>
  by_cases ha : (griessCoordinatePair p).1 = 0 <;>
  simp [ha] <;> norm_num

/-- Exactly 506 actual pair addresses are orthogonal to the odd prototype. -/
private theorem pair_card :
    (Finset.univ.filter fun q : (Fin 2 × Fin 276) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inl q.1) q.2) generatedOddAxis = 0).card = 506 := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [pair_zero_iff]
  have he (s : Fin 2) : (∑ p : Fin 276, ∑ c : ZMod 2,
      if pairZero s (griessCoordinatePair p).1 c then 1 else 0) =
      ∑ q ∈ griessCoordinatePairs, ∑ c : ZMod 2, if pairZero s q.1 c then 1 else 0 := by
    rw [← Finset.sum_coe_sort griessCoordinatePairs]
    exact Fintype.sum_equiv griessCoordinatePairEquiv _ _ fun _ => rfl
  simp_rw [he]
  decide +kernel

private theorem octad_card :
    (Finset.univ.filter fun q : (Fin 759 × Fin 64) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inl q.1)) q.2) generatedOddAxis = 0).card =
      0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  rw [generatedFeasibleAmbient_odd_form, odd_octad_coordinate]
  have h := weight_sum_ge (Sum.inr (Sum.inl q.1))
  intro h0
  linarith

private theorem odd_card :
    (Finset.univ.filter fun q : (Fin 2048 × Fin 24) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inr q.1)) q.2) generatedOddAxis = 0).card =
      0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  rw [generatedFeasibleAmbient_odd_form, odd_odd_coordinate]
  have h := weight_sum_ge (Sum.inr (Sum.inr q.1))
  intro h0
  linarith

set_option maxRecDepth 1000000 in
-- Kernel checking of the three-family split unfolds the finite address type deeply.
private theorem total_card :
    (Finset.univ.filter fun p : GriessShortIndex × ZMod 2 =>
      griessForm (conwayShortAxis p.1 p.2) generatedOddAxis = 0).card = 506 := by
  have h := generatedFeasibleAmbient_short_filter_card (fun r c =>
    griessForm (conwayShortAxis r c) generatedOddAxis = 0)
  rw [pair_card, octad_card, odd_card] at h
  exact h

/-- Exactly 506 actual signed-short axes are orthogonal to the actual odd prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_odd :
    generatedFeasibleAmbientAxisZeroCount generatedOddAxis = 506 := by
  rw [generatedFeasibleAmbientAxisZeroCount_eq_card]
  exact total_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
