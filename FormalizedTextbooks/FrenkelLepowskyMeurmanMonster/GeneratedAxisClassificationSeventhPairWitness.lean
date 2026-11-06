/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhPairWitnessData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityProduct

/-! The finite inverse-coordinate witnesses exclude the original pair family. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine integral short action has the same unavoidable global sign as its real action. -/
theorem generatedSeventh_short_integral_sign (e : leechIsomSubgroup) (r : GriessShortIndex) :
    (leechIntegralAction e (griessShortLatticeVector r)).val =
      griessShortIntegral (griessShortPermutation e r) ∨
    (leechIntegralAction e (griessShortLatticeVector r)).val =
      -griessShortIntegral (griessShortPermutation e r) := by
  have hv := griessShortPermutation_vector e r
  have he := leechIntegralAction_embedding e (griessShortLatticeVector r)
  change leechCoordinateEmbedding _ = e.val (griessShortVector r) at he
  rcases hv with hv | hv
  · left
    apply leechCoordinateEmbedding_injective
    exact he.trans hv
  · right
    apply leechCoordinateEmbedding_injective
    rw [he, hv]
    ext i
    simp [leechCoordinateEmbedding, griessShortVector, neg_div]

/-- The cached numerator is the actual inverse matrix applied to the original pair coordinates. -/
theorem generatedSeventh_pair_witness_numerator (s : Fin 2) (p : Fin 276) :
    (generatedSeventhInverseNumerator *ᵥ griessShortIntegral (Sum.inl (s, p)))
      (generatedSeventhPairWitness s (griessCoordinatePair p).1 (griessCoordinatePair p).2) =
        generatedSeventhPairWitnessNumerator s
          (griessCoordinatePair p).1 (griessCoordinatePair p).2 := by
  simp only [Matrix.mulVec, dotProduct, griessShortIntegral, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_zero, mul_one]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, generatedSeventhPairWitnessNumerator]
  split_ifs <;> ring

/-- Every excluded target pair has an inverse short label outside the genuine pair family. -/
theorem generatedSeventh_pair_inverse_not_pair (s : Fin 2) (p : Fin 276)
    (hp : ¬ generatedSeventhPairExceptional s
      (griessCoordinatePair p).1 (griessCoordinatePair p).2) (t : Fin 2) (q : Fin 276) :
    griessShortPermutation (generatedSeventhLocalFiber.val.2⁻¹) (Sum.inl (s, p)) ≠
      Sum.inl (t, q) := by
  intro hq
  let i := generatedSeventhPairWitness s (griessCoordinatePair p).1 (griessCoordinatePair p).2
  have hl := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hl
  have hc := generatedSeventh_pair_witness_certificate s
    (griessCoordinatePair p).1 (griessCoordinatePair p).2 hl hp
  have he := generatedSeventh_inverse_integral_coordinate
    (griessShortLatticeVector (Sum.inl (s, p))) i
  change 8 * _ = (generatedSeventhInverseNumerator *ᵥ
    griessShortIntegral (Sum.inl (s, p))) i at he
  rw [show (generatedSeventhInverseNumerator *ᵥ griessShortIntegral (Sum.inl (s, p))) i =
    generatedSeventhPairWitnessNumerator s (griessCoordinatePair p).1
      (griessCoordinatePair p).2 from generatedSeventh_pair_witness_numerator s p] at he
  have hv := generatedSeventh_short_integral_sign (generatedSeventhLocalFiber.val.2⁻¹)
    (Sum.inl (s, p))
  rw [hq] at hv
  have hs := griessPair_coordinate_square t q i
  have hn := griessCoordinatePair_ne q
  have hz : griessShortIntegral (Sum.inl (t, q)) i ^ 2 = 0 ∨
      griessShortIntegral (Sum.inl (t, q)) i ^ 2 = 16 := by
    by_cases ha : i = (griessCoordinatePair q).1
    · exact Or.inr (by simpa only [ha, hn, ite_true, ite_false, add_zero] using hs)
    · by_cases hb : i = (griessCoordinatePair q).2
      · exact Or.inr (by simpa only [hb, hn.symm, ite_true, ite_false, zero_add] using hs)
      · exact Or.inl (by simpa only [ha, hb, ite_false, add_zero] using hs)
  rcases hv with hv | hv <;> have hi := congrFun hv i
  · rw [hi] at he
    rcases hz with hz | hz
    · exact hc.1 (by rw [← he, mul_pow]; norm_num only [neg_sq, hz])
    · exact hc.2 (by rw [← he, mul_pow]; norm_num only [neg_sq, hz])
  · change _ = -griessShortIntegral (Sum.inl (t, q)) i at hi
    rw [hi] at he
    rcases hz with hz | hz
    · exact hc.1 (by rw [← he, mul_pow]; norm_num only [neg_sq, hz])
    · exact hc.2 (by rw [← he, mul_pow]; norm_num only [neg_sq, hz])

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
