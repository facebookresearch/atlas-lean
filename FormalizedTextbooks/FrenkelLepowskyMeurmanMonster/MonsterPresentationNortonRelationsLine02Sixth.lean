/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete sixth distance-two states, keeping the actual Q phase on spin and short factors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02Fifth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQTensorCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Q transport of a whole rank-one tensor acts on precisely its spin factor. -/
theorem monsterNortonQ_tensor_rank_one (q : Q) (b : Fin 24 → ℝ) (a : SpinSpace) :
    (qIntoGenerated q).val (monsterNortonTensorRankOne b a) =
      monsterNortonTensorRankOne b (spinOperator q a) := by
  change (qIntoGenerated q).val
    (monsterNortonTensorLift (conwayTensorCoordinates (a ⊗ₜ[ℝ] b))) = _
  rw [monsterNortonQ_tensor_coordinates]
  apply congrArg monsterNortonTensorLift
  funext t i
  simp only [conwayTensorCoordinates_tmul]
  have h : (fun u => a u * b i) = b i • a := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  rw [h, map_smul]
  exact mul_comm _ _

private theorem q_rank_one_integer (q : Q) (b : Fin 24 → ℝ)
    (c d : ℝ) (v : NortonUIntegerVector) :
    (qIntoGenerated q).val (monsterNortonTensorRankOne b (c • (d • nortonUIntegerEmbed v))) =
      monsterNortonTensorRankOne b (c • (d • nortonUIntegerEmbed (nortonUIntegerQ q v))) := by
  rw [monsterNortonQ_tensor_rank_one]
  have hs : spinOperator q (c • (d • nortonUIntegerEmbed v)) =
      c • (d • nortonUIntegerEmbed (nortonUIntegerQ q v)) := by
    simp only [(spinOperator q).map_smul]
    exact congrArg (fun a : SpinSpace => c • (d • a)) (nortonUIntegerQ_embed q v)
  exact congrArg (monsterNortonTensorRankOne b) hs

/-- A sixth packet keeps every actual short phase and the true Q-translated spin numerator. -/
noncomputable def monsterNortonLine02SixthPacket (k : Fin 23) : GriessSpace :=
  if monsterNortonLine02FirstUIsOdd k then
    monsterNortonTensorRankOne (((monsterNortonUFiber⁻¹) ^ 2).val.2.val
      (Pi.single (monsterNortonLine02FirstUOddPosition k) 1))
      ((qSign (golayMaskWeight
        (golayEncodedMask (monsterNortonLine02FirstUOddCode k).val) / 4 : ℕ) /
          Real.sqrt 2) • ((1 / 4 : ℝ) • nortonUIntegerEmbed
            (nortonUIntegerQ y555NortonVQ (monsterNortonUTwoCompactInverseNumerator
              (nortonUIntegerQ y555NortonVQ
                (monsterNortonSourceZInteger (monsterNortonLine02FirstUOddCode k)))))))
  else
    let d := monsterNortonOctadIndex (monsterNortonLine02FirstUOctadCodes k)
      (monsterNortonLine02FirstUOctad_weight k)
    ∑ e : Fin 64,
      (((monsterNortonOctadInverseCoefficient e (monsterNortonLine02FirstUOctadSign k) : ℝ) /
        8) * qSign (monsterNortonVShortPhase (Sum.inr (Sum.inl (d, e)))) *
          qSign (monsterNortonUTwoInverseShortPhase (Sum.inr (Sum.inl (d, e)))) *
          qSign (monsterNortonVShortPhase
            (monsterNortonUTwoInverseShortOutput (Sum.inr (Sum.inl (d, e)))))) •
              monsterNortonPureShort
                (monsterNortonUTwoInverseShortOutput (Sum.inr (Sum.inl (d, e))))

/-- Literal V transports the whole fifth packet to its explicit sixth packet. -/
theorem monsterNortonLine02SixthPacket_actual (k : Fin 23) :
    y555NortonV.val (monsterNortonLine02FifthPacket k) =
      monsterNortonLine02SixthPacket k := by
  unfold monsterNortonLine02FifthPacket monsterNortonLine02SixthPacket
  by_cases h : monsterNortonLine02FirstUIsOdd k = true
  · simp only [ite_eq_left h]
    rw [y555NortonV]
    exact q_rank_one_integer y555NortonVQ _ _ _ _
  · simp only [ite_eq_right h]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [map_smul, monsterNortonV_pure_short, smul_smul]

/-- All twenty-three original preferred inputs have this complete sixth literal state. -/
theorem monsterNortonLine02FirstSix_actual (k : Fin 23) :
    y555NortonV.val (((y555NortonActualU ^ 2)⁻¹).val (y555NortonV.val (sExtra.symm
      ((y555NortonActualU ^ 2).val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis k))))))) =
      qSign (monsterNortonLine02FirstThreePhase k) • monsterNortonLine02SixthPacket k := by
  rw [monsterNortonLine02FirstFive_actual, map_smul, monsterNortonLine02SixthPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
