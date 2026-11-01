/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete fourth literal line-word states on all twenty-three preferred short units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortThird
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSourceZQCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp
    ((LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _))

/-- The genuine polar phase of the actual Norton V on any original short label. -/
noncomputable def monsterNortonVShortPhase (r : GriessShortIndex) : ZMod 2 :=
  qBeta (toAdd y555NortonVQ.base) (toAdd (monsterNortonShortQ r).base) +
    qBeta (toAdd (monsterNortonShortQ r).base) (toAdd y555NortonVQ.base)

/-- Literal V acts on every whole original short unit by this full actual polar phase. -/
theorem monsterNortonV_pure_short (r : GriessShortIndex) :
    y555NortonV.val (monsterNortonPureShort r) =
      qSign (monsterNortonVShortPhase r) • monsterNortonPureShort r := by
  have h := monsterNortonQ_griess_short_basis y555NortonVQ r
  have hs : griessConwayDecode (0, (qSign (monsterNortonVShortPhase r) • Pi.single r 1, 0)) =
      qSign (monsterNortonVShortPhase r) • monsterNortonPureShort r :=
    shortLift.map_smul (qSign (monsterNortonVShortPhase r)) (Pi.single r 1)
  exact h.trans hs

/-- Entire V image of a Fourier octad packet, including all sixty-four actual phases. -/
theorem monsterNortonV_octad_packet (d : Fin 759) (v : Fin 64 → ℝ) :
    y555NortonV.val (monsterNortonOctadShortVector d v) =
      ∑ e, (v e * qSign (monsterNortonVShortPhase (Sum.inr (Sum.inl (d, e))))) •
        monsterNortonPureShort (Sum.inr (Sum.inl (d, e))) := by
  rw [monsterNortonOctadShortVector_expansion, map_sum]
  simp only [map_smul, monsterNortonV_pure_short, smul_smul]

/-- The fourth packet contains sixty-four short units or two translated spin deltas. -/
noncomputable def monsterNortonEvenShortFourthPacket (k : Fin 23) : GriessSpace :=
  if monsterNortonEvenShortFirstUIsOdd k then
    monsterNortonTensorLift (conwaySpinColumn
      (monsterNortonSourceZQSpinImage y555NortonVQ (monsterNortonEvenShortFirstUOddCode k))
      (monsterNortonEvenShortFirstUOddPosition k))
  else
    let d := monsterNortonOctadIndex (monsterNortonEvenShortFirstUOctadCodes k)
      (monsterNortonEvenShortFirstUOctad_weight k)
    ∑ e : Fin 64,
      (((monsterNortonOctadInverseCoefficient e (monsterNortonEvenShortFirstUOctadSign k) : ℝ) /
        8) * qSign (monsterNortonVShortPhase (Sum.inr (Sum.inl (d, e))))) •
          monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))

/-- Literal V takes the whole third packet to the stated fourth packet. -/
theorem monsterNortonEvenShortFourthPacket_actual (k : Fin 23) :
    y555NortonV.val (monsterNortonEvenShortThirdPacket k) =
      monsterNortonEvenShortFourthPacket k := by
  unfold monsterNortonEvenShortThirdPacket monsterNortonEvenShortFourthPacket
  by_cases h : monsterNortonEvenShortFirstUIsOdd k = true
  · simp only [ite_eq_left h]
    exact monsterNortonQ_source_Z_explicit y555NortonVQ _ _
  · simp only [ite_eq_right h]
    exact monsterNortonV_octad_packet _ _

/-- Complete original-coordinate state after four literal V, U, inverse-triality, V steps. -/
theorem monsterNortonEvenShortFirstFour_actual (k : Fin 23) :
    y555NortonV.val (sExtra.symm (y555NortonActualU.val (y555NortonV.val
      (monsterNortonPureShort (monsterNortonEvenShortBasis k))))) =
      qSign (monsterNortonEvenShortInitialVPhase k) • monsterNortonEvenShortFourthPacket k := by
  rw [monsterNortonEvenShortFirstThree_actual, map_smul, monsterNortonEvenShortFourthPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
