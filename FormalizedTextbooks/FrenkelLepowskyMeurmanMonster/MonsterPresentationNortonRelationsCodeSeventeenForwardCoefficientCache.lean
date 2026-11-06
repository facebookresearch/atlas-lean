/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual source phases of the octad-seventeen forward-half packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQOctadCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem kind_ne_zero (e : Fin 64) :
    monsterNortonEvenShortInverseUKind 17 e ≠ 0 := by
  revert e
  decide +kernel

/-- The finite exact preferred output lift of each source Fourier term. -/
def monsterNortonCodeSeventeenForwardOutputQ (e : Fin 64) : Q :=
  if monsterNortonEvenShortInverseUKind 17 e = 1 then
    let a := monsterNortonEvenShortInverseUOctadSlot 17 e
    monsterNortonOctadQSource (monsterNortonEvenShortInverseUOctadCodes a)
      (monsterNortonEvenShortInverseUOctadPositions a)
        (monsterNortonEvenShortInverseUOctadSign 17 e)
  else monsterNortonShortQSource (Sum.inr (Sum.inr
    (monsterNortonEvenShortInverseUOddCode 17 e, monsterNortonEvenShortInverseUOddPosition 17 e)))

/-- The computed source lift is exactly the actual original short lift. -/
theorem monsterNortonCodeSeventeenForwardOutputQ_actual (e : Fin 64) :
    monsterNortonShortQSource (monsterNortonEvenShortInverseUOutput 17 e) =
      monsterNortonCodeSeventeenForwardOutputQ e := by
  unfold monsterNortonEvenShortInverseUOutput monsterNortonCodeSeventeenForwardOutputQ
  simp only [kind_ne_zero, ite_false]
  by_cases h : monsterNortonEvenShortInverseUKind 17 e = 1
  · simp only [h, ite_true]
    apply monsterNortonOctadQSource_actual
    exact monsterNortonEvenShortInverseUOctad_coordinate _
  · simp only [h, ite_false]

/-- The actual V polar phase evaluated on a full preferred source lift. -/
def monsterNortonCodeSeventeenVSourcePhase (q : Q) : ZMod 2 :=
  qBeta (toAdd y555NortonVQ.base) (toAdd q.base) +
    qBeta (toAdd q.base) (toAdd y555NortonVQ.base)

/-- The full integer forward coefficient retains every V, Fourier, and inverse-U sign. -/
def monsterNortonCodeSeventeenForwardCoefficient (e : Fin 64) : ℤ :=
  nortonUIntegerSign (monsterNortonEvenShortInitialVPhase 17) *
    monsterNortonOctadInverseCoefficient e (monsterNortonEvenShortFirstUOctadSign 17) *
    nortonUIntegerSign (monsterNortonCodeSeventeenVSourcePhase
      (monsterNortonEvenShortInverseUInputQ 17 e)) *
    nortonUIntegerSign (monsterNortonEvenShortInverseUPhase 17 e) *
    nortonUIntegerSign (monsterNortonCodeSeventeenVSourcePhase
      (monsterNortonCodeSeventeenForwardOutputQ e))

/-- All complete signed coefficients of the actual forward packet. -/
def monsterNortonCodeSeventeenForwardCoefficientCache : Fin 64 → ℤ :=
  ![1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, -1, -1, 1,
    1, 1, 1, 1, 1, -1, -1, 1,
    1, -1, -1, 1, 1, -1, -1, 1,
    1, -1, -1, -1, 1, -1, -1, -1,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1,
    -1, -1, -1, 1, -1, -1, -1, 1]

set_option maxHeartbeats 16000000 in
-- Check all sixty-four complete actual preferred-lift phase expressions.
/-- Every cached integer is checked against the whole genuine source phase expression. -/
theorem monsterNortonCodeSeventeenForwardCoefficient_cache (e : Fin 64) :
    monsterNortonCodeSeventeenForwardCoefficient e =
      monsterNortonCodeSeventeenForwardCoefficientCache e := by
  revert e
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
