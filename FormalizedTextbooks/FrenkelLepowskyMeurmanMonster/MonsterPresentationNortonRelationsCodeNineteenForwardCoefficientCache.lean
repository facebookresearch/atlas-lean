/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual source phases of the octad-nineteen forward-half packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQOctadCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem kind_ne_zero (e : Fin 64) :
    monsterNortonEvenShortInverseUKind 19 e ≠ 0 := by
  revert e
  decide +kernel

/-- The finite exact preferred output lift of each source Fourier term. -/
def monsterNortonCodeNineteenForwardOutputQ (e : Fin 64) : Q :=
  if monsterNortonEvenShortInverseUKind 19 e = 1 then
    let a := monsterNortonEvenShortInverseUOctadSlot 19 e
    monsterNortonOctadQSource (monsterNortonEvenShortInverseUOctadCodes a)
      (monsterNortonEvenShortInverseUOctadPositions a)
        (monsterNortonEvenShortInverseUOctadSign 19 e)
  else monsterNortonShortQSource (Sum.inr (Sum.inr
    (monsterNortonEvenShortInverseUOddCode 19 e, monsterNortonEvenShortInverseUOddPosition 19 e)))

/-- The computed source lift is exactly the actual original short lift. -/
theorem monsterNortonCodeNineteenForwardOutputQ_actual (e : Fin 64) :
    monsterNortonShortQSource (monsterNortonEvenShortInverseUOutput 19 e) =
      monsterNortonCodeNineteenForwardOutputQ e := by
  unfold monsterNortonEvenShortInverseUOutput monsterNortonCodeNineteenForwardOutputQ
  simp only [kind_ne_zero, ite_false]
  by_cases h : monsterNortonEvenShortInverseUKind 19 e = 1
  · simp only [h, ite_true]
    apply monsterNortonOctadQSource_actual
    exact monsterNortonEvenShortInverseUOctad_coordinate _
  · simp only [h, ite_false]

/-- The actual V polar phase evaluated on a full preferred source lift. -/
def monsterNortonCodeNineteenVSourcePhase (q : Q) : ZMod 2 :=
  qBeta (toAdd y555NortonVQ.base) (toAdd q.base) +
    qBeta (toAdd q.base) (toAdd y555NortonVQ.base)

/-- The full integer forward coefficient retains every V, Fourier, and inverse-U sign. -/
def monsterNortonCodeNineteenForwardCoefficient (e : Fin 64) : ℤ :=
  nortonUIntegerSign (monsterNortonEvenShortInitialVPhase 19) *
    monsterNortonOctadInverseCoefficient e (monsterNortonEvenShortFirstUOctadSign 19) *
    nortonUIntegerSign (monsterNortonCodeNineteenVSourcePhase
      (monsterNortonEvenShortInverseUInputQ 19 e)) *
    nortonUIntegerSign (monsterNortonEvenShortInverseUPhase 19 e) *
    nortonUIntegerSign (monsterNortonCodeNineteenVSourcePhase
      (monsterNortonCodeNineteenForwardOutputQ e))

/-- All complete signed coefficients of the actual forward packet. -/
def monsterNortonCodeNineteenForwardCoefficientCache : Fin 64 → ℤ :=
  ![1, -1, -1, 1, 1, 1, 1, -1,
    1, 1, 1, -1, 1, -1, -1, 1,
    1, 1, 1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, -1, -1, 1,
    1, -1, -1, 1, 1, -1, -1, -1,
    1, -1, -1, -1, 1, -1, -1, 1,
    1, -1, -1, -1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, 1, 1, 1]

set_option maxHeartbeats 16000000 in
-- Check all sixty-four complete actual preferred-lift phase expressions.
/-- Every cached integer is checked against the whole genuine source phase expression. -/
theorem monsterNortonCodeNineteenForwardCoefficient_cache (e : Fin 64) :
    monsterNortonCodeNineteenForwardCoefficient e =
      monsterNortonCodeNineteenForwardCoefficientCache e := by
  revert e
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
