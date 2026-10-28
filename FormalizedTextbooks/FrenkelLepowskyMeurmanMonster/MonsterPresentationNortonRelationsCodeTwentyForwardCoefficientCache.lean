/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual source phases of the octad-twenty forward-half packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQOctadCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem kind_ne_zero (e : Fin 64) :
    monsterNortonEvenShortInverseUKind 20 e ≠ 0 := by
  revert e
  decide +kernel

/-- The finite exact preferred output lift of each source Fourier term. -/
def monsterNortonCodeTwentyForwardOutputQ (e : Fin 64) : Q :=
  if monsterNortonEvenShortInverseUKind 20 e = 1 then
    let a := monsterNortonEvenShortInverseUOctadSlot 20 e
    monsterNortonOctadQSource (monsterNortonEvenShortInverseUOctadCodes a)
      (monsterNortonEvenShortInverseUOctadPositions a)
        (monsterNortonEvenShortInverseUOctadSign 20 e)
  else monsterNortonShortQSource (Sum.inr (Sum.inr
    (monsterNortonEvenShortInverseUOddCode 20 e, monsterNortonEvenShortInverseUOddPosition 20 e)))

/-- The computed source lift is exactly the actual original short lift. -/
theorem monsterNortonCodeTwentyForwardOutputQ_actual (e : Fin 64) :
    monsterNortonShortQSource (monsterNortonEvenShortInverseUOutput 20 e) =
      monsterNortonCodeTwentyForwardOutputQ e := by
  unfold monsterNortonEvenShortInverseUOutput monsterNortonCodeTwentyForwardOutputQ
  simp only [kind_ne_zero, ite_false]
  by_cases h : monsterNortonEvenShortInverseUKind 20 e = 1
  · simp only [h, ite_true]
    apply monsterNortonOctadQSource_actual
    exact monsterNortonEvenShortInverseUOctad_coordinate _
  · simp only [h, ite_false]

/-- The actual V polar phase evaluated on a full preferred source lift. -/
def monsterNortonCodeTwentyVSourcePhase (q : Q) : ZMod 2 :=
  qBeta (toAdd y555NortonVQ.base) (toAdd q.base) +
    qBeta (toAdd q.base) (toAdd y555NortonVQ.base)

/-- The full integer forward coefficient retains every V, Fourier, and inverse-U sign. -/
def monsterNortonCodeTwentyForwardCoefficient (e : Fin 64) : ℤ :=
  nortonUIntegerSign (monsterNortonEvenShortInitialVPhase 20) *
    monsterNortonOctadInverseCoefficient e (monsterNortonEvenShortFirstUOctadSign 20) *
    nortonUIntegerSign (monsterNortonCodeTwentyVSourcePhase
      (monsterNortonEvenShortInverseUInputQ 20 e)) *
    nortonUIntegerSign (monsterNortonEvenShortInverseUPhase 20 e) *
    nortonUIntegerSign (monsterNortonCodeTwentyVSourcePhase
      (monsterNortonCodeTwentyForwardOutputQ e))

/-- All complete signed coefficients of the actual forward packet. -/
def monsterNortonCodeTwentyForwardCoefficientCache : Fin 64 → ℤ :=
  ![1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, -1, -1, 1,
    1, -1, -1, -1, 1, -1, -1, -1,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, 1, 1, 1, 1, -1, -1, 1,
    1, -1, -1, 1, 1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1,
    -1, -1, -1, 1, -1, -1, -1, 1]

set_option maxHeartbeats 16000000 in
-- Check all sixty-four complete actual preferred-lift phase expressions.
/-- Every cached integer is checked against the whole genuine source phase expression. -/
theorem monsterNortonCodeTwentyForwardCoefficient_cache (e : Fin 64) :
    monsterNortonCodeTwentyForwardCoefficient e =
      monsterNortonCodeTwentyForwardCoefficientCache e := by
  revert e
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
