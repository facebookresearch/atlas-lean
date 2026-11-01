/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual V polar bits on every inverse-U transported preferred short label. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQPolarTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFourth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsVBinaryCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The binary coordinates of the actual forward U conjugate of V. -/
def monsterNortonUVBinary (i : Fin 24) : ZMod 2 :=
  if (0x80100e : ℕ).testBit i.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Verify all 24 coordinates through the fully certified actual Norton Q evaluator.
/-- The displayed binary vector is the genuine forward U image of the actual V element. -/
theorem monsterNortonUVBinary_actual :
    toAdd (spinConjugation monsterNortonUFiber.val.1 y555NortonVQ).base =
      monsterNortonUVBinary := by
  rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq]
  unfold monsterNortonUQFastImage monsterNortonCoordinateEvaluation
  rw [qCentral_mul_base, monsterNortonVBinaryCoordinates_actual]
  funext i
  revert i
  decide +kernel

/-- V's exact phase on every inverse-U output is read on its original input using the U probe. -/
theorem monsterNortonInverseUOutputV_phase (k : Fin 23) (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUOutput k e) =
      qBeta monsterNortonUVBinary
        (toAdd (monsterNortonShortQ (monsterNortonEvenShortInverseUInput k e)).base) +
      qBeta (toAdd (monsterNortonShortQ (monsterNortonEvenShortInverseUInput k e)).base)
        monsterNortonUVBinary := by
  have h := monsterNortonQPolar_inverse_input monsterNortonUFiber.val.1 y555NortonVQ
    (monsterNortonShortQ (monsterNortonEvenShortInverseUInput k e))
  change monsterNortonQPolar y555NortonVQ
    (spinConjugation (monsterNortonUFiber⁻¹).val.1
      (monsterNortonShortQ (monsterNortonEvenShortInverseUInput k e))) = _ at h
  rw [monsterNortonEvenShortInverseU_Q_image] at h
  unfold monsterNortonQPolar at h
  rw [qCentral_mul_base, monsterNortonUVBinary_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
