/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual inverse-U conjugate probe for Norton V polar phases. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQPolarTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortUpperPairs

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Binary coordinates of the genuine inverse-U conjugate of the actual Norton V. -/
def monsterNortonInverseUVBinary (i : Fin 24) : ZMod 2 :=
  if (0x3fc40e : ℕ).testBit i.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check every actual inverse-U probe coordinate through the complete frozen Q evaluator.
/-- The displayed inverse probe is the exact binary image in the actual local model. -/
theorem monsterNortonInverseUVBinary_actual :
    toAdd (spinConjugation (monsterNortonUFiber⁻¹).val.1 y555NortonVQ).base =
      monsterNortonInverseUVBinary := by
  rw [monsterNortonUQInverseFastImage_eq]
  unfold monsterNortonUQInverseFastImage monsterNortonCoordinateEvaluation
  rw [qCentral_mul_base, monsterNortonVBinaryCoordinates_actual]
  funext i
  revert i
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check both original pair families at all eleven physical pair coordinates.
/-- The actual inverse-U probe has the original family-zero V phase on either preferred
pair family. -/
theorem monsterNortonInverseUVPairPolar_actual (k : Fin 11) (s : Fin 2) :
    qBeta monsterNortonInverseUVBinary
      (toAdd (monsterNortonShortQ (Sum.inl (s, monsterNortonEvenShortPairIndex k))).base) +
    qBeta (toAdd (monsterNortonShortQ (Sum.inl (s, monsterNortonEvenShortPairIndex k))).base)
      monsterNortonInverseUVBinary = monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩ := by
  unfold monsterNortonShortQ
  simp only [griessShortIntegral, monsterNortonEvenShortPairIndex,
    griessPairIndex_coordinates, monsterNortonEvenShortPairCoordinate_positive, ite_true]
  revert k s
  decide +kernel

/-- Pulling the genuine V polar phase through actual forward U uses the exact inverse probe. -/
theorem monsterNortonVPhase_forwardU (q : Q) :
    monsterNortonQPolar y555NortonVQ (spinConjugation monsterNortonUFiber.val.1 q) =
      qBeta monsterNortonInverseUVBinary (toAdd q.base) +
        qBeta (toAdd q.base) monsterNortonInverseUVBinary := by
  have h := monsterNortonQPolar_inverse_input monsterNortonUFiber.val.1⁻¹ y555NortonVQ q
  change monsterNortonQPolar y555NortonVQ (spinConjugation monsterNortonUFiber.val.1 q) =
    monsterNortonQPolar (spinConjugation (monsterNortonUFiber⁻¹).val.1 y555NortonVQ) q at h
  unfold monsterNortonQPolar at h
  rw [monsterNortonInverseUVBinary_actual] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
