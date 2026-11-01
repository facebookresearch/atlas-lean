/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Phase-complete actual squared-U images of all twenty-three original preferred short units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02FirstUData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoQImageCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFirstU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Actual full central phases of the twenty-three preferred squared-U outputs. -/
def monsterNortonLine02FirstUPhase : Fin 23 → ZMod 2 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]

/-- The phase-complete finite evaluator of the genuine squared spin conjugation. -/
def monsterNortonLine02QFastImage (q : Q) : Q :=
  monsterNortonCoordinateEvaluation monsterNortonUTwoQGeneratorImage q

/-- All full Q inputs use the checked actual twenty-four generator images. -/
theorem monsterNortonLine02QFastImage_actual (q : Q) :
    spinConjugation (monsterNortonUFiber.val.1 ^ 2) q = monsterNortonLine02QFastImage q :=
  monsterNortonCoordinateEvaluation_eq _ _ monsterNortonUTwoQGeneratorImage_actual q

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- All binary coordinates and central phases of the twenty-three actual short lifts are checked.
/-- Every full squared-U image is the listed preferred source lift with its true central phase. -/
theorem monsterNortonLine02FirstU_Q_image (k : Fin 23) :
    spinConjugation (monsterNortonUFiber.val.1 ^ 2)
      (monsterNortonShortQ (monsterNortonEvenShortBasis k)) =
        qCentral (monsterNortonLine02FirstUPhase k) *
          monsterNortonShortQ (monsterNortonLine02FirstUOutput k) := by
  rw [monsterNortonLine02QFastImage_actual]
  unfold monsterNortonShortQ
  rw [monsterNortonEvenShortIntegral_actual, monsterNortonLine02FirstUIntegral_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext i
    revert k i
    decide +kernel
  · apply toAdd.injective
    revert k
    decide +kernel

private theorem fiber_square_spin (f : localFiberSubgroup) :
    (f ^ 2).val.1 = f.val.1 ^ 2 := rfl

private theorem generated_fiber_apply (f : localFiberSubgroup) (x : GriessSpace) :
    (localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f)).val x =
      localGriessRepresentation f x := rfl

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp
    ((LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _))

private theorem short_smul (r : GriessShortIndex) (c : ℝ) :
    griessConwayDecode (0, (c • Pi.single r 1, 0)) =
      c • griessConwayDecode (0, (Pi.single r 1, 0)) :=
  shortLift.map_smul c (Pi.single r 1)

set_option maxRecDepth 10000 in
/-- The literal actual squared Norton word transports every entire preferred short unit. -/
theorem monsterNortonLine02FirstU_actual (k : Fin 23) :
    (y555NortonActualU ^ 2).val (monsterNortonPureShort (monsterNortonEvenShortBasis k)) =
      qSign (monsterNortonLine02FirstUPhase k) •
        monsterNortonPureShort (monsterNortonLine02FirstUOutput k) := by
  have hq : spinConjugation (monsterNortonUFiber ^ 2).val.1
      (monsterNortonShortQ (monsterNortonEvenShortBasis k)) =
        qCentral (monsterNortonLine02FirstUPhase k) *
          monsterNortonShortQ (monsterNortonLine02FirstUOutput k) := by
    rw [fiber_square_spin]
    exact monsterNortonLine02FirstU_Q_image k
  have h := monsterNortonGriessShortBasis_of_Q_image (monsterNortonUFiber ^ 2)
    (monsterNortonEvenShortBasis k) (monsterNortonLine02FirstUOutput k)
      (monsterNortonLine02FirstUPhase k) hq
  have hg : localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup
      (monsterNortonUFiber ^ 2)) = y555NortonActualU ^ 2 := by
    simpa only [zpow_ofNat] using monsterNortonUFiber_generated_zpow (2 : ℤ)
  rw [← generated_fiber_apply, hg] at h
  rw [short_smul] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
