/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual squared-U transport of the eight complementary preferred pair units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddlePlusUData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all binary coordinates and central coefficients of the eight complementary images.
/-- Each full actual squared-U complementary image is the indicated positive octad lift. -/
theorem monsterNortonLine02MiddlePlusU_Q_image (a : Fin 8) :
    spinConjugation (monsterNortonUFiber.val.1 ^ 2)
      (monsterNortonShortQ (monsterNortonLine02MiddlePlusInput a)) =
        monsterNortonShortQ (monsterNortonLine02MiddlePlusOutput a) := by
  rw [monsterNortonLine02QFastImage_actual]
  unfold monsterNortonShortQ
  rw [monsterNortonLine02MiddlePlusInputIntegral_actual,
    monsterNortonLine02MiddlePlusOutputIntegral_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    revert a j
    decide +kernel
  · apply toAdd.injective
    revert a
    decide +kernel

private theorem fiber_square_spin (f : localFiberSubgroup) :
    (f ^ 2).val.1 = f.val.1 ^ 2 := rfl

private theorem generated_fiber_apply (f : localFiberSubgroup) (x : GriessSpace) :
    (localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f)).val x =
      localGriessRepresentation f x := rfl

set_option maxRecDepth 10000 in
/-- Literal squared U transports each whole complementary preferred unit with its positive phase. -/
theorem monsterNortonLine02MiddlePlusU_actual (a : Fin 8) :
    (y555NortonActualU ^ 2).val
      (monsterNortonPureShort (monsterNortonLine02MiddlePlusInput a)) =
        monsterNortonPureShort (monsterNortonLine02MiddlePlusOutput a) := by
  have hq : spinConjugation (monsterNortonUFiber ^ 2).val.1
      (monsterNortonShortQ (monsterNortonLine02MiddlePlusInput a)) =
        qCentral 0 * monsterNortonShortQ (monsterNortonLine02MiddlePlusOutput a) := by
    rw [fiber_square_spin, show qCentral 0 = (1 : Q) from rfl, one_mul]
    exact monsterNortonLine02MiddlePlusU_Q_image a
  have h := monsterNortonGriessShortBasis_of_Q_image (monsterNortonUFiber ^ 2)
    (monsterNortonLine02MiddlePlusInput a) (monsterNortonLine02MiddlePlusOutput a) 0 hq
  have hg : localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup
      (monsterNortonUFiber ^ 2)) = y555NortonActualU ^ 2 := by
    simpa only [zpow_ofNat] using monsterNortonUFiber_generated_zpow (2 : ℤ)
  rw [← generated_fiber_apply, hg] at h
  simpa only [qSign_zero, one_smul, monsterNortonPureShort] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
