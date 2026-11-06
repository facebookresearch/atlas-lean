/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket00Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket01Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket02Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket03Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket04Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket05Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket06Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket07Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket08Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket09Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket10Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket11Coordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignWhole

/-! Twelve complete actual original source sign lifts in the fifth axis stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All twelve actual corrected source sign words fix every supported octad coordinate. -/
theorem generatedFifth_sign_corrected_octad (k : Fin 12) (j : Fin 56) (e : Fin 64) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber k))
      generatedFifthAxis)).2.1 (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) =
        (griessConwayEncode generatedFifthAxis).2.1
          (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) := by
  fin_cases k
  · exact generatedFifthSignShortPacket00_coordinate j e
  · exact generatedFifthSignShortPacket01_coordinate j e
  · exact generatedFifthSignShortPacket02_coordinate j e
  · exact generatedFifthSignShortPacket03_coordinate j e
  · exact generatedFifthSignShortPacket04_coordinate j e
  · exact generatedFifthSignShortPacket05_coordinate j e
  · exact generatedFifthSignShortPacket06_coordinate j e
  · exact generatedFifthSignShortPacket07_coordinate j e
  · exact generatedFifthSignShortPacket08_coordinate j e
  · exact generatedFifthSignShortPacket09_coordinate j e
  · exact generatedFifthSignShortPacket10_coordinate j e
  · exact generatedFifthSignShortPacket11_coordinate j e

/-- The twelve actual corrected sign words preserve the entire original short block. -/
theorem generatedFifth_sign_corrected_short (k : Fin 12) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber k))
      generatedFifthAxis)).2.1 = (griessConwayEncode generatedFifthAxis).2.1 :=
  generatedFifth_sign_short_fixed_of_octads k (generatedFifth_sign_corrected_octad k)

/-- Every displayed actual source sign lift fixes the full original fifth axis. -/
theorem generatedFifth_sign_corrected_full (k : Fin 12) :
    rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber k)) generatedFifthAxis =
      generatedFifthAxis :=
  generatedFifth_sign_full_fixed_of_short k (generatedFifth_sign_corrected_short k)

/-- The full-axis lifts have the genuine twelve source Golay sign projections. -/
theorem generatedFifth_sign_corrected_projection (k : Fin 12) :
    projH (localFiberIntoH (generatedFifthSignCorrectedFiber k)) =
      (QuotientGroup.mk
        (golaySignIsometry (sourceGeneratedSignCode (generatedFifthSignCode k))) : Co1) := by
  rw [generatedFifthSignCorrectedFiber, map_mul, map_mul]
  change 1 * projH (localFiberIntoH (generatedFifthSignFiber (generatedFifthSignCode k) 0)) = _
  rw [one_mul, generatedFifth_sign_fiber_local, generatedFifth_sign_local_projection]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
