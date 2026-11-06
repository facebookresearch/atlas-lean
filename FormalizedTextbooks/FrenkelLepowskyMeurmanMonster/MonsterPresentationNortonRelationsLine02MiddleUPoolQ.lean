/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine full Q dictionaries of the middle squared-U finite transport pool. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleUPoolParity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Positive full lift of the actual packed input hyperbolic coordinates. -/
def monsterNortonLine02MiddleUPoolInputQ (i : Fin 1264) : Q :=
  ⟨ofAdd (fun j : Fin 24 =>
    if (monsterNortonLine02MiddleUPoolInputMask i).testBit j.val then 1 else 0), 1⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 256000000 in
-- Transport every already checked actual integral parity into genuine hyperbolic coordinates.
/-- Every packed input mask is precisely its full positive preferred short lift. -/
theorem monsterNortonLine02MiddleUPoolInputQ_actual (i : Fin 1264) :
    monsterNortonShortQ (monsterNortonLine02MiddleUPoolInput i) =
      monsterNortonLine02MiddleUPoolInputQ i := by
  unfold monsterNortonShortQ monsterNortonLine02MiddleUPoolInputQ
  rw [monsterNortonLine02MiddleUPoolInputIntegral_actual]
  have hp : integerParity (monsterNortonLeechCoordinates
      (monsterNortonLine02MiddleUPoolInputIntegral i)) =
        fun j : Fin 24 =>
          if (monsterNortonLine02MiddleUPoolInputParity i).testBit j.val then 1 else 0 :=
    funext (monsterNortonLine02MiddleUPoolInputParity_actual i)
  rw [hp]
  clear hp
  apply NormalizedCocycleExtension.Extension.ext
  · funext j
    revert i j
    decide +kernel
  · rfl

/-- Positive full lift of the actual packed output hyperbolic coordinates. -/
def monsterNortonLine02MiddleUPoolOutputQ (i : Fin 1264) : Q :=
  ⟨ofAdd (fun j : Fin 24 =>
    if (monsterNortonLine02MiddleUPoolOutputMask i).testBit j.val then 1 else 0), 1⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 256000000 in
-- Transport every already checked actual integral parity into genuine hyperbolic coordinates.
/-- Every packed output mask is precisely its full positive preferred short lift. -/
theorem monsterNortonLine02MiddleUPoolOutputQ_actual (i : Fin 1264) :
    monsterNortonShortQ (monsterNortonLine02MiddleUPoolOutput i) =
      monsterNortonLine02MiddleUPoolOutputQ i := by
  unfold monsterNortonShortQ monsterNortonLine02MiddleUPoolOutputQ
  rw [monsterNortonLine02MiddleUPoolOutputIntegral_actual]
  have hp : integerParity (monsterNortonLeechCoordinates
      (monsterNortonLine02MiddleUPoolOutputIntegral i)) =
        fun j : Fin 24 =>
          if (monsterNortonLine02MiddleUPoolOutputParity i).testBit j.val then 1 else 0 :=
    funext (monsterNortonLine02MiddleUPoolOutputParity_actual i)
  rw [hp]
  clear hp
  apply NormalizedCocycleExtension.Extension.ext
  · funext j
    revert i j
    decide +kernel
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
