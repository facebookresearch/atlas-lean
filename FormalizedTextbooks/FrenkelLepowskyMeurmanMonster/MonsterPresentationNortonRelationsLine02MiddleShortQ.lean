/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual preferred Q labels for every finite middle short entry. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleShortParity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The coefficient-zero actual lift specified by the packed input mask. -/
def monsterNortonLine02MiddleInputQ (a : Fin 8) (e : Fin 64) : Q :=
  ⟨ofAdd (fun j : Fin 24 =>
    if (monsterNortonLine02MiddleInputMask a e).testBit j.val then 1 else 0), 1⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Check every hyperbolic coordinate after transporting the already checked genuine basis parity.
/-- Each packed input mask is precisely its full actual preferred short lift. -/
theorem monsterNortonLine02MiddleInputQ_actual (a : Fin 8) (e : Fin 64) :
    monsterNortonShortQ (monsterNortonLine02MiddleInput a e) =
      monsterNortonLine02MiddleInputQ a e := by
  unfold monsterNortonShortQ monsterNortonLine02MiddleInputQ
  rw [monsterNortonLine02MiddleInputIntegral_actual]
  have hp : integerParity (monsterNortonLeechCoordinates
      (monsterNortonLine02MiddleInputIntegral a e)) =
        fun j : Fin 24 =>
          if (monsterNortonLine02MiddleInputParity a e).testBit j.val then 1 else 0 :=
    funext (monsterNortonLine02MiddleInputParity_actual a e)
  rw [hp]
  clear hp
  apply NormalizedCocycleExtension.Extension.ext
  · funext j
    revert a e j
    decide +kernel
  · rfl

/-- The coefficient-zero actual lift specified by the packed output mask. -/
def monsterNortonLine02MiddleOutputQ (a : Fin 8) (e : Fin 64) : Q :=
  ⟨ofAdd (fun j : Fin 24 =>
    if (monsterNortonLine02MiddleOutputMask a e).testBit j.val then 1 else 0), 1⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Check every hyperbolic coordinate after transporting the already checked genuine basis parity.
/-- Each packed output mask is precisely its full actual preferred short lift. -/
theorem monsterNortonLine02MiddleOutputQ_actual (a : Fin 8) (e : Fin 64) :
    monsterNortonShortQ (monsterNortonLine02MiddleOutput a e) =
      monsterNortonLine02MiddleOutputQ a e := by
  unfold monsterNortonShortQ monsterNortonLine02MiddleOutputQ
  rw [monsterNortonLine02MiddleOutputIntegral_actual]
  have hp : integerParity (monsterNortonLeechCoordinates
      (monsterNortonLine02MiddleOutputIntegral a e)) =
        fun j : Fin 24 =>
          if (monsterNortonLine02MiddleOutputParity a e).testBit j.val then 1 else 0 :=
    funext (monsterNortonLine02MiddleOutputParity_actual a e)
  rw [hp]
  clear hp
  apply NormalizedCocycleExtension.Extension.ext
  · funext j
    revert a e j
    decide +kernel
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
