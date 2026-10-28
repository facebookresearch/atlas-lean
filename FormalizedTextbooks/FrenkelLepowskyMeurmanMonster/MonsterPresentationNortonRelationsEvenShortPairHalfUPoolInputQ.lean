/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual preferred-Q inputs of the deduplicated short U transport pool. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolInputParity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Full coefficient-zero lift encoded by each stored genuine input hyperbolic mask. -/
def monsterNortonPairHalfUPoolInputQ (i : Fin 1552) : Q :=
  ⟨ofAdd (fun j : Fin 24 =>
    if (monsterNortonPairHalfUPoolInputMask i).testBit j.val then 1 else 0), 1⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 128000000 in
-- Check every hyperbolic coordinate after the actual integral Leech parity has been transported.
/-- Every pool mask is its complete actual original preferred input, including the zero phase. -/
theorem monsterNortonPairHalfUPoolInputQ_actual (i : Fin 1552) :
    monsterNortonShortQ (monsterNortonPairHalfUPoolInput i) =
      monsterNortonPairHalfUPoolInputQ i := by
  unfold monsterNortonShortQ monsterNortonPairHalfUPoolInputQ
  rw [monsterNortonPairHalfUPoolInputIntegral_actual]
  have hpar : integerParity (monsterNortonLeechCoordinates
      (monsterNortonPairHalfUPoolInputIntegral i)) =
        fun j : Fin 24 =>
          if (monsterNortonPairHalfUPoolInputParity i).testBit j.val then 1 else 0 :=
    funext (monsterNortonPairHalfUPoolInputParity_actual i)
  rw [hpar]
  clear hpar
  apply NormalizedCocycleExtension.Extension.ext
  · funext j
    revert i j
    decide +kernel
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
