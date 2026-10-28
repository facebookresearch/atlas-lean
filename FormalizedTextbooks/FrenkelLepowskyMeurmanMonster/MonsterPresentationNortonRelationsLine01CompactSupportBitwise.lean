/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite support geometry for the exact bitwise inverse compact evaluator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactColumnData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The six Gaussian basis image masks under the actual published permutation zero. -/
def monsterNortonLine01CompactInputGaussianMask (a : Fin 64) : Fin 4096 :=
  ⟨((if a.val.testBit 0 then 3508 else 0) ^^^
    (if a.val.testBit 1 then 1254 else 0) ^^^
    (if a.val.testBit 2 then 1210 else 0) ^^^
    (if a.val.testBit 3 then 3328 else 0) ^^^
    (if a.val.testBit 4 then 3342 else 0) ^^^
    (if a.val.testBit 5 then 339 else 0)) % 4096, Nat.mod_lt _ (by norm_num)⟩

/-- The exact base preimage for the proposed output support, written in bitwise coordinates. -/
def monsterNortonLine01CompactBitPreimage (n : Fin 4096) : Fin 4096 :=
  ⟨((monsterNortonUCompactBitPermutation 0
    (monsterNortonUCompactBitPermutation 1 n)).val ^^^ 1024) % 4096,
    Nat.mod_lt _ (by norm_num)⟩

set_option maxHeartbeats 16000000 in
-- The check covers all 4096 output labels, including every label outside the catalogue.
/-- The output support equals precisely the input support of its base bitwise preimage. -/
theorem monsterNortonLine01CompactSupport_preimage (n : Fin 4096) :
    monsterNortonLine01CompactOutputSupport n ↔
      monsterNortonLine01CompactInputSupport (monsterNortonLine01CompactBitPreimage n) := by
  revert n
  decide +kernel

set_option maxHeartbeats 16000000 in
-- This checks the full 128 by 64 affine support action through the finite index catalogues.
/-- Every Gaussian image shift preserves the complete input support catalogue. -/
theorem monsterNortonLine01CompactSupport_gaussian (p : Fin 128) (a : Fin 64) :
    monsterNortonLine01CompactInputSupport
      ⟨((monsterNortonLine01CompactInputLabel p).val ^^^
        (monsterNortonLine01CompactInputGaussianMask a).val) % 4096,
          Nat.mod_lt _ (by norm_num)⟩ := by
  revert p a
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
