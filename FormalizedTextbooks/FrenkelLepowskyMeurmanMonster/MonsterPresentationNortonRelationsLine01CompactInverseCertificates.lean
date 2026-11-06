/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Assembly of bounded kernel-checked actual inverse compact output certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactInverseBatch0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactInverseBatch1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactInverseBatch2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactInverseBatch3

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem inverse_coefficient_batch (b : Fin 4) (k : Fin 4) (p : Fin 128) :
    monsterNortonUCompactInverseNumerator
      (monsterNortonLine01CompactInputVector ⟨4 * b.val + k.val, by omega⟩)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient ⟨4 * b.val + k.val, by omega⟩ p := by
  fin_cases b
  · exact monsterNortonLine01CompactInverse_coefficient_batch0 k p
  · exact monsterNortonLine01CompactInverse_coefficient_batch1 k p
  · exact monsterNortonLine01CompactInverse_coefficient_batch2 k p
  · exact monsterNortonLine01CompactInverse_coefficient_batch3 k p

/-- Each displayed output coefficient is computed by the genuine inverse compact numerator. -/
theorem monsterNortonLine01CompactInverse_coefficient (k : Fin 16) (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector k)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient k p := by
  let b : Fin 4 := ⟨k.val / 4, by omega⟩
  let r : Fin 4 := ⟨k.val % 4, Nat.mod_lt _ (by omega)⟩
  have hk : k = ⟨4 * b.val + r.val, by omega⟩ := by
    apply Fin.ext
    dsimp [b, r]
    omega
  rw [hk]
  exact inverse_coefficient_batch b r p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
