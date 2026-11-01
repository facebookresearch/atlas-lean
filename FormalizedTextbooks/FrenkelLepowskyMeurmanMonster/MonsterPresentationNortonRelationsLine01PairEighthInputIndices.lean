/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Identifying the compact eighth input slots with the actual original pair and octad labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthShortInput
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhExpansion

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The first sixteen checked inputs are the two families of eight original adjacent pairs. -/
theorem monsterNortonLine01PairEighthInput_pair (s : Fin 2) (k : Fin 8) :
    monsterNortonLine01PairEighthShortInput ⟨8 * s.val + k.val, by omega⟩ =
      Sum.inl (s, monsterNortonLine01AdjacentPair k) := by
  have hk : 8 * s.val + k.val < 16 := by omega
  unfold monsterNortonLine01PairEighthShortInput
  rw [dite_eq_left hk]
  have hf : monsterNortonLine01PairEighthInputPairFirst
      ⟨8 * s.val + k.val, hk⟩ = (⟨2 * k.val, by omega⟩ : Fin 24) := by
    apply Fin.ext
    dsimp [monsterNortonLine01PairEighthInputPairFirst]
    omega
  have hs : monsterNortonLine01PairEighthInputPairSecond
      ⟨8 * s.val + k.val, hk⟩ = (⟨2 * k.val + 1, by omega⟩ : Fin 24) := by
    apply Fin.ext
    dsimp [monsterNortonLine01PairEighthInputPairSecond]
    omega
  have hfamily : (if 8 * s.val + k.val < 8 then (0 : Fin 2) else 1) = s := by
    fin_cases s <;> simp_all
  simp only [hf, hs]
  change Sum.inl ((if 8 * s.val + k.val < 8 then 0 else 1), _) = _
  rw [hfamily]
  rfl

/-- The remaining 224 inputs are exactly the fourteen supported original octad packets. -/
theorem monsterNortonLine01PairEighthInput_octad (a : Fin 14) (j : Fin 16) :
    monsterNortonLine01PairEighthShortInput ⟨16 + 16 * a.val + j.val, by omega⟩ =
      Sum.inr (Sum.inl (monsterNortonLine01PairBlockOctad a,
        monsterNortonLine01PairSeventhOctadSupport a j)) := by
  have hk : ¬16 + 16 * a.val + j.val < 16 := by omega
  unfold monsterNortonLine01PairEighthShortInput
  rw [dite_eq_right hk]
  have ha : monsterNortonLine01PairEighthInputOctadSlot
      ⟨16 + 16 * a.val + j.val, by omega⟩ hk = a := by
    apply Fin.ext
    dsimp [monsterNortonLine01PairEighthInputOctadSlot]
    omega
  have hj : monsterNortonLine01PairEighthInputSignSlot
      ⟨16 + 16 * a.val + j.val, by omega⟩ = j := by
    apply Fin.ext
    dsimp [monsterNortonLine01PairEighthInputSignSlot]
    omega
  simp only [ha, hj]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
