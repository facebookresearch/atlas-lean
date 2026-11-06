/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual sixth odd-short numerator with its fully verified source phase cache. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OddSixthLookup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortSixthCoefficientData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhInteger

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The cached sixth odd-short integer phase, with zero outside its actual support. -/
def monsterNortonLine01OddSixthCached (d : Fin 2048) (i : Fin 24) : ℤ :=
  if monsterNortonLine01OddCodeSupport d ∧ i.val < 16 then
    monsterNortonLine01ShortSixthSourceCoefficientLookup
      (monsterNortonLine01OddSourceA (monsterNortonLine01OddCodeLookup d)
        (monsterNortonLine01OddPhysicalSlot i))
      (monsterNortonLine01OddSourceK (monsterNortonLine01OddCodeLookup d)
        (monsterNortonLine01OddPhysicalSlot i)) else 0

/-- The entire actual odd-short numerator is exactly its verified unique-source cached phase. -/
theorem monsterNortonLine01OddSixthCached_actual (d : Fin 2048) (i : Fin 24) :
    monsterNortonLine01OddSixthNumerator d i = monsterNortonLine01OddSixthCached d i := by
  rw [monsterNortonLine01OddSixthSourceLookup_actual]
  unfold monsterNortonLine01OddSixthSourceLookup monsterNortonLine01OddSixthCached
  split_ifs
  · rw [monsterNortonLine01ShortSixthSourceCoefficientLookup_actual]
  · rfl

/-- The seventh tensor integer formula using the proved source cache for its odd-short input. -/
def monsterNortonLine01TensorSeventhCachedNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by norm_num)⟩
  (if (golayEncodedMask d.val).testBit i.val then (-1 : ℤ) else 1) *
    (-nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (monsterNortonLine01TensorSixthIntegerNumerator ⟨d.val, by omega⟩ i -
          monsterNortonLine01TensorSixthIntegerNumerator ⟨d.val + 2048, by omega⟩ i) +
      64 * nortonUIntegerSign (golayLabelCoefficients n 11) *
        monsterNortonLine01OddSixthCached d i)

/-- The cached seventh tensor formula is exactly the entire actual seventh integer numerator. -/
theorem monsterNortonLine01TensorSeventhCachedNumerator_actual (n : Fin 4096) (i : Fin 24) :
    monsterNortonLine01TensorSeventhIntegerNumerator n i =
      monsterNortonLine01TensorSeventhCachedNumerator n i := by
  unfold monsterNortonLine01TensorSeventhIntegerNumerator
    monsterNortonLine01TensorSeventhCachedNumerator
  simp only [monsterNortonLine01OddSixthCached_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
