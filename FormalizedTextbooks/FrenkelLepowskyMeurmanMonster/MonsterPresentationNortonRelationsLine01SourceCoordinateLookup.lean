/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Verified inverse lookup of the genuine source code and physical column coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseParity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A finite inverse of the sixty-four actual source codes. -/
def monsterNortonLine01SourceCodeLookup (d : Fin 2048) : Fin 64 :=
  ⟨((if monsterNortonBitParity ((d.val ^^^ 233) &&& 1293) then 1 else 0) +
    (if monsterNortonBitParity ((d.val ^^^ 233) &&& 11) then 2 else 0) +
    (if monsterNortonBitParity ((d.val ^^^ 233) &&& 1290) then 4 else 0) +
    (if monsterNortonBitParity ((d.val ^^^ 233) &&& 270) then 8 else 0) +
    (if monsterNortonBitParity ((d.val ^^^ 233) &&& 1282) then 16 else 0) +
    (if monsterNortonBitParity ((d.val ^^^ 233) &&& 1) then 32 else 0)) % 64,
    Nat.mod_lt _ (by norm_num)⟩

/-- Actual source code labels are recovered with their exact original index. -/
theorem monsterNortonLine01SourceCodeLookup_label (a : Fin 64) :
    monsterNortonLine01SourceCodeLookup (monsterNortonLine01ShortInputCode a) = a := by
  revert a
  decide +kernel

/-- A finite inverse of the sixteen actual supported physical columns. -/
def monsterNortonLine01SourcePhysicalLookup : Fin 24 → Fin 16 :=
  ![0, 1, 0, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 0, 12, 0, 0, 13, 14, 0, 15, 0]

/-- Each actual physical column is recovered with its original index. -/
theorem monsterNortonLine01SourcePhysicalLookup_label (k : Fin 16) :
    monsterNortonLine01SourcePhysicalLookup (monsterNortonLine01ShortPhysicalColumn k) = k := by
  revert k
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
