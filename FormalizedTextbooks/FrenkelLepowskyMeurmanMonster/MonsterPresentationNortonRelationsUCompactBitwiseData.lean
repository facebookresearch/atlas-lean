/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Compact bitwise coordinate formulas checked against the actual Norton factors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Parity of a twelve-bit integer, evaluated without a field-valued sum. -/
def monsterNortonBitParity (n : ℕ) : Bool :=
  ([n.testBit 0,
    n.testBit 1,
    n.testBit 2,
    n.testBit 3,
    n.testBit 4,
    n.testBit 5,
    n.testBit 6,
    n.testBit 7,
    n.testBit 8,
    n.testBit 9,
    n.testBit 10,
    n.testBit 11]).foldl Bool.xor false

/-- The published actual binary matrix acting through twelve bit-parity rows. -/
def monsterNortonUCompactBitPermutation (k : Fin 2) (n : Fin 4096) : Fin 4096 :=
  ⟨(((if monsterNortonBitParity (n.val &&&
      monsterNortonUCompactPermutationRows k 0) then 1 else 0) +
    (if monsterNortonBitParity (n.val &&& monsterNortonUCompactPermutationRows k 1) then 2 else 0) +
    (if monsterNortonBitParity (n.val &&& monsterNortonUCompactPermutationRows k 2) then 4 else 0) +
    (if monsterNortonBitParity (n.val &&& monsterNortonUCompactPermutationRows k 3) then 8 else 0) +
    (if monsterNortonBitParity (n.val &&&
      monsterNortonUCompactPermutationRows k 4) then 16 else 0) +
    (if monsterNortonBitParity (n.val &&&
      monsterNortonUCompactPermutationRows k 5) then 32 else 0) +
    (if monsterNortonBitParity (n.val &&&
      monsterNortonUCompactPermutationRows k 6) then 64 else 0) +
    (if monsterNortonBitParity (n.val &&&
      monsterNortonUCompactPermutationRows k 7) then 128 else 0) +
    (if monsterNortonBitParity (n.val &&&
      monsterNortonUCompactPermutationRows k 8) then 256 else 0) +
    (if monsterNortonBitParity (n.val &&&
      monsterNortonUCompactPermutationRows k 9) then 512 else 0) +
    (if monsterNortonBitParity (n.val &&&
      monsterNortonUCompactPermutationRows k 10) then 1024 else 0) +
    (if monsterNortonBitParity (n.val &&&
      monsterNortonUCompactPermutationRows k 11) then 2048 else 0)) % 4096),
    Nat.mod_lt _ (by norm_num)⟩

/-- The published actual quadratic diagonal sign evaluated through bit parity. -/
def monsterNortonUCompactBitDiagonal (k : Fin 2) (n : Fin 4096) : ℤ :=
  if monsterNortonBitParity ((if n.val.testBit 0 then n.val &&&
      monsterNortonUCompactDiagonalRows k 0 else 0) ^^^
    (if n.val.testBit 1 then n.val &&& monsterNortonUCompactDiagonalRows k 1 else 0) ^^^
    (if n.val.testBit 2 then n.val &&& monsterNortonUCompactDiagonalRows k 2 else 0) ^^^
    (if n.val.testBit 3 then n.val &&& monsterNortonUCompactDiagonalRows k 3 else 0) ^^^
    (if n.val.testBit 4 then n.val &&& monsterNortonUCompactDiagonalRows k 4 else 0) ^^^
    (if n.val.testBit 5 then n.val &&& monsterNortonUCompactDiagonalRows k 5 else 0) ^^^
    (if n.val.testBit 6 then n.val &&& monsterNortonUCompactDiagonalRows k 6 else 0) ^^^
    (if n.val.testBit 7 then n.val &&& monsterNortonUCompactDiagonalRows k 7 else 0) ^^^
    (if n.val.testBit 8 then n.val &&& monsterNortonUCompactDiagonalRows k 8 else 0) ^^^
    (if n.val.testBit 9 then n.val &&& monsterNortonUCompactDiagonalRows k 9 else 0) ^^^
    (if n.val.testBit 10 then n.val &&& monsterNortonUCompactDiagonalRows k 10 else 0) ^^^
    (if n.val.testBit 11 then n.val &&&
      monsterNortonUCompactDiagonalRows k 11 else 0)) then -1 else 1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
