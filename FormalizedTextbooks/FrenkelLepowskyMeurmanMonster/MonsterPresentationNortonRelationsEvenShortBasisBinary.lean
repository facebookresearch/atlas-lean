/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Checked actual binary coordinates and inverse basis matrix for twenty-three even short units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortBasisData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortBasis

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Binary masks of the actual twenty-three preferred pair/octet shortest vectors. -/
def monsterNortonEvenShortBasisMasks : Fin 23 → ℕ :=
  ![0x600000, 0x500000, 0x700000, 0x40f000, 0x8f000, 0x4f000, 0x40e000, 0x2e000,
    0x1e000, 0x40d000, 0x40b000, 0x600800, 0x403003, 0x405005, 0x408007, 0x409009,
    0xf010, 0xf020, 0xe040, 0xe080, 0x401100, 0x401200, 0x400]

/-- The finite vectors represented by those masks. -/
def monsterNortonEvenShortBasisBinary (k : Fin 23) : Fin 24 → ZMod 2 :=
  fun i => if (monsterNortonEvenShortBasisMasks k).testBit i.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Kernel-check all actual integer-short coordinates, including the twenty-fourth zero coordinate.
/-- Every finite basis vector is the actual Q binary image of its original preferred short label. -/
theorem monsterNortonEvenShortBasisBinary_actual (k : Fin 23) :
    toAdd (monsterNortonShortQ (monsterNortonEvenShortBasis k)).base =
      monsterNortonEvenShortBasisBinary k := by
  unfold monsterNortonShortQ
  rw [monsterNortonEvenShortIntegral_actual]
  funext i
  revert i
  fin_cases k <;> decide +kernel

/-- Inverse coefficient masks expressing coordinate units in this actual binary basis. -/
def monsterNortonEvenShortBasisInverseMasks : Fin 23 → ℕ :=
  ![0x7040, 0x6207, 0x5407, 0xf648, 0x1000f, 0x2000f, 0x40047, 0x80047,
    0x10004f, 0x20004f, 0x400000, 0x801, 0x48, 0x208, 0x408, 0x647,
    0x147, 0xc7, 0x2f, 0x1f, 0x5, 0x6, 0x7]

/-- The exact binary inverse coefficients. -/
def monsterNortonEvenShortBasisInverse (i k : Fin 23) : ZMod 2 :=
  if (monsterNortonEvenShortBasisInverseMasks i).testBit k.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the full inverse product over F₂, for every displayed coordinate and every output slot.
/-- These original short vectors span every one of the first twenty-three actual Q coordinates. -/
theorem monsterNortonEvenShortBasisInverse_certificate (i : Fin 23) :
    (∑ k : Fin 23, monsterNortonEvenShortBasisInverse i k • monsterNortonEvenShortBasisBinary k) =
      Pi.single (Fin.castAdd 1 i) (1 : ZMod 2) := by
  funext j
  revert i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
