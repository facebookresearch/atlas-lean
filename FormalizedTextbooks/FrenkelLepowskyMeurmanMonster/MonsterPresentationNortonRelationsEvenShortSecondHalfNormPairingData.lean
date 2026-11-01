/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer numerator of the sparse forward-half pairing with the sixth inverse half. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original physical numerator of U applied to the source A unit at coordinates zero and two. -/
def monsterNortonSecondSourceMatrixNumerator (i j : Fin 24) : ℤ :=
  monsterNortonUNumerator1 i 0 * monsterNortonUNumerator1 j 2 +
    monsterNortonUNumerator1 i 2 * monsterNortonUNumerator1 j 0

/-- Physical numerator of U on each of the eight source A units in the sparse half packet. -/
def monsterNortonSecondHalfMatrixNumerator (p : Fin 8) (i j : Fin 24) : ℤ :=
  monsterNortonUNumerator1 i (monsterNortonSecondHalfPairFirst p) *
      monsterNortonUNumerator1 j (monsterNortonSecondHalfPairSecond p) +
    monsterNortonUNumerator1 i (monsterNortonSecondHalfPairSecond p) *
      monsterNortonUNumerator1 j (monsterNortonSecondHalfPairFirst p)

/-- Integer source scalar of each short term before applying U. -/
def monsterNortonSecondHalfShortNumerator : NortonSecondHalfShortIndex → ℤ
  | Sum.inl _ => -1
  | Sum.inr (d, e) => monsterNortonSecondHalfOctadCoefficient d e

/-- Numerator, over thirty-two, of each reached short unit's inverse-half pairing. -/
def monsterNortonSecondHalfInverseShortGram (i : NortonSecondHalfShortIndex) : ℤ :=
  let k := monsterNortonSecondHalfShortStorage i
  if monsterNortonSecondHalfUKind k = 0 then
    -(if monsterNortonSecondHalfUPairSign k = 0 then 1 else -1) *
      monsterNortonSecondSourceMatrixNumerator (monsterNortonSecondHalfUPairFirst k)
        (monsterNortonSecondHalfUPairSecond k)
  else -2 * monsterNortonOctadPositiveInteger (monsterNortonSecondHalfUOctadSign k)
    (if monsterNortonSecondHalfUOctadChoice k = 0 then 57 else 45)

/-- Exact integer matrix contribution at denominator8192. -/
theorem monsterNortonSecondHalfMatrixPairing_integer :
    -(∑ p : Fin 8, monsterNortonSecondHalfPairCoefficient p *
      ∑ j : Fin 24, monsterNortonSecondHalfMatrixNumerator p j j *
        monsterNortonSecondSourceMatrixNumerator j j) = 512 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all240actual short output dictionary pairings as a finite integer sum.
/-- Exact integer short contribution at denominator512. -/
theorem monsterNortonSecondHalfShortPairing_integer :
    (∑ i : NortonSecondHalfShortIndex, monsterNortonSecondHalfShortNumerator i *
      monsterNortonSecondHalfInverseShortGram i) = 480 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
