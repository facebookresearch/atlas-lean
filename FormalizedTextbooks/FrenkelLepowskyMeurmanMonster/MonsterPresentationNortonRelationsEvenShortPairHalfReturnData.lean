/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer whole-half pairings for eleven original preferred pair inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairsInversePhases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfCoefficientData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original physical pair index for ten lower-family inputs and the first upper input. -/
def monsterNortonPairReturnOriginal (q : Fin 11) : Fin 11 :=
  if q.val < 10 then q else 0

/-- The actual original preferred pair family of each return case. -/
def monsterNortonPairReturnFamily (q : Fin 11) : Fin 2 :=
  if q.val < 10 then 0 else 1

/-- The corresponding norm-one forward-half candidate in the twelve-entry table. -/
def monsterNortonPairReturnCandidate (q : Fin 11) : Fin 12 :=
  if q.val < 10 then ⟨q.val, by omega⟩ else 10

/-- Exact actual family-zero V phase as an integer scalar. -/
def monsterNortonPairReturnBaseSign (q : Fin 11) : ℤ :=
  nortonUIntegerSign (monsterNortonEvenShortInitialVPhase
    ⟨(monsterNortonPairReturnOriginal q).val, by omega⟩)

/-- Original preferred-family sign as an integer scalar. -/
def monsterNortonPairReturnFamilySign (q : Fin 11) : ℤ :=
  if q.val < 10 then 1 else -1

/-- The original physical numerator of U applied to the original source A pair. -/
def monsterNortonPairReturnSourceMatrixNumerator (q : Fin 11) (i j : Fin 24) : ℤ :=
  monsterNortonUNumerator1 i 0 *
      monsterNortonUNumerator1 j
        (monsterNortonEvenShortPairCoordinate (monsterNortonPairReturnOriginal q)) +
    monsterNortonUNumerator1 i
        (monsterNortonEvenShortPairCoordinate (monsterNortonPairReturnOriginal q)) *
      monsterNortonUNumerator1 j 0

/-- Numerator of actual U on each of the eight source A units in the forward-half packet. -/
def monsterNortonPairReturnHalfMatrixNumerator (q : Fin 11) (p : Fin 8)
    (i j : Fin 24) : ℤ :=
  monsterNortonUNumerator1 i (monsterNortonPairHalfPairFirst
      (monsterNortonPairReturnCandidate q) p) *
    monsterNortonUNumerator1 j (monsterNortonPairHalfPairSecond
      (monsterNortonPairReturnCandidate q) p) +
  monsterNortonUNumerator1 i (monsterNortonPairHalfPairSecond
      (monsterNortonPairReturnCandidate q) p) *
    monsterNortonUNumerator1 j (monsterNortonPairHalfPairFirst
      (monsterNortonPairReturnCandidate q) p)

/-- Exact short input scalar of every candidate term before actual U. -/
def monsterNortonPairReturnShortNumerator (q : Fin 11) : NortonPairHalfShortIndex → ℤ
  | Sum.inl (p, _) => monsterNortonPairHalfPairCCoefficient
      (monsterNortonPairReturnCandidate q) p
  | Sum.inr (d, e) => monsterNortonPairHalfOctadCoefficient
      (monsterNortonPairReturnCandidate q) d e

/-- Numerator over thirty-two of each reached unit's full inverse-sixth pairing. -/
def monsterNortonPairReturnInverseShortGram (q : Fin 11)
    (i : NortonPairHalfShortIndex) : ℤ :=
  let n := monsterNortonPairHalfUPoolStorage (monsterNortonPairReturnCandidate q) i
  let k := monsterNortonPairReturnOriginal q
  if monsterNortonPairHalfUPoolOutputKind n = 0 then
    monsterNortonPairReturnBaseSign q *
      (if monsterNortonPairHalfUPoolOutputPairSign n = 0 then 1 else -1) *
        monsterNortonPairReturnSourceMatrixNumerator q
          (monsterNortonPairHalfUPoolOutputPairFirst n)
          (monsterNortonPairHalfUPoolOutputPairSecond n)
  else 2 * monsterNortonPairReturnFamilySign q * monsterNortonPairReturnBaseSign q *
    ((if monsterNortonEvenShortFirstUOctadCodes ⟨k.val, by omega⟩ =
        monsterNortonPairHalfUPoolOctadCode (monsterNortonPairHalfUPoolOutputOctadChoice n)
      then monsterNortonOctadPositiveInteger (monsterNortonPairHalfUPoolOutputOctadSign n)
        (monsterNortonEvenShortFirstUOctadSign ⟨k.val, by omega⟩) else 0) +
    (if monsterNortonEvenShortUpperUOctadCodes k =
        monsterNortonPairHalfUPoolOctadCode (monsterNortonPairHalfUPoolOutputOctadChoice n)
      then monsterNortonOctadPositiveInteger (monsterNortonPairHalfUPoolOutputOctadSign n)
        (monsterNortonEvenShortUpperUOctadSign k) else 0))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 32000000 in
-- Check all eleven exact physical diagonal matrix contributions.
/-- Every matrix contribution has exact numerator 512 at denominator 8192. -/
theorem monsterNortonPairReturnMatrixPairing_integer (q : Fin 11) :
    monsterNortonPairReturnBaseSign q *
      (∑ p : Fin 8, monsterNortonPairHalfPairCoefficient (monsterNortonPairReturnCandidate q) p *
        ∑ j : Fin 24, monsterNortonPairReturnHalfMatrixNumerator q p j j *
          monsterNortonPairReturnSourceMatrixNumerator q j j) = 512 := by
  revert q
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 128000000 in
-- Check all eleven complete 240-term original short contributions.
/-- Every short contribution has exact numerator 480 at denominator 512. -/
theorem monsterNortonPairReturnShortPairing_integer (q : Fin 11) :
    (∑ i : NortonPairHalfShortIndex, monsterNortonPairReturnShortNumerator q i *
      monsterNortonPairReturnInverseShortGram q i) = 480 := by
  revert q
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
