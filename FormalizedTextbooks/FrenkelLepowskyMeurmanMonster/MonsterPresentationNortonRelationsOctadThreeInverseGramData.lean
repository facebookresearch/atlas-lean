/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Integer Gram certificates for the actual code-three inverse half-word return. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadThreeInversePhases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUWholeData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Zero selects the physical pair family and one the octad family. -/
def monsterNortonOctadThreeUOutputKind : Fin 64 → ℕ :=
  ![
    1, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0, 1, 1, 1, 1,
    1, 0, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 0, 1,
    1, 1, 0, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 0, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 0,
    0, 1, 1, 1, 1, 1, 1, 1
  ]

/-- First sorted physical coordinate of each output pair. -/
def monsterNortonOctadThreeUOutputPairFirst : Fin 64 → Fin 24 :=
  ![
    0, 0, 0, 0, 9, 0, 0, 0,
    0, 0, 0, 4, 0, 0, 0, 0,
    0, 13, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 5, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 6, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 12,
    0, 0, 0, 0, 0, 0, 0, 0
  ]

/-- Second sorted physical coordinate of each output pair. -/
def monsterNortonOctadThreeUOutputPairSecond : Fin 64 → Fin 24 :=
  ![
    1, 1, 1, 1, 10, 1, 1, 1,
    1, 1, 1, 11, 1, 1, 1, 1,
    1, 22, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 19, 1,
    1, 1, 7, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 8, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 20,
    16, 1, 1, 1, 1, 1, 1, 1
  ]

/-- Original preferred sign of each output pair. -/
def monsterNortonOctadThreeUOutputPairSign : Fin 64 → Fin 2 :=
  ![
    0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1,
    1, 0, 0, 0, 0, 0, 0, 0
  ]

/-- Original output Golay code in the verified common dictionary. -/
def monsterNortonOctadThreeUOutputOctadChoice : Fin 64 → Fin 50 :=
  ![
    5, 20, 2, 47, 0, 46, 33, 44,
    44, 4, 21, 0, 22, 2, 20, 34,
    46, 0, 19, 4, 20, 5, 22, 28,
    28, 47, 34, 20, 33, 19, 0, 21,
    33, 19, 0, 21, 2, 22, 5, 45,
    45, 34, 47, 2, 46, 0, 19, 4,
    47, 28, 45, 5, 44, 4, 21, 0,
    0, 46, 33, 44, 34, 45, 28, 22
  ]

/-- Original even sign of each output octad unit. -/
def monsterNortonOctadThreeUOutputOctadSign : Fin 64 → Fin 64 :=
  ![
    16, 1, 20, 1, 0, 1, 1, 1,
    31, 16, 31, 0, 31, 10, 31, 1,
    6, 0, 20, 6, 18, 3, 6, 17,
    4, 12, 24, 12, 12, 10, 0, 12,
    61, 1, 0, 1, 62, 1, 31, 1,
    31, 61, 31, 32, 31, 0, 31, 31,
    18, 34, 20, 12, 18, 9, 18, 0,
    0, 24, 48, 12, 36, 10, 55, 24
  ]

/-- Every displayed output pair uses the actual strictly increasing coordinate convention. -/
theorem monsterNortonOctadThreeUOutputPair_lt (e : Fin 64) :
    monsterNortonOctadThreeUOutputPairFirst e < monsterNortonOctadThreeUOutputPairSecond e := by
  revert e
  decide +kernel

/-- All finite output labels coincide with their complete phase-checked actual U outputs. -/
theorem monsterNortonOctadThreeUOutput_dictionary (e : Fin 64) :
    monsterNortonOctadThreeUOutput e =
      if monsterNortonOctadThreeUOutputKind e = 0 then
        Sum.inl (monsterNortonOctadThreeUOutputPairSign e,
          griessPairIndex (monsterNortonOctadThreeUOutputPairFirst e)
            (monsterNortonOctadThreeUOutputPairSecond e)
            (ne_of_lt (monsterNortonOctadThreeUOutputPair_lt e)))
      else Sum.inr (Sum.inl
        (monsterNortonOctadIndex
          (monsterNortonPairHalfUPoolOctadCode (monsterNortonOctadThreeUOutputOctadChoice e))
          (monsterNortonPairHalfUPoolOctad_weight (monsterNortonOctadThreeUOutputOctadChoice e)),
          monsterNortonOctadThreeUOutputOctadSign e)) := by
  fin_cases e <;> rfl

/-- Numerators for pairing a full transported A unit with each actual extra-output unit. -/
def monsterNortonOctadThreeInverseMatrixGram (p : Fin 8) (e : Fin 64) : ℤ :=
  if monsterNortonOctadThreeUOutputKind e = 0 then
    monsterNortonUNumerator1 (monsterNortonOctadThreeUOutputPairFirst e)
      (monsterNortonPairHalfPairFirst 11 p) *
        monsterNortonUNumerator1 (monsterNortonOctadThreeUOutputPairSecond e)
          (monsterNortonPairHalfPairSecond 11 p) +
    monsterNortonUNumerator1 (monsterNortonOctadThreeUOutputPairFirst e)
      (monsterNortonPairHalfPairSecond 11 p) *
        monsterNortonUNumerator1 (monsterNortonOctadThreeUOutputPairSecond e)
          (monsterNortonPairHalfPairFirst 11 p)
  else 0

/-- Original integer coefficients of all 240 actual U-transported candidate short units. -/
def monsterNortonOctadThreeReturnShortNumerator : NortonPairHalfShortIndex → ℤ
  | Sum.inl (p, _) => monsterNortonPairHalfPairCCoefficient 11 p
  | Sum.inr (d, e) => monsterNortonPairHalfOctadCoefficient 11 d e

/-- Exact eight-scaled short Gram entries, retaining the positive Fourier row sign. -/
def monsterNortonOctadThreeInverseShortGram (e : Fin 64)
    (i : NortonPairHalfShortIndex) : ℤ :=
  let k := monsterNortonPairHalfUPoolStorage 11 i
  if monsterNortonOctadThreeUOutputKind e = 0 then
    if monsterNortonPairHalfUPoolOutputKind k = 0 ∧
      monsterNortonPairHalfUPoolOutputPairFirst k = monsterNortonOctadThreeUOutputPairFirst e ∧
      monsterNortonPairHalfUPoolOutputPairSecond k = monsterNortonOctadThreeUOutputPairSecond e
    then if monsterNortonOctadThreeUOutputPairSign e = 0 then 4 else -4
    else 0
  else
    if monsterNortonPairHalfUPoolOutputKind k ≠ 0 ∧
      monsterNortonPairHalfUPoolOctadCode (monsterNortonPairHalfUPoolOutputOctadChoice k) =
        monsterNortonPairHalfUPoolOctadCode (monsterNortonOctadThreeUOutputOctadChoice e)
    then monsterNortonOctadPositiveInteger (monsterNortonPairHalfUPoolOutputOctadSign k)
      (monsterNortonOctadThreeUOutputOctadSign e)
    else 0

set_option maxHeartbeats 16000000 in
-- Check the complete finite integer matrix pairing.
/-- The matrix packet contributes the exact integer numerator 128. -/
theorem monsterNortonOctadThreeReturnMatrix_integer :
    (∑ p : Fin 8, monsterNortonPairHalfPairCoefficient 11 p *
      ∑ e : Fin 64, monsterNortonOctadThreeInverseIntegerCoefficient e *
        monsterNortonOctadThreeInverseMatrixGram p e) = 128 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every supported short coefficient against the complete inverse Fourier packet.
/-- The short packet contributes the exact integer numerator 960. -/
theorem monsterNortonOctadThreeReturnShort_integer :
    (∑ i : NortonPairHalfShortIndex, monsterNortonOctadThreeReturnShortNumerator i *
      ∑ e : Fin 64, monsterNortonOctadThreeInverseIntegerCoefficient e *
        monsterNortonOctadThreeInverseShortGram e i) = 960 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
