/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer scalars of the complete preferred-short forward packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQPolarVImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFifthSixth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual input V phase expressed in its certified finite binary coordinates. -/
def monsterNortonEvenShortInputVPhase (k : Fin 23) (e : Fin 64) : ZMod 2 :=
  qBeta monsterNortonVBinaryCoordinates (toAdd (monsterNortonEvenShortInverseUInputQ k e).base) +
    qBeta (toAdd (monsterNortonEvenShortInverseUInputQ k e).base) monsterNortonVBinaryCoordinates

/-- The actual output V phase pulled back along U to the certified original input. -/
def monsterNortonEvenShortOutputVPhase (k : Fin 23) (e : Fin 64) : ZMod 2 :=
  qBeta monsterNortonUVBinary (toAdd (monsterNortonEvenShortInverseUInputQ k e).base) +
    qBeta (toAdd (monsterNortonEvenShortInverseUInputQ k e).base) monsterNortonUVBinary

/-- The finite input phase agrees with the actual preferred-short conjugation phase. -/
theorem monsterNortonEvenShortInputVPhase_actual (k : Fin 23) (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUInput k e) =
      monsterNortonEvenShortInputVPhase k e := by
  unfold monsterNortonVShortPhase monsterNortonEvenShortInputVPhase
  rw [monsterNortonVBinaryCoordinates_actual, monsterNortonEvenShortInverseUInputQ_actual]

/-- The finite output phase retains the exact inverse-U polar transport. -/
theorem monsterNortonEvenShortOutputVPhase_actual (k : Fin 23) (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonEvenShortInverseUOutput k e) =
      monsterNortonEvenShortOutputVPhase k e := by
  rw [monsterNortonInverseUOutputV_phase, monsterNortonEvenShortInverseUInputQ_actual]
  rfl

/-- The integer numerator of each genuine sixth-step short coefficient. -/
def monsterNortonEvenShortSixthInteger (k : Fin 23) (e : Fin 64) : ℤ :=
  monsterNortonOctadInverseCoefficient e (monsterNortonEvenShortFirstUOctadSign k) *
    nortonUIntegerSign (monsterNortonEvenShortInputVPhase k e) *
    nortonUIntegerSign (monsterNortonEvenShortInverseUPhase k e) *
    nortonUIntegerSign (monsterNortonEvenShortOutputVPhase k e)

/-- The full actual sixth coefficient is the displayed integer divided by eight. -/
theorem monsterNortonEvenShortSixthInteger_actual (k : Fin 23) (e : Fin 64) :
    monsterNortonEvenShortSixthCoefficient k e =
      (monsterNortonEvenShortSixthInteger k e : ℝ) / 8 := by
  unfold monsterNortonEvenShortSixthCoefficient monsterNortonEvenShortFifthCoefficient
    monsterNortonEvenShortSixthInteger
  rw [monsterNortonEvenShortInputVPhase_actual, monsterNortonEvenShortOutputVPhase_actual]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
