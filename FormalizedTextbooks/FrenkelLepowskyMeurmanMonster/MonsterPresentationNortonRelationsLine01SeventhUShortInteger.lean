/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Integer evaluation of every genuine tenth-state odd-short coordinate with its full phase. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUShortLookup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full integer coefficient of an actual tenth-state source term. -/
def monsterNortonLine01SeventhUShortIntegerCoefficient (jp : Fin 16 × Fin 32) : ℤ :=
  monsterNortonLine01OctadSeventhCoefficientLookup jp.1
    (monsterNortonLine01OctadSignLabel jp.2) *
    nortonUIntegerSign (monsterNortonLine01ShortInversePhase
      (monsterNortonLine01OctadSourceA jp.1 jp.2) (monsterNortonLine01OctadSourceK jp.1 jp.2))

/-- The direct integer numerator of every original tenth-state short coordinate. -/
def monsterNortonLine01SeventhUShortIntegerNumerator (r : GriessShortIndex) : ℤ :=
  if monsterNortonLine01SeventhUShortSupport r then
    monsterNortonLine01SeventhUShortIntegerCoefficient (monsterNortonLine01SeventhUShortLookup r)
      else 0

/-- The integer coefficient is exactly the actual real phase-corrected coefficient. -/
theorem monsterNortonLine01SeventhUShortIntegerCoefficient_real (jp : Fin 16 × Fin 32) :
    (monsterNortonLine01SeventhUShortIntegerCoefficient jp : ℝ) =
      monsterNortonLine01SeventhUShortCoefficient jp := by
  simp only [monsterNortonLine01SeventhUShortIntegerCoefficient, Int.cast_mul,
    nortonUIntegerSign_real, monsterNortonLine01SeventhUShortCoefficient]

/-- All actual tenth-state short coordinates equal their integer numerator divided by 512. -/
theorem monsterNortonLine01SeventhUShortInteger_actual (r : GriessShortIndex) :
    monsterNortonLine01SeventhUShortCoordinates r =
      (1 / 512 : ℝ) * (monsterNortonLine01SeventhUShortIntegerNumerator r : ℝ) := by
  rw [monsterNortonLine01SeventhUShortLookup_actual]
  simp only [monsterNortonLine01SeventhUShortIntegerNumerator, Int.cast_ite,
    monsterNortonLine01SeventhUShortIntegerCoefficient_real, Int.cast_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
