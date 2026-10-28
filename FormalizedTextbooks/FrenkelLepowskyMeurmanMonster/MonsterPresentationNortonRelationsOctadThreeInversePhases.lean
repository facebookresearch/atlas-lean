/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual V phases on both sides of the original code-three U images. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadThreeInverseSixth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsInverseUVProbe

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Actual V phases on the original code-three inputs. -/
def monsterNortonOctadThreeInverseInputPhase : Fin 64 → ZMod 2 :=
  ![
    1, 0, 1, 1, 1, 1, 0, 1,
    1, 1, 0, 1, 0, 1, 0, 0,
    1, 1, 0, 1, 0, 1, 0, 0,
    0, 1, 0, 0, 0, 0, 1, 0,
    0, 0, 1, 0, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 1, 0, 1,
    1, 0, 1, 1, 1, 1, 0, 1,
    1, 1, 0, 1, 0, 1, 0, 0
  ]

/-- Actual V phases on their preferred U outputs. -/
def monsterNortonOctadThreeInverseOutputPhase : Fin 64 → ZMod 2 :=
  ![
    0, 0, 1, 1, 1, 1, 0, 0,
    1, 1, 0, 0, 0, 0, 1, 1,
    1, 1, 0, 0, 0, 0, 1, 1,
    0, 0, 1, 1, 1, 1, 0, 0,
    0, 0, 1, 1, 1, 1, 0, 0,
    1, 1, 0, 0, 0, 0, 1, 1,
    1, 1, 0, 0, 0, 0, 1, 1,
    0, 0, 1, 1, 1, 1, 0, 0
  ]

/-- Signed inverse-sixth numerators before division by eight. -/
def monsterNortonOctadThreeInverseIntegerCoefficient : Fin 64 → ℤ :=
  ![
    1, -1, -1, -1, -1, -1, -1, 1,
    -1, -1, -1, 1, -1, 1, 1, 1,
    -1, -1, -1, 1, -1, 1, 1, 1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, -1, -1, 1, -1, 1, 1, 1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    1, 1, 1, -1, 1, -1, -1, -1
  ]

/-- The complete positive input lift uses its verified original source mask. -/
def monsterNortonOctadThreeUInputQ (e : Fin 64) : Q :=
  Sum.elim monsterNortonPairHalfUPoolInputQ monsterNortonOctadThreeSupplementInputQ
    (monsterNortonOctadThreeUStorage e)

/-- Every finite lift is the actual original preferred input, including its phase. -/
theorem monsterNortonOctadThreeUInputQ_actual (e : Fin 64) :
    monsterNortonShortQ (monsterNortonOctadThreeUInput e) = monsterNortonOctadThreeUInputQ e := by
  rw [← monsterNortonOctadThreeUInput_actual]
  unfold monsterNortonOctadThreeUInputQ
  rcases h : monsterNortonOctadThreeUStorage e with k | k
  · exact monsterNortonPairHalfUPoolInputQ_actual k
  · exact monsterNortonOctadThreeSupplementInputQ_actual k

set_option maxHeartbeats 16000000 in
-- Check the polar pairing on each complete original input mask.
/-- The input phase follows from actual Norton V and the actual input Q element. -/
theorem monsterNortonOctadThreeInverseInputPhase_actual (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonOctadThreeUInput e) =
      monsterNortonOctadThreeInverseInputPhase e := by
  unfold monsterNortonVShortPhase
  rw [monsterNortonOctadThreeUInputQ_actual, monsterNortonVBinaryCoordinates_actual]
  revert e
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Pull V through the genuine U automorphism before checking the finite input pairing.
/-- Output phases use the exact inverse-U V probe, retaining the actual polar pairing. -/
theorem monsterNortonOctadThreeInverseOutputPhase_actual (e : Fin 64) :
    monsterNortonVShortPhase (monsterNortonOctadThreeUOutput e) =
      monsterNortonOctadThreeInverseOutputPhase e := by
  change monsterNortonQPolar y555NortonVQ
    (monsterNortonShortQ (monsterNortonOctadThreeUOutput e)) = _
  rw [← monsterNortonOctadThreeU_Q_image, monsterNortonVPhase_forwardU,
    monsterNortonOctadThreeUInputQ_actual]
  revert e
  decide +kernel

/-- Each full real coefficient is its exact signed integer numerator divided by eight. -/
theorem monsterNortonOctadThreeInverseIntegerCoefficient_actual (e : Fin 64) :
    qSign (monsterNortonVShortPhase (monsterNortonOctadThreeUInput 0)) *
      monsterNortonOctadThreeInverseSixthCoefficient e =
        (monsterNortonOctadThreeInverseIntegerCoefficient e : ℝ) / 8 := by
  unfold monsterNortonOctadThreeInverseSixthCoefficient
  rw [monsterNortonOctadThreeInverseInputPhase_actual,
    monsterNortonOctadThreeInverseInputPhase_actual,
    monsterNortonOctadThreeInverseOutputPhase_actual]
  have hi : monsterNortonOctadInverseCoefficient e 0 = 1 := by
    revert e
    decide +kernel
  rw [hi]
  fin_cases e <;>
    norm_num [monsterNortonOctadThreeInverseInputPhase,
      monsterNortonOctadThreeInverseOutputPhase,
      monsterNortonOctadThreeInverseIntegerCoefficient,
      qSign]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
