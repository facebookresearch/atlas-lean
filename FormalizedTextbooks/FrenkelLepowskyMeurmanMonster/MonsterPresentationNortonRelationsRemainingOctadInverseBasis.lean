/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual preferred-basis identification and whole norm of the remaining inverse packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadInverseSixth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ReturnFromPackets

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The remaining octads occupy preferred-basis positions thirteen through twenty-two. -/
def monsterNortonRemainingOctadBasisIndex (k : Fin 10) : Fin 23 :=
  ⟨13 + k.val, by omega⟩

/-- Each original sign-zero input is exactly its actual chosen preferred-basis vector. -/
theorem monsterNortonRemainingOctadUInput_basis (k : Fin 10) :
    monsterNortonRemainingOctadUInput k 0 =
      monsterNortonEvenShortBasis (monsterNortonRemainingOctadBasisIndex k) := by
  fin_cases k <;> rfl

/-- All six actual inverse operators on these preferred inputs give their whole packets. -/
theorem monsterNortonRemainingOctadInverseBasis_actual (k : Fin 10) :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val (monsterNortonPureShort (monsterNortonEvenShortBasis
        (monsterNortonRemainingOctadBasisIndex k)))))))) =
      monsterNortonRemainingOctadInverseSixthPacket k := by
  rw [← monsterNortonRemainingOctadUInput_basis]
  exact monsterNortonRemainingOctadInverseFirstSix_actual k

/-- Every complete inverse packet has actual Griess norm one, including all tensor contributions. -/
theorem monsterNortonRemainingOctadInverseSixthPacket_norm (k : Fin 10) :
    griessForm (monsterNortonRemainingOctadInverseSixthPacket k)
      (monsterNortonRemainingOctadInverseSixthPacket k) = 1 := by
  let x := monsterNortonPureShort (monsterNortonRemainingOctadUInput k 0)
  let g : G := extraIntoGenerated * y555NortonV * y555NortonActualU * y555NortonV *
    extraIntoGenerated⁻¹ * y555NortonV
  have h := generated_group_preserves_griessForm g x x
  change griessForm
    (sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val x))))))
    (sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val x)))))) = griessForm x x at h
  dsimp only [x] at h
  rw [monsterNortonRemainingOctadInverseFirstSix_actual, monsterNortonPureShort_form] at h
  simpa only [ite_true] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
