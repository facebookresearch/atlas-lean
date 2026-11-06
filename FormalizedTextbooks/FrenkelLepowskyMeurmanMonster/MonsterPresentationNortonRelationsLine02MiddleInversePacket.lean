/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete sixth inverse-half packets for the eight middle preferred distance-two inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddlePlusU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairInversePrefix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMatrixTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortPositiveTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual physical pair shared by the original and complementary middle inputs. -/
noncomputable def monsterNortonLine02MiddlePhysicalPair (a : Fin 8) : Fin 276 :=
  griessPairIndex 0 (monsterNortonEvenShortPairSecond (Fin.natAdd 2 (Fin.castAdd 2 a)))
    (ne_of_lt (monsterNortonEvenShortPairSecond_positive _))

/-- The original preferred slot is exactly the minus-pair member of this physical pair. -/
theorem monsterNortonLine02MiddleBasis_pair (a : Fin 8) :
    monsterNortonEvenShortBasis (monsterNortonLine02MiddleBasis a) =
      Sum.inl (0, monsterNortonLine02MiddlePhysicalPair a) := by
  have hk : (monsterNortonLine02MiddleBasis a).val < 12 := by
    change 2 + a.val < 12
    omega
  have hj : (⟨(monsterNortonLine02MiddleBasis a).val, hk⟩ : Fin 12) =
      Fin.natAdd 2 (Fin.castAdd 2 a) := by
    apply Fin.ext
    rfl
  have hn : (monsterNortonLine02MiddleBasis a).val ≠ 11 := by
    change 2 + a.val ≠ 11
    omega
  simp only [monsterNortonEvenShortBasis, dite_eq_left hk]
  simp only [hj, ite_eq_right hn]
  rfl

/-- The true squared-U image of the original minus-pair unit has positive phase here. -/
theorem monsterNortonLine02MiddleMinusU_actual (a : Fin 8) :
    (y555NortonActualU ^ 2).val
      (monsterNortonPureShort (Sum.inl (0, monsterNortonLine02MiddlePhysicalPair a))) =
      monsterNortonPureShort
        (monsterNortonLine02FirstUOutput (monsterNortonLine02MiddleBasis a)) := by
  rw [← monsterNortonLine02MiddleBasis_pair]
  have hp : monsterNortonLine02FirstUPhase (monsterNortonLine02MiddleBasis a) = 0 := by
    revert a
    decide +kernel
  rw [monsterNortonLine02FirstU_actual, hp, qSign_zero, one_smul]

/-- The complete explicit matrix part before the last inverse-half triality step. -/
noncomputable def monsterNortonLine02MiddleInverseMatrix (a : Fin 8) :
    Matrix (Fin 24) (Fin 24) ℝ :=
  conwayMatrixAction (monsterNortonUFiber.val.2 ^ 2)
    (trialityPairMatrix (monsterNortonLine02MiddlePhysicalPair a))

/-- The full matrix and short coordinates of the six-step inverse source packet. -/
noncomputable def monsterNortonLine02MiddleInversePacket (a : Fin 8) : GriessSpace :=
  let p := monsterNortonLine02MiddlePhysicalPair a
  let r := monsterNortonLine02FirstUOutput (monsterNortonLine02MiddleBasis a)
  let s := monsterNortonLine02MiddlePlusOutput a
  let M := monsterNortonLine02MiddleInverseMatrix a
  qSign (monsterNortonVShortPhase (Sum.inl (0, p))) •
    ((1 / 2 : ℝ) •
      (qSign (monsterNortonVShortPhase (Sum.inl (0, p))) •
        (qSign (monsterNortonVShortPhase r) • monsterNortonShortExtraPacket r) -
      qSign (monsterNortonVShortPhase (Sum.inl (1, p))) •
        (qSign (monsterNortonVShortPhase s) • monsterNortonShortExtraPacket s)) +
    (1 / 2 : ℝ) • griessConwayDecode
      (Matrix.diagonal (fun i => M i i), (monsterNortonDistanceTwoMatrixTrialityShort M, 0)))

set_option maxRecDepth 10000 in
/-- The complete literal inverse half agrees with the actual physical matrix and short packet. -/
theorem monsterNortonLine02MiddleInversePacket_actual (a : Fin 8) :
    sExtra (y555NortonV.val ((y555NortonActualU ^ 2).val (y555NortonV.val
      (sExtra.symm (y555NortonV.val (monsterNortonPureShort
        (monsterNortonEvenShortBasis (monsterNortonLine02MiddleBasis a)))))))) =
      monsterNortonLine02MiddleInversePacket a := by
  rw [monsterNortonLine02MiddleBasis_pair, monsterNortonPairInversePrefix_actual]
  simp only [map_smul, map_add, map_sub]
  rw [monsterNortonLine02MiddleMinusU_actual]
  have hp : (y555NortonActualU ^ 2).val
      (monsterNortonPureShort (Sum.inl (1, monsterNortonLine02MiddlePhysicalPair a))) =
      monsterNortonPureShort (monsterNortonLine02MiddlePlusOutput a) :=
    monsterNortonLine02MiddlePlusU_actual a
  rw [hp, monsterNortonUTwo_pair_matrix, monsterNortonV_pure_short,
    monsterNortonV_pure_short]
  have hM : y555NortonV.val (griessConwayDecode
      (monsterNortonLine02MiddleInverseMatrix a, (0, 0))) =
      griessConwayDecode (monsterNortonLine02MiddleInverseMatrix a, (0, 0)) := by
    rw [y555NortonV]
    exact monsterNortonQ_pure_matrix y555NortonVQ _
      (conwayMatrixAction_symmetric _ _ (trialityPairMatrix_symmetric _))
  unfold monsterNortonLine02MiddleInverseMatrix at hM
  rw [hM]
  simp only [map_smul, monsterNortonShortExtraPacket_actual, monsterNortonMatrix_extra]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
