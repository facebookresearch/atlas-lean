/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete first three inverse-half states on the eleven physical pair basis inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondInverseThird

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original second physical coordinates of the eleven pair inputs. -/
def monsterNortonEvenShortPairCoordinate : Fin 11 → Fin 24 :=
  ![1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16]

/-- Every displayed pair coordinate is strictly greater than the first coordinate zero. -/
theorem monsterNortonEvenShortPairCoordinate_positive (k : Fin 11) :
    (0 : Fin 24) < monsterNortonEvenShortPairCoordinate k := by
  revert k
  decide +kernel

/-- The actual pair index associated to each original basis input. -/
noncomputable def monsterNortonEvenShortPairIndex (k : Fin 11) : Fin 276 :=
  griessPairIndex 0 (monsterNortonEvenShortPairCoordinate k)
    (ne_of_lt (monsterNortonEvenShortPairCoordinate_positive k))

/-- The first eleven original basis entries are exactly these family-zero physical pairs. -/
theorem monsterNortonEvenShortPair_input (k : Fin 11) :
    monsterNortonEvenShortBasis ⟨k.val, by omega⟩ =
      Sum.inl (0, monsterNortonEvenShortPairIndex k) := by
  fin_cases k <;> rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check both family phases at all eleven pairs through the actual preferred-Q dictionary.
/-- V's two pair-family phases differ by the actual central polar bit one. -/
theorem monsterNortonEvenShortPairVPhase (k : Fin 11) (s : Fin 2) :
    monsterNortonVShortPhase (Sum.inl (s, monsterNortonEvenShortPairIndex k)) =
      monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩ +
        if s = 0 then 0 else 1 := by
  unfold monsterNortonVShortPhase
  rw [monsterNortonVBinaryCoordinates_actual]
  unfold monsterNortonShortQ
  simp only [griessShortIntegral, monsterNortonEvenShortPairIndex,
    griessPairIndex_coordinates, monsterNortonEvenShortPairCoordinate_positive, ite_true]
  revert k s
  decide +kernel

/-- The actual B vector goes to the appropriately signed entire C vector. -/
theorem monsterNortonEvenShortPairV_B (k : Fin 11) :
    y555NortonV.val (trialityABCBasis 1 (monsterNortonEvenShortPairIndex k)) =
      qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) •
        trialityABCBasis 2 (monsterNortonEvenShortPairIndex k) := by
  rw [monsterNortonPairShort_B, map_sub, monsterNortonV_pure_short,
    monsterNortonV_pure_short, monsterNortonEvenShortPairVPhase,
    monsterNortonEvenShortPairVPhase]
  simp only [ite_true, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), add_zero,
    qSign_add, qSign_one, mul_neg_one, neg_smul, sub_neg_eq_add]
  rw [← smul_add, monsterNortonPairShort_C]

/-- The complete third inverse-half packet on every original physical pair input. -/
noncomputable def monsterNortonEvenShortPairInverseThirdPacket (k : Fin 11) : GriessSpace :=
  (qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2) •
    trialityABCBasis 0 (monsterNortonEvenShortPairIndex k) +
      (1 / 2 : ℝ) • trialityABCBasis 2 (monsterNortonEvenShortPairIndex k)

/-- Three literal inverse-half operators give the entire stated vector on all eleven pairs. -/
theorem monsterNortonEvenShortPairInverseFirstThree_actual (k : Fin 11) :
    y555NortonV.val (sExtra.symm (y555NortonV.val
      (monsterNortonPureShort (monsterNortonEvenShortBasis ⟨k.val, by omega⟩)))) =
        monsterNortonEvenShortPairInverseThirdPacket k := by
  rw [monsterNortonEvenShortInitialV_actual, map_smul, map_smul,
    monsterNortonEvenShortPair_input, monsterNortonPairShort_extra_inverse]
  simp only [ite_true]
  rw [map_add, map_smul, map_smul, monsterNortonEvenShortPairV_B, monsterNortonV_matrix_A]
  simp only [smul_add, smul_smul]
  have hcoef : qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) *
      ((1 / 2 : ℝ) * qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩)) =
        (1 / 2 : ℝ) := by
    rw [mul_left_comm, qSign_sq, mul_one]
  have hhalf : qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) * (1 / 2 : ℝ) =
      qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2 := by ring
  rw [hcoef, hhalf]
  exact add_comm _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
