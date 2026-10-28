/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual sixth inverse-half images of both original families on all eleven pairs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortUpperPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMatrixTrialityCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortPositiveTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The sign of the original two preferred physical pair families. -/
def monsterNortonPairFamilySign (s : Fin 2) : ℝ := if s = 0 then 1 else -1

/-- The complete third inverse-half packet for either family of an original pair. -/
noncomputable def monsterNortonEvenShortPairsInverseThird (k : Fin 11) (s : Fin 2) : GriessSpace :=
  (qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2) •
    trialityABCBasis 0 (monsterNortonEvenShortPairIndex k) +
    (monsterNortonPairFamilySign s / 2) •
      trialityABCBasis 2 (monsterNortonEvenShortPairIndex k)

/-- Three literal inverse-half operators have the whole stated original-coordinate pair image. -/
theorem monsterNortonEvenShortPairsInverseThird_actual (k : Fin 11) (s : Fin 2) :
    y555NortonV.val (sExtra.symm (y555NortonV.val
      (monsterNortonPureShort (Sum.inl (s, monsterNortonEvenShortPairIndex k))))) =
        monsterNortonEvenShortPairsInverseThird k s := by
  fin_cases s
  · change y555NortonV.val (sExtra.symm (y555NortonV.val
      (monsterNortonPureShort (Sum.inl (0, monsterNortonEvenShortPairIndex k))))) =
        monsterNortonEvenShortPairsInverseThird k 0
    rw [monsterNortonEvenShortPairsInverseThird,
      show monsterNortonPairFamilySign 0 = (1 : ℝ) from rfl]
    simpa only [monsterNortonEvenShortPair_input,
      monsterNortonEvenShortPairInverseThirdPacket] using
      monsterNortonEvenShortPairInverseFirstThree_actual k
  · change y555NortonV.val (sExtra.symm (y555NortonV.val
      (monsterNortonPureShort (Sum.inl (1, monsterNortonEvenShortPairIndex k))))) =
        monsterNortonEvenShortPairsInverseThird k 1
    rw [monsterNortonV_pure_short, monsterNortonEvenShortPairVPhase]
    simp only [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), qSign_add, qSign_one,
      mul_neg_one, map_smul, monsterNortonPairShort_extra_inverse]
    simp only [map_add, map_smul,
      monsterNortonEvenShortPairV_B, monsterNortonV_matrix_A, smul_add, smul_smul]
    have hc : -qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) *
        ((1 / 2 : ℝ) * qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩)) =
          (-1 / 2 : ℝ) := by
      calc
        _ = (-1 / 2 : ℝ) * (qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) *
          qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩)) := by ring
        _ = _ := by rw [qSign_sq]; ring
    have ha : -qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) *
        (-1 / 2 : ℝ) = qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2 := by
      ring
    rw [hc, ha]
    unfold monsterNortonEvenShortPairsInverseThird monsterNortonPairFamilySign
    simp only [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
    exact add_comm _ _

/-- The actual physical matrix after U on the original A pair vector. -/
noncomputable def monsterNortonEvenShortPairsUMatrix (k : Fin 11) :
    Matrix (Fin 24) (Fin 24) ℝ :=
  conwayMatrixAction monsterNortonUFiber.val.2
    (trialityPairMatrix (monsterNortonEvenShortPairIndex k))

/-- This genuine transported physical matrix remains symmetric. -/
theorem monsterNortonEvenShortPairsUMatrix_symmetric (k : Fin 11) :
    ∀ i j, monsterNortonEvenShortPairsUMatrix k i j = monsterNortonEvenShortPairsUMatrix k j i :=
  conwayMatrixAction_symmetric _ _ (trialityPairMatrix_symmetric _)

/-- Actual U transports both original preferred pair families, so their sum gives the whole C
image. -/
theorem monsterNortonEvenShortPairsU_C (k : Fin 11) :
    y555NortonActualU.val (trialityABCBasis 2 (monsterNortonEvenShortPairIndex k)) =
      monsterNortonPureShort (monsterNortonEvenShortFirstUOutput ⟨k.val, by omega⟩) +
        monsterNortonPureShort (monsterNortonEvenShortUpperUOutput k) := by
  rw [monsterNortonPairShort_C, map_add]
  rw [← monsterNortonEvenShortPair_input k, monsterNortonEvenShortFirstU_actual]
  exact congrArg (fun x : GriessSpace =>
    monsterNortonPureShort (monsterNortonEvenShortFirstUOutput ⟨k.val, by omega⟩) + x)
    (monsterNortonEvenShortUpperU_actual k)

private theorem matrix_V (k : Fin 11) :
    y555NortonV.val (griessConwayDecode (monsterNortonEvenShortPairsUMatrix k, (0, 0))) =
      griessConwayDecode (monsterNortonEvenShortPairsUMatrix k, (0, 0)) :=
  monsterNortonQ_matrix_fixed y555NortonVQ _ (monsterNortonEvenShortPairsUMatrix_symmetric k)

/-- The whole fourth inverse-half packet, including both actual preferred short images. -/
noncomputable def monsterNortonEvenShortPairsInverseFourth (k : Fin 11) (s : Fin 2) : GriessSpace :=
  (qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2) •
    griessConwayDecode (monsterNortonEvenShortPairsUMatrix k, (0, 0)) +
    (monsterNortonPairFamilySign s / 2) •
      (monsterNortonPureShort (monsterNortonEvenShortFirstUOutput ⟨k.val, by omega⟩) +
        monsterNortonPureShort (monsterNortonEvenShortUpperUOutput k))

/-- The entire fourth inverse-half U image agrees with the stated physical packet. -/
theorem monsterNortonEvenShortPairsInverseFourth_actual (k : Fin 11) (s : Fin 2) :
    y555NortonActualU.val (monsterNortonEvenShortPairsInverseThird k s) =
      monsterNortonEvenShortPairsInverseFourth k s := by
  rw [monsterNortonEvenShortPairsInverseThird, map_add, map_smul, map_smul,
    monsterNortonU_pair_matrix, monsterNortonEvenShortPairsU_C]
  rfl

/-- Fifth inverse-half coordinates retain each genuine short output's exact V phase. -/
noncomputable def monsterNortonEvenShortPairsInverseFifth (k : Fin 11) (s : Fin 2) : GriessSpace :=
  (qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2) •
    griessConwayDecode (monsterNortonEvenShortPairsUMatrix k, (0, 0)) +
    (monsterNortonPairFamilySign s / 2) •
      (qSign (monsterNortonVShortPhase (monsterNortonEvenShortFirstUOutput ⟨k.val, by omega⟩)) •
        monsterNortonPureShort (monsterNortonEvenShortFirstUOutput ⟨k.val, by omega⟩) +
      qSign (monsterNortonVShortPhase (monsterNortonEvenShortUpperUOutput k)) •
        monsterNortonPureShort (monsterNortonEvenShortUpperUOutput k))

/-- Actual V acts on the entire fourth vector with precisely its true two short phases. -/
theorem monsterNortonEvenShortPairsInverseFifth_actual (k : Fin 11) (s : Fin 2) :
    y555NortonV.val (monsterNortonEvenShortPairsInverseFourth k s) =
      monsterNortonEvenShortPairsInverseFifth k s := by
  rw [monsterNortonEvenShortPairsInverseFourth, map_add, map_smul, map_smul,
    matrix_V,
    map_add, monsterNortonV_pure_short, monsterNortonV_pure_short]
  rfl

/-- The full sixth inverse-half packet retains the matrix, both short phases, and any odd
tensor branch. -/
noncomputable def monsterNortonEvenShortPairsInverseSixth (k : Fin 11) (s : Fin 2) : GriessSpace :=
  (qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2) •
    griessConwayDecode (Matrix.diagonal (fun i => monsterNortonEvenShortPairsUMatrix k i i),
      (monsterNortonMatrixTrialityShort (monsterNortonEvenShortPairsUMatrix k), 0)) +
    (monsterNortonPairFamilySign s / 2) •
      (qSign (monsterNortonVShortPhase (monsterNortonEvenShortFirstUOutput ⟨k.val, by omega⟩)) •
        monsterNortonShortExtraPacket (monsterNortonEvenShortFirstUOutput ⟨k.val, by omega⟩) +
      qSign (monsterNortonVShortPhase (monsterNortonEvenShortUpperUOutput k)) •
        monsterNortonShortExtraPacket (monsterNortonEvenShortUpperUOutput k))

/-- Positive triality gives the entire sixth packet, including its genuine odd source image
when present. -/
theorem monsterNortonEvenShortPairsInverseSixth_actual (k : Fin 11) (s : Fin 2) :
    sExtra (monsterNortonEvenShortPairsInverseFifth k s) =
      monsterNortonEvenShortPairsInverseSixth k s := by
  rw [monsterNortonEvenShortPairsInverseFifth, map_add, map_smul, map_smul,
    monsterNortonMatrix_extra_actual, map_add, map_smul, map_smul,
    monsterNortonShortExtraPacket_actual, monsterNortonShortExtraPacket_actual]
  rfl

/-- Six literal inverse-half generators have the complete stated image on either family of
every pair. -/
theorem monsterNortonEvenShortPairsInverseFirstSix_actual (k : Fin 11) (s : Fin 2) :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val
        (monsterNortonPureShort (Sum.inl (s, monsterNortonEvenShortPairIndex k)))))))) =
        monsterNortonEvenShortPairsInverseSixth k s := by
  rw [monsterNortonEvenShortPairsInverseThird_actual,
    monsterNortonEvenShortPairsInverseFourth_actual,
    monsterNortonEvenShortPairsInverseFifth_actual, monsterNortonEvenShortPairsInverseSixth_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
