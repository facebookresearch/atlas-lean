/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete pair and octad form dictionary of the normalized actual inverse-half pair packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairsInversePhases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondInverseSixthPairings

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private noncomputable def matrixPacket (k : Fin 11) : GriessSpace :=
  griessConwayDecode (Matrix.diagonal (fun i => monsterNortonEvenShortPairsUMatrix k i i),
    (monsterNortonMatrixTrialityShort (monsterNortonEvenShortPairsUMatrix k), 0))

private theorem projection_decode (A : Matrix (Fin 24) (Fin 24) ℝ)
    (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ)
    (h : ∀ i j, A i j = A j i) :
    monsterNortonShortProjection (griessConwayDecode (A, (X, T))) = X := by
  change (griessConwayEncode (griessConwayDecode (A, (X, T)))).2.1 = X
  rw [griessConwayEncode_decode _ h]

private theorem matrix_projection (k : Fin 11) :
    monsterNortonShortProjection (matrixPacket k) =
      monsterNortonMatrixTrialityShort (monsterNortonEvenShortPairsUMatrix k) := by
  unfold matrixPacket
  apply projection_decode
  intro i j
  simp only [Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h, Ne.symm]

private theorem form_matrix_pair (k : Fin 11) (s : Fin 2) (p : Fin 276) :
    griessForm (matrixPacket k)
      (monsterNortonPureShort (Sum.inl (s, p))) =
      if s = 0 then monsterNortonEvenShortPairsUMatrix k
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 else
      -monsterNortonEvenShortPairsUMatrix k
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 := by
  rw [monsterNortonForm_pureShort_right, matrix_projection k]
  rfl

private theorem form_matrix_octad (k : Fin 11) (d : Fin 759) (e : Fin 64) :
    griessForm (matrixPacket k)
      (monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))) = 0 := by
  rw [monsterNortonForm_pureShort_right, matrix_projection k]
  rfl

private theorem octad_pair_zero (d : Fin 759) (v : Fin 64 → ℝ)
    (s : Fin 2) (p : Fin 276) :
    griessForm (monsterNortonOctadShortVector d v)
      (monsterNortonPureShort (Sum.inl (s, p))) = 0 := by
  rw [monsterNortonForm_pureShort_right]
  unfold monsterNortonOctadShortVector
  rw [monsterNortonShortProjection_short]
  rfl

private theorem lower_even (k : Fin 11) (hk : k.val < 10) :
    monsterNortonEvenShortFirstUIsOdd ⟨k.val, by omega⟩ = false := by
  revert k
  decide +kernel

private theorem upper_even (k : Fin 11) (hk : k.val < 10) :
    monsterNortonEvenShortUpperUIsOdd k = false := by
  revert k
  decide +kernel

private theorem lowerPacket (k : Fin 11) (hk : k.val < 10) :
    monsterNortonShortExtraPacket (monsterNortonEvenShortFirstUOutput ⟨k.val, by omega⟩) =
      monsterNortonOctadShortVector
        (monsterNortonOctadIndex (monsterNortonEvenShortFirstUOctadCodes ⟨k.val, by omega⟩)
          (monsterNortonEvenShortFirstUOctad_weight ⟨k.val, by omega⟩))
        (trialityOctadAction
          (Pi.single (monsterNortonEvenShortFirstUOctadSign ⟨k.val, by omega⟩) 1)) := by
  simp only [monsterNortonEvenShortFirstUOutput, lower_even k hk, Bool.false_eq_true,
    ite_false, monsterNortonShortExtraPacket]

private theorem upperPacket (k : Fin 11) (hk : k.val < 10) :
    monsterNortonShortExtraPacket (monsterNortonEvenShortUpperUOutput k) =
      monsterNortonOctadShortVector
        (monsterNortonOctadIndex (monsterNortonEvenShortUpperUOctadCodes k)
          (monsterNortonEvenShortUpperUOctad_weight k))
        (trialityOctadAction (Pi.single (monsterNortonEvenShortUpperUOctadSign k) 1)) := by
  simp only [monsterNortonEvenShortUpperUOutput, upper_even k hk, Bool.false_eq_true,
    ite_false, monsterNortonShortExtraPacket]

/-- Exact pairing of the full normalized inverse-sixth vector with any genuine pair unit. -/
theorem monsterNortonPairsInverseSixth_pair_form (k : Fin 11) (hk : k.val < 10)
    (s t : Fin 2) (p : Fin 276) :
    griessForm (monsterNortonEvenShortPairsInverseSixthNormalized k s)
      (monsterNortonPureShort (Sum.inl (t, p))) =
      (qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2) *
        (if t = 0 then monsterNortonEvenShortPairsUMatrix k
          (griessCoordinatePair p).1 (griessCoordinatePair p).2 else
          -monsterNortonEvenShortPairsUMatrix k
            (griessCoordinatePair p).1 (griessCoordinatePair p).2) := by
  unfold monsterNortonEvenShortPairsInverseSixthNormalized
  change griessForm (_ • matrixPacket k + _) _ = _
  rw [lowerPacket k hk, upperPacket k hk]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, form_matrix_pair, octad_pair_zero, add_zero, mul_zero]

/-- Exact pairing with any octad retains both genuine Fourier images and original family sign. -/
theorem monsterNortonPairsInverseSixth_octad_form (k : Fin 11) (hk : k.val < 10)
    (s : Fin 2) (a : Fin 4096) (ha : golayMaskWeight (golayEncodedMask a.val) = 8)
    (e : Fin 64) :
    griessForm (monsterNortonEvenShortPairsInverseSixthNormalized k s)
      (monsterNortonPureShort (Sum.inr (Sum.inl (monsterNortonOctadIndex a ha, e)))) =
      (monsterNortonPairFamilySign s *
        qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2) *
        ((if monsterNortonEvenShortFirstUOctadCodes ⟨k.val, by omega⟩ = a then
          monsterNortonOctadTrialityCoefficient e
            (monsterNortonEvenShortFirstUOctadSign ⟨k.val, by omega⟩) else 0) +
        (if monsterNortonEvenShortUpperUOctadCodes k = a then
          monsterNortonOctadTrialityCoefficient e (monsterNortonEvenShortUpperUOctadSign k)
          else 0)) := by
  unfold monsterNortonEvenShortPairsInverseSixthNormalized
  change griessForm (_ • matrixPacket k + _) _ = _
  rw [lowerPacket k hk, upperPacket k hk]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, form_matrix_octad, mul_zero, zero_add]
  rw [monsterNortonForm_octad_unit_code, monsterNortonForm_octad_unit_code,
    monsterNortonOctadTriality_single, monsterNortonOctadTriality_single]
  simp only [mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
