/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact source-unit pairings with the complete actual sixth inverse-half packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondInverseSixth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem projection_decode (A : Matrix (Fin 24) (Fin 24) ℝ)
    (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ)
    (h : ∀ i j, A i j = A j i) :
    monsterNortonShortProjection (griessConwayDecode (A, (X, T))) = X := by
  change (griessConwayEncode (griessConwayDecode (A, (X, T)))).2.1 = X
  rw [griessConwayEncode_decode _ h]

private theorem matrix_projection :
    monsterNortonShortProjection monsterNortonEvenShortSecondInverseSixthMatrix =
      monsterNortonMatrixTrialityShort monsterNortonEvenShortSecondUMatrix := by
  unfold monsterNortonEvenShortSecondInverseSixthMatrix
  apply projection_decode
  intro i j
  simp only [Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h, Ne.symm]

private theorem form_matrix_pair (s : Fin 2) (p : Fin 276) :
    griessForm monsterNortonEvenShortSecondInverseSixthMatrix
      (monsterNortonPureShort (Sum.inl (s, p))) =
      if s = 0 then monsterNortonEvenShortSecondUMatrix
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 else
      -monsterNortonEvenShortSecondUMatrix
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 := by
  rw [monsterNortonForm_pureShort_right, matrix_projection]
  rfl

private theorem form_matrix_octad (d : Fin 759) (e : Fin 64) :
    griessForm monsterNortonEvenShortSecondInverseSixthMatrix
      (monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))) = 0 := by
  rw [monsterNortonForm_pureShort_right, matrix_projection]
  rfl

private theorem octad_pair_zero (d : Fin 759) (v : Fin 64 → ℝ)
    (s : Fin 2) (p : Fin 276) :
    griessForm (monsterNortonOctadShortVector d v)
      (monsterNortonPureShort (Sum.inl (s, p))) = 0 := by
  rw [monsterNortonForm_pureShort_right]
  unfold monsterNortonOctadShortVector
  rw [monsterNortonShortProjection_short]
  rfl

/-- Exact pairing of the whole sixth inverse-half image with any original pair unit. -/
theorem monsterNortonSecondInverseSixth_pair_form (s : Fin 2) (p : Fin 276) :
    griessForm monsterNortonEvenShortSecondInverseSixthPacket
      (monsterNortonPureShort (Sum.inl (s, p))) =
        (-1 / 2 : ℝ) * (if s = 0 then monsterNortonEvenShortSecondUMatrix
          (griessCoordinatePair p).1 (griessCoordinatePair p).2 else
        -monsterNortonEvenShortSecondUMatrix
          (griessCoordinatePair p).1 (griessCoordinatePair p).2) := by
  unfold monsterNortonEvenShortSecondInverseSixthPacket
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [form_matrix_pair]
  change _ + (-1 / 2 : ℝ) *
    (griessForm (monsterNortonOctadShortVector _ _) (monsterNortonPureShort (Sum.inl (s, p))) +
      griessForm (monsterNortonOctadShortVector _ _) (monsterNortonPureShort (Sum.inl (s, p)))) = _
  rw [octad_pair_zero, octad_pair_zero]
  ring

/-- Exact pairing with any genuine source octad, retaining both full triality Fourier images. -/
theorem monsterNortonSecondInverseSixth_octad_form (a : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8) (e : Fin 64) :
    griessForm monsterNortonEvenShortSecondInverseSixthPacket
      (monsterNortonPureShort (Sum.inr (Sum.inl (monsterNortonOctadIndex a ha, e)))) =
      (-1 / 2 : ℝ) *
        ((if (1295 : Fin 4096) = a then monsterNortonOctadTrialityCoefficient e 57 else 0) +
          (if (3087 : Fin 4096) = a then monsterNortonOctadTrialityCoefficient e 45 else 0)) := by
  unfold monsterNortonEvenShortSecondInverseSixthPacket
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [form_matrix_octad]
  change _ + (-1 / 2 : ℝ) *
    (griessForm (monsterNortonOctadShortVector (monsterNortonOctadIndex 1295 _) _)
      (monsterNortonPureShort (Sum.inr (Sum.inl (monsterNortonOctadIndex a ha, e)))) +
    griessForm (monsterNortonOctadShortVector (monsterNortonOctadIndex 3087 _) _)
      (monsterNortonPureShort (Sum.inr (Sum.inl (monsterNortonOctadIndex a ha, e))))) = _
  rw [monsterNortonForm_octad_unit_code, monsterNortonForm_octad_unit_code,
    monsterNortonOctadTriality_single, monsterNortonOctadTriality_single]
  rw [show monsterNortonEvenShortFirstUOctadSign (1 : Fin 23) = 57 from rfl]
  simp only [mul_one, mul_zero, zero_add]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
