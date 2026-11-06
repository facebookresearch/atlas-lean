/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A norm-one sparse source-dictionary candidate for the second preferred half-word input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsDictionaryPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSparseImage

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The eight A terms, eight C terms, and 224 genuine octad units in the candidate. -/
abbrev NortonSecondHalfIndex := Fin 8 ⊕ (Fin 8 ⊕ (Fin 14 × Fin 16))

/-- The actual increasing-enumeration pair index for each physical pair. -/
noncomputable def monsterNortonSecondHalfPairIndex (i : Fin 8) : Fin 276 :=
  griessPairIndex (monsterNortonSecondHalfPairFirst i) (monsterNortonSecondHalfPairSecond i)
    (ne_of_lt (monsterNortonSecondHalfPair_lt i))

/-- Comparing the actual pair indices is exactly comparing their finite data indices. -/
theorem monsterNortonSecondHalfPairIndex_eq_iff (i j : Fin 8) :
    monsterNortonSecondHalfPairIndex i = monsterNortonSecondHalfPairIndex j ↔ i = j := by
  unfold monsterNortonSecondHalfPairIndex
  rw [monsterNortonOrderedPairIndex_eq_iff _ _ _ _ (monsterNortonSecondHalfPair_lt i)
    (monsterNortonSecondHalfPair_lt j), monsterNortonSecondHalfPair_eq_iff]

/-- The actual source units of the finite sparse candidate. -/
noncomputable def monsterNortonSecondHalfVector : NortonSecondHalfIndex → GriessSpace
  | Sum.inl i => trialityABCBasis 0 (monsterNortonSecondHalfPairIndex i)
  | Sum.inr (Sum.inl i) => trialityABCBasis 2 (monsterNortonSecondHalfPairIndex i)
  | Sum.inr (Sum.inr (d, e)) => monsterNortonPureShort
      (Sum.inr (Sum.inl
        (monsterNortonOctadIndex (monsterNortonSecondHalfOctadCode d)
          (monsterNortonSecondHalfOctad_weight d), monsterNortonSecondHalfOctadSign d e)))

/-- Actual source squared norms are two for A and C, and one for each octad unit. -/
def monsterNortonSecondHalfWeight : NortonSecondHalfIndex → ℝ
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 2
  | Sum.inr (Sum.inr _) => 1

/-- Every candidate coefficient retains its exact original denominator sixteen. -/
noncomputable def monsterNortonSecondHalfCoefficient : NortonSecondHalfIndex → ℝ
  | Sum.inl i => (monsterNortonSecondHalfPairCoefficient i : ℝ) / 16
  | Sum.inr (Sum.inl _) => -1 / 16
  | Sum.inr (Sum.inr (d, e)) => (monsterNortonSecondHalfOctadCoefficient d e : ℝ) / 16

/-- The complete sparse vector candidate in the actual Griess space. -/
noncomputable def monsterNortonSecondHalfPacket : GriessSpace :=
  ∑ i : NortonSecondHalfIndex,
    monsterNortonSecondHalfCoefficient i • monsterNortonSecondHalfVector i

private theorem form_symm (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem pure_octad_ABC (d : Fin 759) (e : Fin 64) (s : Fin 3) (p : Fin 276) :
    griessForm (monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))) (trialityABCBasis s p) = 0 := by
  unfold monsterNortonPureShort
  rw [← monsterNortonOctadShortVector_single d e 1, monsterNortonForm_octad_ABC]

/-- Every sparse candidate source unit is orthogonal to all the other listed units. -/
theorem monsterNortonSecondHalfVector_gram (i j : NortonSecondHalfIndex) :
    griessForm (monsterNortonSecondHalfVector i) (monsterNortonSecondHalfVector j) =
      if i = j then monsterNortonSecondHalfWeight i else 0 := by
  rcases i with i | (i | ⟨d, e⟩) <;> rcases j with j | (j | ⟨f, g⟩) <;>
    simp only [monsterNortonSecondHalfVector]
  · simp [monsterNortonSecondHalfWeight, monsterNortonForm_ABC_ABC,
      monsterNortonSecondHalfPairIndex_eq_iff]
  · simp [monsterNortonForm_ABC_ABC]
  · rw [form_symm, pure_octad_ABC]
    rfl
  · simp [monsterNortonForm_ABC_ABC]
  · simp [monsterNortonSecondHalfWeight, monsterNortonForm_ABC_ABC,
      monsterNortonSecondHalfPairIndex_eq_iff]
  · rw [form_symm, pure_octad_ABC]
    rfl
  · rw [pure_octad_ABC]
    rfl
  · rw [pure_octad_ABC]
    rfl
  · rw [monsterNortonOctadShort_form]
    by_cases h : d = f
    · subst f
      simp [monsterNortonSecondHalfOctadSign_eq_iff, monsterNortonSecondHalfWeight]
    · simp [monsterNortonSecondHalfOctad_eq_iff, h]

private theorem weighted_packet_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (v : ι → GriessSpace) (w : ι → ℝ)
    (h : ∀ i j, griessForm (v i) (v j) = if i = j then w i else 0) :
    griessForm (∑ i, c i • v i) (∑ i, c i • v i) = ∑ i, c i ^ 2 * w i := by
  rw [monsterNortonForm_sparse_packet]
  simp only [h, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every candidate coefficient has the exact real square one over 256. -/
theorem monsterNortonSecondHalfCoefficient_sq (i : NortonSecondHalfIndex) :
    monsterNortonSecondHalfCoefficient i ^ 2 = 1 / 256 := by
  rcases i with i | (i | ⟨d, e⟩)
  · have h : (monsterNortonSecondHalfPairCoefficient i : ℝ) ^ 2 = 1 := by
      exact_mod_cast monsterNortonSecondHalfPairCoefficient_sq i
    simp only [monsterNortonSecondHalfCoefficient, div_pow, h]
    norm_num
  · norm_num [monsterNortonSecondHalfCoefficient]
  · have h : (monsterNortonSecondHalfOctadCoefficient d e : ℝ) ^ 2 = 1 := by
      exact_mod_cast monsterNortonSecondHalfOctadCoefficient_sq d e
    simp only [monsterNortonSecondHalfCoefficient, div_pow, h]
    norm_num

/-- The actual weighted total of the 240 supported source units is 256. -/
theorem monsterNortonSecondHalfWeight_sum :
    (∑ i : NortonSecondHalfIndex, monsterNortonSecondHalfWeight i) = 256 := by
  norm_num [Fintype.sum_sum_type, Fintype.sum_prod_type, monsterNortonSecondHalfWeight]

/-- The entire sparse candidate has exact squared norm one in the actual Griess form. -/
theorem monsterNortonSecondHalfPacket_norm :
    griessForm monsterNortonSecondHalfPacket monsterNortonSecondHalfPacket = 1 := by
  rw [monsterNortonSecondHalfPacket, weighted_packet_norm _ _ _ monsterNortonSecondHalfVector_gram]
  simp_rw [monsterNortonSecondHalfCoefficient_sq]
  rw [← Finset.mul_sum, monsterNortonSecondHalfWeight_sum]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
