/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A norm-one sparse source-dictionary candidate for the second preferred half-word input. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsDictionaryPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSparseImage
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
/-- The eight A terms, eight C terms, and 224 genuine octad units in the candidate. -/
abbrev NortonPairHalfIndex := Fin 8 ⊕ (Fin 8 ⊕ (Fin 14 × Fin 16))
/-- The actual increasing-enumeration pair index for each physical pair. -/
noncomputable def monsterNortonPairHalfPairIndex (k : Fin 12) (i : Fin 8) : Fin 276 :=
  griessPairIndex ((monsterNortonPairHalfPairFirst k) i) ((monsterNortonPairHalfPairSecond k) i)
    (ne_of_lt ((monsterNortonPairHalfPair_lt k) i))
/-- Comparing the actual pair indices is exactly comparing their finite data indices. -/
theorem monsterNortonPairHalfPairIndex_eq_iff (k : Fin 12) (i j : Fin 8) :
    (monsterNortonPairHalfPairIndex k) i = (monsterNortonPairHalfPairIndex k) j ↔ i = j := by
  unfold monsterNortonPairHalfPairIndex
  rw [monsterNortonOrderedPairIndex_eq_iff _ _ _ _ ((monsterNortonPairHalfPair_lt k) i)
    ((monsterNortonPairHalfPair_lt k) j), (monsterNortonPairHalfPair_eq_iff k)]
/-- The actual source units of the finite sparse candidate. -/
noncomputable def monsterNortonPairHalfVector (k : Fin 12) : NortonPairHalfIndex → GriessSpace
  | Sum.inl i => trialityABCBasis 0 ((monsterNortonPairHalfPairIndex k) i)
  | Sum.inr (Sum.inl i) => trialityABCBasis 2 ((monsterNortonPairHalfPairIndex k) i)
  | Sum.inr (Sum.inr (d, e)) => monsterNortonPureShort
      (Sum.inr (Sum.inl
        (monsterNortonOctadIndex ((monsterNortonPairHalfOctadCode k) d)
          ((monsterNortonPairHalfOctad_weight k) d), (monsterNortonPairHalfOctadSign k) d e)))
/-- Actual source squared norms are two for A and C, and one for each octad unit. -/
def monsterNortonPairHalfWeight : NortonPairHalfIndex → ℝ
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 2
  | Sum.inr (Sum.inr _) => 1
/-- Every candidate coefficient retains its exact original denominator sixteen. -/
noncomputable def monsterNortonPairHalfCoefficient (k : Fin 12) : NortonPairHalfIndex → ℝ
  | Sum.inl i => ((monsterNortonPairHalfPairCoefficient k) i : ℝ) / 16
  | Sum.inr (Sum.inl i) => (monsterNortonPairHalfPairCCoefficient k i : ℝ) / 16
  | Sum.inr (Sum.inr (d, e)) => ((monsterNortonPairHalfOctadCoefficient k) d e : ℝ) / 16
/-- The complete sparse vector candidate in the actual Griess space. -/
noncomputable def monsterNortonPairHalfPacket (k : Fin 12) : GriessSpace :=
  ∑ i : NortonPairHalfIndex,
    (monsterNortonPairHalfCoefficient k) i • (monsterNortonPairHalfVector k) i
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
theorem monsterNortonPairHalfVector_gram (k : Fin 12) (i j : NortonPairHalfIndex) :
    griessForm ((monsterNortonPairHalfVector k) i) ((monsterNortonPairHalfVector k) j) =
      if i = j then monsterNortonPairHalfWeight i else 0 := by
  rcases i with i | (i | ⟨d, e⟩) <;> rcases j with j | (j | ⟨f, g⟩) <;>
    simp only [monsterNortonPairHalfVector]
  · simp [monsterNortonPairHalfWeight, monsterNortonForm_ABC_ABC,
      (monsterNortonPairHalfPairIndex_eq_iff k)]
  · simp [monsterNortonForm_ABC_ABC]
  · rw [form_symm, pure_octad_ABC]
    rfl
  · simp [monsterNortonForm_ABC_ABC]
  · simp [monsterNortonPairHalfWeight, monsterNortonForm_ABC_ABC,
      (monsterNortonPairHalfPairIndex_eq_iff k)]
  · rw [form_symm, pure_octad_ABC]
    rfl
  · rw [pure_octad_ABC]
    rfl
  · rw [pure_octad_ABC]
    rfl
  · rw [monsterNortonOctadShort_form]
    by_cases h : d = f
    · subst f
      simp [(monsterNortonPairHalfOctadSign_eq_iff k), monsterNortonPairHalfWeight]
    · simp [(monsterNortonPairHalfOctad_eq_iff k), h]
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
theorem monsterNortonPairHalfCoefficient_sq (k : Fin 12) (i : NortonPairHalfIndex) :
    (monsterNortonPairHalfCoefficient k) i ^ 2 = 1 / 256 := by
  rcases i with i | (i | ⟨d, e⟩)
  · have h : ((monsterNortonPairHalfPairCoefficient k) i : ℝ) ^ 2 = 1 := by
      exact_mod_cast (monsterNortonPairHalfPairCoefficient_sq k) i
    simp only [monsterNortonPairHalfCoefficient, div_pow, h]
    norm_num
  · have h : (monsterNortonPairHalfPairCCoefficient k i : ℝ) ^ 2 = 1 := by
      exact_mod_cast monsterNortonPairHalfPairCCoefficient_sq k i
    simp only [monsterNortonPairHalfCoefficient, div_pow, h]
    norm_num
  · have h : ((monsterNortonPairHalfOctadCoefficient k) d e : ℝ) ^ 2 = 1 := by
      exact_mod_cast (monsterNortonPairHalfOctadCoefficient_sq k) d e
    simp only [monsterNortonPairHalfCoefficient, div_pow, h]
    norm_num
/-- The actual weighted total of the 240 supported source units is 256. -/
theorem monsterNortonPairHalfWeight_sum :
    (∑ i : NortonPairHalfIndex, monsterNortonPairHalfWeight i) = 256 := by
  norm_num [Fintype.sum_sum_type, Fintype.sum_prod_type, monsterNortonPairHalfWeight]
/-- The entire sparse candidate has exact squared norm one in the actual Griess form. -/
theorem monsterNortonPairHalfPacket_norm (k : Fin 12) :
    griessForm (monsterNortonPairHalfPacket k) (monsterNortonPairHalfPacket k) = 1 := by
  rw [monsterNortonPairHalfPacket,
      weighted_packet_norm _ _ _ (monsterNortonPairHalfVector_gram k)]
  simp_rw [(monsterNortonPairHalfCoefficient_sq k)]
  rw [← Finset.mul_sum, monsterNortonPairHalfWeight_sum]
  norm_num
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
