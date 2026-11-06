/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSpatialSourceWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineSignedWordActions

/-! Exact source-level spatial identities, retaining every inverse and the complete transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Spatial projection respects every primitive source product. -/
theorem generatedNinth_lower_spin_spatial_word_projection
    (w : List GeneratedNinthLowerSpinLetter) :
    generatedNinthLowerSpinSpatialWord w = generatedNinthLowerSpinSpatialProjection
      ((w.map generatedNinthLowerSpinFiberLetter).prod) := by
  rw [map_list_prod, List.map_map]
  rfl

/-- Concatenation evaluates to the genuine spatial group product. -/
theorem generatedNinth_lower_spin_spatial_word_append
    (v w : List GeneratedNinthLowerSpinLetter) :
    generatedNinthLowerSpinSpatialWord (v ++ w) =
      generatedNinthLowerSpinSpatialWord v * generatedNinthLowerSpinSpatialWord w := by
  simp only [generatedNinthLowerSpinSpatialWord, List.map_append, List.prod_append]

private theorem fiber_inverse_letter (l : GeneratedNinthLowerSpinLetter) :
    generatedNinthLowerSpinFiberLetter (l.1, !l.2) =
      (generatedNinthLowerSpinFiberLetter l)⁻¹ := by
  rcases l with ⟨k, b⟩
  cases b <;> simp [generatedNinthLowerSpinFiberLetter]

/-- Reversing and inverting every primitive letter evaluates to the genuine inverse. -/
theorem generatedNinth_lower_spin_spatial_word_inverse
    (w : List GeneratedNinthLowerSpinLetter) :
    generatedNinthLowerSpinSpatialWord (generatedNinthLowerSpinInverseWord w) =
      (generatedNinthLowerSpinSpatialWord w)⁻¹ := by
  rw [generatedNinthLowerSpinSpatialWord, generatedNinthLowerSpinInverseWord,
    List.map_map, List.map_reverse]
  simp_rw [Function.comp_def, fiber_inverse_letter, map_inv]
  simpa only [generatedNinthLowerSpinSpatialWord, List.map_map, Function.comp_def] using
    (List.prod_inv_reverse
      (w.map (fun l => generatedNinthLowerSpinSpatialProjection
        (generatedNinthLowerSpinFiberLetter l)))).symm

private theorem permutation_embed_spatial (l : Fin 2 × Bool) :
    generatedNinthLowerSpinSpatialProjection
      (generatedNinthLowerSpinFiberLetter (generatedNinthLowerSpinPermutationEmbed l)) =
        generatedNinthAffinePermutationLetter l := by
  rcases l with ⟨k, b⟩
  fin_cases k <;> cases b <;> rfl

/-- A positive section macro is exactly its original genuine spatial generator. -/
theorem generatedNinth_lower_spin_section_macro_genuine (k : Fin 18) (hk : k.val ≠ 11) :
    generatedNinthLowerSpinSpatialWord (generatedNinthLowerSpinSectionMacro k) =
      generatedFifthSectionGenerator k := by
  by_cases h : k.val < 12
  · have h11 : k.val < 11 := by omega
    simp only [generatedNinthLowerSpinSectionMacro, h, ↓reduceDIte,
      generatedNinthLowerSpinSpatialWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, generatedNinthLowerSpinFiberLetter, Bool.false_eq_true,
      ↓reduceIte, generatedNinthLowerSpinPositiveFiber, h11,
      generatedFifthSectionGenerator]
    rfl
  · by_cases h' : k.val < 17
    · simp only [generatedNinthLowerSpinSectionMacro, h, h', ↓reduceDIte,
        generatedNinthLowerSpinSpatialWord, List.map_map]
      simp_rw [Function.comp_def, permutation_embed_spatial]
      rw [generatedNinth_affine_selected_word_genuine]
      simp only [generatedFifthSectionGenerator, h, h', ↓reduceDIte]
    · have he : k = 17 := Fin.ext (by omega)
      subst k
      rfl

/-- A signed section macro is exactly the complete original signed generator. -/
theorem generatedNinth_lower_spin_signed_section_macro_genuine (l : Fin 18 × Bool)
    (hl : l.1.val ≠ 11) :
    generatedNinthLowerSpinSpatialWord (generatedNinthLowerSpinSignedSectionMacro l) =
      generatedNinthAffineSectionLetter l := by
  rcases l with ⟨k, b⟩
  cases b
  · exact generatedNinth_lower_spin_section_macro_genuine k hl
  · change generatedNinthLowerSpinSpatialWord
      (generatedNinthLowerSpinInverseWord (generatedNinthLowerSpinSectionMacro k)) = _
    rw [generatedNinth_lower_spin_spatial_word_inverse,
      generatedNinth_lower_spin_section_macro_genuine k hl]
    rfl

private theorem permutation_positive_spatial (k : Fin 2) :
    generatedNinthLowerSpinSpatialProjection
      (generatedNinthLowerSpinPositiveFiber ⟨k.val + 12, by omega⟩) =
      golayPermutationHom (omegaOrbitGolayPermutation k) := by
  change generatedNinthLowerSpinSpatialProjection
    (generatedNinthLowerSpinFiberLetter
      (generatedNinthLowerSpinPermutationEmbed (k, false))) = _
  rw [permutation_embed_spatial]
  rfl

/-- The primitive transport word is the exact previously certified actual Co0 transport. -/
theorem generatedNinth_lower_spin_transport_word_genuine :
    generatedNinthLowerSpinSpatialWord generatedNinthLowerSpinTransportWord =
      generatedNinthAffineTransport := by
  have hs : generatedNinthSectionSign = monsterCo1GeometrySignCode 5 := by
    apply Subtype.ext
    change golayEncoder (golayLabelCoefficients 32) = golayEncoder (Pi.single 5 1)
    congr 1
    decide +kernel
  simp only [generatedNinthLowerSpinSpatialWord, generatedNinthLowerSpinTransportWord,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    generatedNinthLowerSpinFiberLetter, Bool.false_eq_true,
    ↓reduceIte, map_inv, mul_one]
  have hp0 : generatedNinthLowerSpinSpatialProjection
      (generatedNinthLowerSpinPositiveFiber 12) =
        golayPermutationHom (omegaOrbitGolayPermutation 0) := by
    have hf : (⟨(0 : Fin 2).val + 12, by omega⟩ : Fin 15) = 12 := by
      apply Fin.ext
      norm_num
    simpa only [hf] using permutation_positive_spatial 0
  have hp1 : generatedNinthLowerSpinSpatialProjection
      (generatedNinthLowerSpinPositiveFiber 13) =
        golayPermutationHom (omegaOrbitGolayPermutation 1) := by
    have hf : (⟨(1 : Fin 2).val + 12, by omega⟩ : Fin 15) = 13 := by
      apply Fin.ext
      norm_num
    simpa only [hf] using permutation_positive_spatial 1
  have hx : generatedNinthLowerSpinSpatialProjection
      (generatedNinthLowerSpinPositiveFiber 14) = co1XiIsometry := rfl
  have hsg : generatedNinthLowerSpinSpatialProjection
      (generatedNinthLowerSpinPositiveFiber 5) =
        golaySignIsometry (monsterCo1GeometrySignCode 5) := rfl
  simp only [hp0, hp1, hx, hsg]
  change _ = golayPermutationHom generatedNinthAffineOctadPermutation *
    (co1XiIsometry⁻¹ * golayPermutationHom generatedNinthSectionPermutation *
      golaySignIsometry generatedNinthSectionSign)
  rw [hs]
  simp only [generatedNinthAffineOctadPermutation, generatedNinthSectionPermutation,
    map_mul, map_inv, mul_assoc]

private theorem section_word_genuine (w : List (Fin 18 × Bool))
    (hw : ∀ l ∈ w, l.1.val ≠ 11) :
    generatedNinthLowerSpinSpatialWord
      (w.flatMap generatedNinthLowerSpinSignedSectionMacro) =
        (w.map generatedNinthAffineSectionLetter).prod := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.flatMap_cons, generatedNinth_lower_spin_spatial_word_append,
      generatedNinth_lower_spin_signed_section_macro_genuine l
        (hw l (List.mem_cons_self ..)), List.map_cons, List.prod_cons,
      ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))]

/-- The actual source fiber is exactly the transport conjugate of the original section word. -/
theorem generatedNinth_lower_spin_spatial_source_genuine (i : Fin 11) :
    (generatedNinthLowerSpinSourceFiber i).val.2 =
      generatedNinthAffineTransport⁻¹ * generatedNinthAffineLowerSourceIsometry i *
        generatedNinthAffineTransport := by
  change generatedNinthLowerSpinSpatialProjection
    (((generatedNinthLowerSpinSourceWord i).map generatedNinthLowerSpinFiberLetter).prod) = _
  rw [← generatedNinth_lower_spin_spatial_word_projection,
    generatedNinth_lower_spin_spatial_word_expansion,
    generatedNinth_lower_spin_spatial_word_append,
    generatedNinth_lower_spin_spatial_word_append,
    generatedNinth_lower_spin_spatial_word_inverse,
    generatedNinth_lower_spin_transport_word_genuine,
    section_word_genuine _ (generatedNinth_lower_spin_section_letter_ne_scalar i)]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
