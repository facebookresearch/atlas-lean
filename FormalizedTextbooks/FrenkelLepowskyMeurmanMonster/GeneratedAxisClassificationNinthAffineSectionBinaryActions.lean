/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineSectionLetters

/-! Every full binary column is the entire action of its original genuine section letter. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The original positive source permutation has its whole genuine binary-column action. -/
theorem generatedNinth_affine_permutation_positive_binary (k : Fin 2) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry k) v =
      sixthFrameOrbitColumnMatrix
        (generatedNinthAffinePermutationColumns ⟨k.val, by omega⟩) *ᵥ v := by
  have h := omegaOrbitIsometry_binary (Fin.natAdd 3 k) v
  have hi : omegaOrbitIsometry (Fin.natAdd 3 k) = omegaOrbitPermutationIsometry k := by
    fin_cases k <;> rfl
  rw [hi, ← generatedNinth_affine_original_columns.1 k] at h
  exact h

/-- The literal inverse source permutation has its whole genuine binary-column action. -/
theorem generatedNinth_affine_permutation_inverse_binary (k : Fin 2) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry k)⁻¹ v =
      sixthFrameOrbitColumnMatrix
        (generatedNinthAffinePermutationColumns ⟨k.val + 2, by omega⟩) *ᵥ v := by
  apply (leechBinaryAction (omegaOrbitPermutationIsometry k)).injective
  rw [map_inv]
  change (leechBinaryAction (omegaOrbitPermutationIsometry k))
      ((leechBinaryAction (omegaOrbitPermutationIsometry k)).symm v) = _
  rw [LinearEquiv.apply_symm_apply,
    generatedNinth_affine_permutation_positive_binary, Matrix.mulVec_mulVec,
    (generatedNinth_affine_permutation_column_inverse k).1, Matrix.one_mulVec]

/-- Either original source orientation retains the entire packed binary action. -/
theorem generatedNinth_affine_permutation_letter_packed (l : Fin 2 × Bool) (v : ℕ) :
    leechBinaryAction (generatedNinthAffinePermutationLetter l)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply (generatedNinthAffinePermutationLetterColumns l) v) := by
  rcases l with ⟨k, b⟩
  cases b
  · change leechBinaryAction (omegaOrbitPermutationIsometry k)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode (sixthFrameOrbitMaskApply
        (generatedNinthAffinePermutationColumns ⟨k.val, by omega⟩) v)
    rw [generatedNinth_affine_permutation_positive_binary]
    exact (sixthFrameOrbitMaskApply_decode _ _).symm
  · change leechBinaryAction (omegaOrbitPermutationIsometry k)⁻¹
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode (sixthFrameOrbitMaskApply
        (generatedNinthAffinePermutationColumns ⟨k.val + 2, by omega⟩) v)
    rw [generatedNinth_affine_permutation_inverse_binary]
    exact (sixthFrameOrbitMaskApply_decode _ _).symm

/-- Every entire original permutation word retains the full packed source action. -/
theorem generatedNinth_affine_permutation_word_packed (w : List (Fin 2 × Bool)) (v : ℕ) :
    leechBinaryAction ((w.map generatedNinthAffinePermutationLetter).prod)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthAffinePermutationMaskWord w v) := by
  induction w with
  | nil => rw [List.map_nil, List.prod_nil, map_one]; rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, map_mul]
    change leechBinaryAction (generatedNinthAffinePermutationLetter l)
        (leechBinaryAction ((w.map generatedNinthAffinePermutationLetter).prod)
          (monsterCo1GeometryBinaryMaskDecode (n := 24) v)) =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply (generatedNinthAffinePermutationLetterColumns l)
          (generatedNinthAffinePermutationMaskWord w v))
    rw [ih, generatedNinth_affine_permutation_letter_packed]

private theorem permutation_letter_genuine (l : Fin 2 × Bool) :
    generatedNinthAffinePermutationLetter l =
      golayPermutationHom (generatedFourthMonomialPermutationLetter l) := by
  rcases l with ⟨k, b⟩
  cases b
  · rfl
  · exact (golayPermutationHom.map_inv _).symm

private theorem permutation_inverse_letter (l : Fin 2 × Bool) :
    generatedFourthMonomialPermutationLetter (l.1, !l.2) =
      (generatedFourthMonomialPermutationLetter l)⁻¹ := by
  rcases l with ⟨k, b⟩
  cases b <;> simp [generatedFourthMonomialPermutationLetter]

private theorem selected_source_word (k : Fin 5) :
    ((generatedNinthAffineSelectedSourceWord k).map
      generatedFourthMonomialPermutationLetter).prod = generatedFifthSourceOctadPermutation k := by
  fin_cases k
  all_goals simp [generatedNinthAffineSelectedSourceWord, generatedFifthSourceOctadPermutation,
    generatedFourthMonomialPermutation, generatedFourthMonomialPermutationLetter]

/-- The complete selected source word is exactly the original genuine Golay permutation. -/
theorem generatedNinth_affine_selected_word_genuine (k : Fin 5) :
    ((generatedNinthAffineSelectedWord k).map generatedNinthAffinePermutationLetter).prod =
      golayPermutationIsometry (generatedFifthSelectedOctadPermutation k) := by
  have hf : generatedNinthAffinePermutationLetter =
      golayPermutationHom ∘ generatedFourthMonomialPermutationLetter := by
    funext l
    exact permutation_letter_genuine l
  rw [hf, ← List.map_map, ← map_list_prod]
  apply congrArg golayPermutationHom
  unfold generatedNinthAffineSelectedWord
  rw [List.map_append, List.map_append, List.prod_append, List.prod_append]
  have hi : (generatedFifthMonomialTransportWord.reverse.map
      (fun l => (l.1, !l.2)) |>.map generatedFourthMonomialPermutationLetter).prod =
      ((generatedFifthMonomialTransportWord.map
        generatedFourthMonomialPermutationLetter).prod)⁻¹ := by
    rw [List.map_map, List.map_reverse]
    simp_rw [Function.comp_def, permutation_inverse_letter]
    exact (List.prod_inv_reverse
      (generatedFifthMonomialTransportWord.map generatedFourthMonomialPermutationLetter)).symm
  rw [hi, selected_source_word]
  rfl

/-- Every original binary coordinate basis vector is its genuine packed unit vector. -/
theorem generatedNinth_affine_binary_basis_decode : ∀ j : Fin 24,
    monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) = Pi.single j (1 : ZMod 2) := by
  decide +kernel

/-- Every selected original permutation acts by the entire proposed full binary matrix. -/
theorem generatedNinth_affine_selected_binary (k : Fin 5) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (golayPermutationIsometry (generatedFifthSelectedOctadPermutation k)) v =
      sixthFrameOrbitColumnMatrix
        (generatedNinthAffineSectionColumns ⟨k.val + 12, by omega⟩) *ᵥ v := by
  have h : (leechBinaryAction
      (golayPermutationIsometry (generatedFifthSelectedOctadPermutation k))).toLinearMap =
      Matrix.mulVecLin (sixthFrameOrbitColumnMatrix
        (generatedNinthAffineSectionColumns ⟨k.val + 12, by omega⟩)) := by
    apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
    intro j
    have hj := generatedNinth_affine_permutation_word_packed (generatedNinthAffineSelectedWord k)
      (2 ^ j.val)
    rw [generatedNinth_affine_selected_word_genuine, generatedNinth_affine_binary_basis_decode,
      generatedNinth_affine_selected_word_columns] at hj
    simpa only [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      sixthFrameOrbitColumnMatrix, monsterCo1GeometryBinaryMaskMatrix, Matrix.col,
      Matrix.transpose_apply, Matrix.transpose_transpose, LinearEquiv.coe_coe] using hj
  exact LinearMap.congr_fun h v

/-- All eighteen original full binary matrices are genuine entire lattice-quotient actions. -/
theorem generatedNinth_affine_section_binary (g : Fin 18) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedFifthSectionGenerator g) v =
      sixthFrameOrbitColumnMatrix (generatedNinthAffineSectionColumns g) *ᵥ v := by
  by_cases h : g.val < 12
  · let k : Fin 12 := ⟨g.val, h⟩
    have hg : generatedFifthSectionGenerator g = monsterCo1GeometrySignIsometry k := by
      simp only [generatedFifthSectionGenerator, h, ↓reduceDIte]
      rfl
    rw [hg]
    have hs := monsterCo1GeometrySign_binary k v
    change leechBinaryAction (monsterCo1GeometrySignIsometry k) v = _ at hs
    rw [← generatedNinth_affine_section_sign_columns k] at hs
    exact hs
  · by_cases h' : g.val < 17
    · let k : Fin 5 := ⟨g.val - 12, by omega⟩
      have hg : g = (⟨k.val + 12, by omega⟩ : Fin 18) := Fin.ext (by dsimp [k]; omega)
      rw [hg]
      simpa only [generatedFifthSectionGenerator, show ¬(k.val + 12 < 12) by omega,
        show k.val + 12 < 17 by omega, ↓reduceDIte, Nat.add_sub_cancel] using
          generatedNinth_affine_selected_binary k v
    · have hg : g = 17 := Fin.ext (by omega)
      subst g
      change leechBinaryAction co1XiIsometry v = _
      rw [generatedNinth_affine_original_columns.2]
      exact omegaOrbitIsometry_binary 0 v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
