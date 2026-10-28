/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineSignedWords

/-! The eleven full binary matrices are the actions of the literal genuine source words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every original inverse section letter has its entire proposed genuine binary action. -/
theorem generatedNinth_affine_section_inverse_binary (g : Fin 18) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedFifthSectionGenerator g)⁻¹ v =
      sixthFrameOrbitColumnMatrix (generatedNinthAffineSectionInverseColumns g) *ᵥ v := by
  have hm : sixthFrameOrbitColumnMatrix (generatedNinthAffineSectionColumns g) *
      sixthFrameOrbitColumnMatrix (generatedNinthAffineSectionInverseColumns g) = 1 := by
    ext i j
    have h := congrArg (fun v => monsterCo1GeometryBinaryMaskDecode (n := 24) v i)
      ((generatedNinth_affine_section_inverse_columns g).1 j)
    rw [sixthFrameOrbitMaskApply_decode, generatedNinth_affine_binary_basis_decode] at h
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.mulVec_single_one,
      sixthFrameOrbitColumnMatrix, monsterCo1GeometryBinaryMaskMatrix, Matrix.transpose_apply,
      Pi.single_apply, Matrix.one_apply] using h
  apply (leechBinaryAction (generatedFifthSectionGenerator g)).injective
  rw [map_inv]
  change (leechBinaryAction (generatedFifthSectionGenerator g))
      ((leechBinaryAction (generatedFifthSectionGenerator g)).symm v) = _
  rw [LinearEquiv.apply_symm_apply, generatedNinth_affine_section_binary,
    Matrix.mulVec_mulVec, hm, Matrix.one_mulVec]

/-- Either genuine orientation of every section source letter has the whole packed action. -/
theorem generatedNinth_affine_section_letter_packed (l : Fin 18 × Bool) (v : ℕ) :
    leechBinaryAction (generatedNinthAffineSectionLetter l)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply (generatedNinthAffineSectionLetterColumns l) v) := by
  rcases l with ⟨g, b⟩
  cases b
  · change leechBinaryAction (generatedFifthSectionGenerator g)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply (generatedNinthAffineSectionColumns g) v)
    rw [generatedNinth_affine_section_binary]
    exact (sixthFrameOrbitMaskApply_decode _ _).symm
  · change leechBinaryAction (generatedFifthSectionGenerator g)⁻¹
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply (generatedNinthAffineSectionInverseColumns g) v)
    rw [generatedNinth_affine_section_inverse_binary]
    exact (sixthFrameOrbitMaskApply_decode _ _).symm

/-- Whole original section source words retain the exact entire packed action. -/
theorem generatedNinth_affine_section_word_packed (w : List (Fin 18 × Bool)) (v : ℕ) :
    leechBinaryAction ((w.map generatedNinthAffineSectionLetter).prod)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthAffineSectionMaskWord w v) := by
  induction w with
  | nil => rw [List.map_nil, List.prod_nil, map_one]; rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, map_mul]
    change leechBinaryAction (generatedNinthAffineSectionLetter l)
        (leechBinaryAction ((w.map generatedNinthAffineSectionLetter).prod)
          (monsterCo1GeometryBinaryMaskDecode (n := 24) v)) =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply (generatedNinthAffineSectionLetterColumns l)
          (generatedNinthAffineSectionMaskWord w v))
    rw [ih, generatedNinth_affine_section_letter_packed]

/-- The eleven literal whole section words are genuine lattice isometries. -/
def generatedNinthAffineLowerSourceIsometry (k : Fin 11) : leechIsomSubgroup :=
  ((generatedNinthAffineLowerSourceWord k).map generatedNinthAffineSectionLetter).prod

/-- Every complete original lower source word has its entire proposed binary matrix action. -/
theorem generatedNinth_affine_lower_source_binary (k : Fin 11) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedNinthAffineLowerSourceIsometry k) v =
      sixthFrameOrbitColumnMatrix (generatedNinthAffineLowerSourceColumns k) *ᵥ v := by
  have h : (leechBinaryAction (generatedNinthAffineLowerSourceIsometry k)).toLinearMap =
      Matrix.mulVecLin (sixthFrameOrbitColumnMatrix
        (generatedNinthAffineLowerSourceColumns k)) := by
    apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
    intro j
    have hj := generatedNinth_affine_section_word_packed (generatedNinthAffineLowerSourceWord k)
      (2 ^ j.val)
    rw [generatedNinth_affine_binary_basis_decode, generatedNinth_affine_lower_source_columns]
      at hj
    simpa only [generatedNinthAffineLowerSourceIsometry, Pi.basisFun_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_single_one, sixthFrameOrbitColumnMatrix,
      monsterCo1GeometryBinaryMaskMatrix, Matrix.col, Matrix.transpose_apply,
      Matrix.transpose_transpose, LinearEquiv.coe_coe] using hj
  exact LinearMap.congr_fun h v

/-- All nine entire kernel orbit matrices are actions of their complete genuine source words. -/
theorem generatedNinth_affine_lower_kernel_packed (k : Fin 9) (v : ℕ) :
    leechBinaryAction (generatedNinthAffineLowerSourceIsometry ⟨k.val, by omega⟩)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) v) =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply (generatedNinthAffineKernelColumns k) v) := by
  rw [generatedNinth_affine_lower_source_binary, generatedNinth_affine_lower_kernel_columns]
  exact (sixthFrameOrbitMaskApply_decode _ _).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
