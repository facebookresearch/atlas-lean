/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete matrix and short-vector coordinates on the actual involution's fixed space. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerBlocks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SymmetricJordanAutomorphism

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The symmetric matrix encoded by an actual Griess vector. -/
noncomputable def griessConwaySym24 (x : GriessSpace) : Sym24 :=
  ⟨(griessConwayEncode x).1, by
    rw [mem_Sym24]
    ext i j
    exact griessConwayEncode_symmetric x j i⟩

/-- Encoding restricted to the actual positive eigenspace. -/
noncomputable def generatedCentralPlusEncode :
    generatedCentralPlus →ₗ[ℝ] (Sym24 × (GriessShortIndex → ℝ)) where
  toFun x := (griessConwaySym24 x.val, (griessConwayEncode x.val).2.1)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun b : ConwayRawSpace => b.1)
        (griessConwayEncodeLinear.map_add x.val y.val)
    · exact congrArg (fun b : ConwayRawSpace => b.2.1)
        (griessConwayEncodeLinear.map_add x.val y.val)
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun b : ConwayRawSpace => b.1)
        (griessConwayEncodeLinear.map_smul c x.val)
    · exact congrArg (fun b : ConwayRawSpace => b.2.1)
        (griessConwayEncodeLinear.map_smul c x.val)

/-- The actual inverse dictionary has tensor coordinate zero. -/
noncomputable def generatedCentralPlusEmbed
    (A : Sym24) (X : GriessShortIndex → ℝ) : generatedCentralPlus :=
  ⟨griessConwayDecode (A.val, (X, 0)), by
    rw [mem_generatedCentralPlus_iff_tensor_zero]
    have h := griessConwayEncode_decode (A.val, (X, 0)) (by
      intro i j
      exact congrArg (fun B : Matrix (Fin 24) (Fin 24) ℝ => B j i) A.property)
    exact congrArg (fun b : ConwayRawSpace => b.2.2) h⟩

@[simp] theorem generatedCentralPlusEmbed_val (A : Sym24) (X : GriessShortIndex → ℝ) :
    (generatedCentralPlusEmbed A X).val = griessConwayDecode (A.val, (X, 0)) := rfl

theorem generatedCentralPlusEmbed_encode (A : Sym24) (X : GriessShortIndex → ℝ) :
    griessConwayEncode (generatedCentralPlusEmbed A X).val = (A.val, (X, 0)) := by
  exact griessConwayEncode_decode _ (by
    intro i j
    exact congrArg (fun B : Matrix (Fin 24) (Fin 24) ℝ => B j i) A.property)

/-- Coordinates of the actual positive eigenspace, with the original Conway decoder as inverse. -/
noncomputable def generatedCentralPlusCoordinates :
    generatedCentralPlus ≃ₗ[ℝ] (Sym24 × (GriessShortIndex → ℝ)) :=
  { generatedCentralPlusEncode with
    invFun := fun p => generatedCentralPlusEmbed p.1 p.2
    left_inv := by
      intro x
      apply Subtype.ext
      change griessConwayDecode
        ((griessConwayEncode x.val).1, ((griessConwayEncode x.val).2.1, 0)) = x.val
      have ht := (mem_generatedCentralPlus_iff_tensor_zero x.val).mp x.property
      rw [← ht]
      exact griessConwayDecode_encode x.val
    right_inv := by
      intro p
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun b : ConwayRawSpace => b.1)
          (generatedCentralPlusEmbed_encode p.1 p.2)
      · exact congrArg (fun b : ConwayRawSpace => b.2.1)
          (generatedCentralPlusEmbed_encode p.1 p.2) }

@[simp] theorem generatedCentralPlusCoordinates_fst_val (x : generatedCentralPlus) :
    (generatedCentralPlusCoordinates x).1.val = (griessConwayEncode x.val).1 := rfl

@[simp] theorem generatedCentralPlusCoordinates_snd (x : generatedCentralPlus) :
    (generatedCentralPlusCoordinates x).2 = (griessConwayEncode x.val).2.1 := rfl

@[simp] theorem generatedCentralPlusCoordinates_symm_apply
    (A : Sym24) (X : GriessShortIndex → ℝ) :
    generatedCentralPlusCoordinates.symm (A, X) = generatedCentralPlusEmbed A X := rfl

/-- The original Griess form on the fixed space is the direct sum of these two pairings. -/
theorem generatedCentralPlus_griessForm_coordinates (x y : generatedCentralPlus) :
    griessForm x.val y.val =
      (∑ i, ∑ j, (generatedCentralPlusCoordinates x).1.val i j *
        (generatedCentralPlusCoordinates y).1.val i j) +
      ∑ r, (generatedCentralPlusCoordinates x).2 r *
        (generatedCentralPlusCoordinates y).2 r := by
  rw [griessForm_eq_conwayRawForm]
  have hx := (mem_generatedCentralPlus_iff_tensor_zero x.val).mp x.property
  have hy := (mem_generatedCentralPlus_iff_tensor_zero y.val).mp y.property
  simp only [conwayRawForm, conwayMatrixForm_eq_sum, hx, hy]
  simp [conwayTensorForm]

theorem generatedCentralPlusEmbed_griessForm
    (A B : Sym24) (X Y : GriessShortIndex → ℝ) :
    griessForm (generatedCentralPlusEmbed A X).val (generatedCentralPlusEmbed B Y).val =
      (∑ i, ∑ j, A.val i j * B.val i j) + ∑ r, X r * Y r := by
  simpa only [← generatedCentralPlusCoordinates_symm_apply,
    LinearEquiv.apply_symm_apply] using
    generatedCentralPlus_griessForm_coordinates
      (generatedCentralPlusEmbed A X) (generatedCentralPlusEmbed B Y)

/-- The actual matrix constituent inside the positive eigenspace. -/
noncomputable def generatedCentralMatrix : Submodule ℝ generatedCentralPlus :=
  ((LinearMap.snd ℝ Sym24 (GriessShortIndex → ℝ)).comp
    generatedCentralPlusCoordinates.toLinearMap).ker

/-- The actual short-vector constituent inside the positive eigenspace. -/
noncomputable def generatedCentralShort : Submodule ℝ generatedCentralPlus :=
  ((LinearMap.fst ℝ Sym24 (GriessShortIndex → ℝ)).comp
    generatedCentralPlusCoordinates.toLinearMap).ker

@[simp] theorem mem_generatedCentralMatrix (x : generatedCentralPlus) :
    x ∈ generatedCentralMatrix ↔ (generatedCentralPlusCoordinates x).2 = 0 := Iff.rfl

@[simp] theorem mem_generatedCentralShort (x : generatedCentralPlus) :
    x ∈ generatedCentralShort ↔ (generatedCentralPlusCoordinates x).1 = 0 := Iff.rfl

theorem mem_generatedCentralMatrix_iff_short_zero (x : generatedCentralPlus) :
    x ∈ generatedCentralMatrix ↔ (griessConwayEncode x.val).2.1 = 0 := Iff.rfl

theorem mem_generatedCentralShort_iff_matrix_zero (x : generatedCentralPlus) :
    x ∈ generatedCentralShort ↔ (griessConwayEncode x.val).1 = 0 := by
  rw [mem_generatedCentralShort]
  exact Subtype.ext_iff

theorem generatedCentralPlusEmbed_mem_matrix (A : Sym24) :
    generatedCentralPlusEmbed A 0 ∈ generatedCentralMatrix := by
  rw [mem_generatedCentralMatrix, ← generatedCentralPlusCoordinates_symm_apply,
    LinearEquiv.apply_symm_apply]

theorem generatedCentralPlusEmbed_mem_short (X : GriessShortIndex → ℝ) :
    generatedCentralPlusEmbed 0 X ∈ generatedCentralShort := by
  rw [mem_generatedCentralShort, ← generatedCentralPlusCoordinates_symm_apply,
    LinearEquiv.apply_symm_apply]

theorem generatedCentralPlus_matrix_short_decomposition (x : generatedCentralPlus) :
    x = generatedCentralPlusEmbed (generatedCentralPlusCoordinates x).1 0 +
      generatedCentralPlusEmbed 0 (generatedCentralPlusCoordinates x).2 := by
  apply generatedCentralPlusCoordinates.injective
  rw [map_add, ← generatedCentralPlusCoordinates_symm_apply,
    ← generatedCentralPlusCoordinates_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact (Prod.ext (by simp) (by simp)).symm

theorem generatedCentralMatrix_short_orthogonal (x y : generatedCentralPlus)
    (hx : x ∈ generatedCentralMatrix) (hy : y ∈ generatedCentralShort) :
    griessForm x.val y.val = 0 := by
  rw [mem_generatedCentralMatrix] at hx
  rw [mem_generatedCentralShort] at hy
  rw [generatedCentralPlus_griessForm_coordinates, hy, hx]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
