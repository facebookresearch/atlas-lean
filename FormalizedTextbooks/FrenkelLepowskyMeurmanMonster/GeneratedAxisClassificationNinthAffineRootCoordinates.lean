/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineMarkingData

/-! A literal left inverse checks independence of the eight discovered actual binary
section directions. Membership uses exact reconstruction, without a catalogue assumption. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The actual binary matrix of the eight proposed quotient-section directions. -/
def generatedNinthAffineRootMatrix : Matrix (Fin 24) (Fin 8) (ZMod 2) :=
  fun j k => monsterCo1GeometryBinaryMaskDecode (generatedNinthAffineRootMasks k) j

/-- A proposed sparse binary left inverse for these eight actual directions. -/
def generatedNinthAffineRootLeftInverse : Matrix (Fin 8) (Fin 24) (ZMod 2) := ![
    ![0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The sparse original coordinate equations certify independence of all eight directions. -/
theorem generatedNinth_affine_root_left_inverse :
    generatedNinthAffineRootLeftInverse * generatedNinthAffineRootMatrix = 1 := by
  decide +kernel

/-- The proposed binary section map is genuinely injective. -/
theorem generatedNinth_affine_root_map_injective :
    Function.Injective generatedNinthAffineRootMap := by
  intro a b hab
  have he := congrArg (fun v => generatedNinthAffineRootLeftInverse *ᵥ v) hab
  change generatedNinthAffineRootLeftInverse *ᵥ
      (generatedNinthAffineRootMatrix *ᵥ a) =
    generatedNinthAffineRootLeftInverse *ᵥ (generatedNinthAffineRootMatrix *ᵥ b) at he
  simpa only [Matrix.mulVec_mulVec, generatedNinth_affine_root_left_inverse,
    Matrix.one_mulVec] using he

/-- Exact reconstruction recognizes membership in the complete actual binary direction range. -/
theorem generatedNinth_affine_root_range_iff (v : Fin 24 → ZMod 2) :
    v ∈ generatedNinthAffineRootMap.range ↔
      generatedNinthAffineRootMatrix *ᵥ (generatedNinthAffineRootLeftInverse *ᵥ v) = v := by
  constructor
  · rintro ⟨a, rfl⟩
    change generatedNinthAffineRootMatrix *ᵥ
      (generatedNinthAffineRootLeftInverse *ᵥ
        (generatedNinthAffineRootMatrix *ᵥ a)) = generatedNinthAffineRootMatrix *ᵥ a
    have he : generatedNinthAffineRootLeftInverse *ᵥ
        (generatedNinthAffineRootMatrix *ᵥ a) = a := by
      rw [Matrix.mulVec_mulVec, generatedNinth_affine_root_left_inverse, Matrix.one_mulVec]
    rw [he]
  · intro he
    exact ⟨generatedNinthAffineRootLeftInverse *ᵥ v, he⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
