/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineRootCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsLabels

/-! Exact eight-direction coordinates bind the four affine-fiber directions to the
proposed whole section range. The finite formulas use the original144 marking masks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Eight-bit coordinates of the four original difference directions in each fiber. -/
def generatedNinthAffineDirectionRootLabels : Fin 9 → Fin 4 → Fin 256 := ![
    ![1, 2, 4, 8],
    ![24, 64, 232, 134],
    ![36, 125, 238, 133],
    ![26, 71, 210, 184],
    ![38, 122, 212, 187],
    ![25, 123, 214, 129],
    ![37, 70, 208, 130],
    ![27, 124, 236, 191],
    ![39, 65, 234, 188]]

/-- The intrinsic four-direction map into the proposed eight-dimensional section. -/
def generatedNinthAffineDirectionRootMatrix (i : Fin 9) :
    Matrix (Fin 8) (Fin 4) (ZMod 2) :=
  fun j k => generatedAxisE8FrameLabelBits (generatedNinthAffineDirectionRootLabels i k) j

/-- The intrinsic four-direction map into the proposed eight-dimensional section. -/
def generatedNinthAffineDirectionRootMap (i : Fin 9) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  Matrix.mulVecLin (generatedNinthAffineDirectionRootMatrix i)

set_option maxHeartbeats 4000000 in
-- Only36 actual source direction vectors are reconstructed in the eight-direction basis.
/-- Each original affine difference direction has the specified genuine root coordinates. -/
theorem generatedNinth_affine_direction_root_coordinates : ∀ (i : Fin 9) (k : Fin 4),
    generatedNinthAffineRootMap
      (generatedAxisE8FrameLabelBits (generatedNinthAffineDirectionRootLabels i k)) =
        monsterCo1GeometryBinaryMaskDecode (generatedNinthAffineDirectionMasks i k) := by
  decide +kernel

/-- The complete actual linear direction map factors through the eight-direction range. -/
theorem generatedNinth_affine_direction_factorization (i : Fin 9) :
    generatedNinthAffineRootMap.comp (generatedNinthAffineDirectionRootMap i) =
      generatedNinthAffineDirectionMap i := by
  let D : Matrix (Fin 24) (Fin 4) (ZMod 2) :=
    fun j k => monsterCo1GeometryBinaryMaskDecode (generatedNinthAffineDirectionMasks i k) j
  have hm : generatedNinthAffineRootMatrix * generatedNinthAffineDirectionRootMatrix i = D := by
    ext j k
    exact congrFun (generatedNinth_affine_direction_root_coordinates i k) j
  apply LinearMap.ext
  intro a
  change generatedNinthAffineRootMatrix *ᵥ
      (generatedNinthAffineDirectionRootMatrix i *ᵥ a) = D *ᵥ a
  rw [Matrix.mulVec_mulVec, hm]

/-- Every original affine fiber direction belongs to the whole actual eight-direction range. -/
theorem generatedNinth_affine_direction_range_le (i : Fin 9) :
    (generatedNinthAffineDirectionMap i).range ≤ generatedNinthAffineRootMap.range := by
  rintro v ⟨a, rfl⟩
  refine ⟨generatedNinthAffineDirectionRootMap i a, ?_⟩
  exact LinearMap.congr_fun (generatedNinth_affine_direction_factorization i) a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
