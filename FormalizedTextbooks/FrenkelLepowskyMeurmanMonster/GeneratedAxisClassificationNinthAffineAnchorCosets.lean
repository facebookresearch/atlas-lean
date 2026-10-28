/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineRootCoordinates

/-! The actual nine marking anchors have distinct cosets modulo the complete discovered
binary direction range. Only original marking coordinates and a checked left inverse are used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The actual linear residual from reconstruction in the eight-direction range. -/
def generatedNinthAffineRootResidual :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  LinearMap.id - generatedNinthAffineRootMap.comp
    (Matrix.mulVecLin generatedNinthAffineRootLeftInverse)

/-- Proposed residual labels of the nine original marking anchors. -/
def generatedNinthAffineAnchorResidualLabels : Fin 9 → ℕ :=
  ![2195456, 8986632, 10027904, 11084698, 15761426, 13730824, 14755712, 15738778, 11043858]

/-- The actual residual vanishes on every member of the complete direction range. -/
theorem generatedNinth_affine_root_residual_zero (v : Fin 24 → ZMod 2)
    (hv : v ∈ generatedNinthAffineRootMap.range) :
    generatedNinthAffineRootResidual v = 0 := by
  change v - generatedNinthAffineRootMatrix *ᵥ
    (generatedNinthAffineRootLeftInverse *ᵥ v) = 0
  rw [(generatedNinth_affine_root_range_iff v).mp hv, sub_self]

set_option maxHeartbeats 4000000 in
-- Check the216 actual coordinate bits of the nine source-marking anchor residuals.
/-- Every residual label agrees with its actual original marking coordinate. -/
theorem generatedNinth_affine_anchor_residual_coordinates : ∀ i : Fin 9,
    generatedNinthAffineRootResidual (monsterCo1GeometryBinaryMaskDecode
      (generatedNinthMarkingMask (generatedNinthAffineAnchorIndex i))) =
        monsterCo1GeometryBinaryMaskDecode (generatedNinthAffineAnchorResidualLabels i) := by
  decide +kernel

/-- The nine actual residual vectors are all different. -/
theorem generatedNinth_affine_anchor_residual_injective :
    Function.Injective (fun i : Fin 9 => monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedNinthAffineAnchorResidualLabels i)) := by
  decide +kernel

/-- Distinct original marking anchors have different cosets in the whole direction range. -/
theorem generatedNinth_affine_anchor_cosets_distinct (i j : Fin 9) (hij : i ≠ j) :
    monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedNinthMarkingMask (generatedNinthAffineAnchorIndex i)) -
      monsterCo1GeometryBinaryMaskDecode
        (generatedNinthMarkingMask (generatedNinthAffineAnchorIndex j)) ∉
      generatedNinthAffineRootMap.range := by
  intro hr
  have hz := generatedNinth_affine_root_residual_zero _ hr
  rw [map_sub, generatedNinth_affine_anchor_residual_coordinates,
    generatedNinth_affine_anchor_residual_coordinates] at hz
  exact hij (generatedNinth_affine_anchor_residual_injective (sub_eq_zero.mp hz))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
