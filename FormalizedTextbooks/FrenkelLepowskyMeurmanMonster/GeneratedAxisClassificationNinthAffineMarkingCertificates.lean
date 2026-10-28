/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineMarkingData

/-! The original144 markings are reordered, without omission, into nine actual affine
four-coordinate fibers. Their coordinates are checked against the frozen original masks.
The full intrinsic spread identification remains separate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The finite sixteen-label encoder is a bijection on binary four-coordinate vectors. -/
theorem generatedNinth_affine_coefficient_label_bijective :
    Function.Bijective generatedNinthAffineCoefficientLabel := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- The144 literal original indices are checked as a complete finite reordering.
/-- Each original marking appears once in the nine-by-sixteen index table. -/
theorem generatedNinth_affine_marking_index_bijective :
    Function.Bijective (fun p : Fin 9 × Fin 16 => generatedNinthAffineMarkingIndex p.1 p.2) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
-- Bind all144 actual binary vectors to their original source masks and affine directions.
/-- The four actual difference directions generate every original marked point in its fiber. -/
theorem generatedNinth_affine_marking_coordinates :
    ∀ (i : Fin 9) (a : Fin 4 → ZMod 2),
    monsterCo1GeometryBinaryMaskDecode (generatedNinthMarkingMask
      (generatedNinthAffineMarkingIndex i (generatedNinthAffineCoefficientLabel a))) =
      monsterCo1GeometryBinaryMaskDecode
        (generatedNinthMarkingMask (generatedNinthAffineAnchorIndex i)) +
          generatedNinthAffineDirectionMap i a := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
-- Each of the nine maps has only sixteen possible inputs.
/-- No nonzero fiber coefficient vector maps to the zero actual difference. -/
theorem generatedNinth_affine_direction_kernel :
    ∀ (i : Fin 9) (a : Fin 4 → ZMod 2),
      generatedNinthAffineDirectionMap i a = 0 → a = 0 := by
  decide +kernel

/-- Every displayed affine fiber has four independent actual binary directions. -/
theorem generatedNinth_affine_direction_injective (i : Fin 9) :
    Function.Injective (generatedNinthAffineDirectionMap i) := by
  intro a b hab
  have hz : generatedNinthAffineDirectionMap i (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (generatedNinth_affine_direction_kernel i (a - b) hz)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
