/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact fixed-vector and subspace actions of all actual original C322 words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3C322Hom

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Every actual original linear source word fixes the nonzero complement vector. -/
theorem y422Orthogonal3C322Lift_fixed (w : FreeGroup (Fin 8)) :
    (FreeGroup.lift y422Orthogonal3C322Generator w).val *ᵥ y422Orthogonal3FixedVector =
      y422Orthogonal3FixedVector := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i =>
    simp only [FreeGroup.lift_apply_of]
    exact y422Orthogonal3C322_generator_fixed i
  | inv_of i _ =>
    simp only [map_inv, FreeGroup.lift_apply_of]
    change y422Orthogonal3Reflection (y422C322Letter i) *ᵥ y422Orthogonal3FixedVector = _
    exact y422Orthogonal3C322_generator_fixed i
  | mul a b ha hb =>
    simp only [map_mul, Units.val_mul]
    rw [← Matrix.mulVec_mulVec, hb, ha]

/-- Every actual original source lift intertwines with the faithful seven-dimensional lift. -/
theorem y422Orthogonal3C322Lift_intertwines (w : FreeGroup (Fin 8)) :
    (FreeGroup.lift y422Orthogonal3C322Generator w).val * y422Orthogonal3C322Embedding =
      y422Orthogonal3C322Embedding * (FreeGroup.lift y322Orthogonal3Generator w).val := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i =>
    simp only [FreeGroup.lift_apply_of]
    exact y422Orthogonal3C322_generator_intertwines i
  | inv_of i _ =>
    simp only [map_inv, FreeGroup.lift_apply_of]
    change y422Orthogonal3Reflection (y422C322Letter i) * y422Orthogonal3C322Embedding =
      y422Orthogonal3C322Embedding * y322Orthogonal3Reflection i
    exact y422Orthogonal3C322_generator_intertwines i
  | mul a b ha hb =>
    simp only [map_mul, Units.val_mul]
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]

/-- Every actual original C322 element fixes the nonzero complement vector in the linear lift. -/
theorem y422Orthogonal3C322Hom_fixed (x : Y322Presentation) :
    (y422Orthogonal3C322Hom x).val *ᵥ y422Orthogonal3FixedVector =
      y422Orthogonal3FixedVector := by
  induction x using PresentedGroup.induction_on with
  | H w =>
    change ((y422Orthogonal3C322Hom.comp (PresentedGroup.mk y322Relations)) w).val *ᵥ
      y422Orthogonal3FixedVector = y422Orthogonal3FixedVector
    rw [y422Orthogonal3C322Hom_quotient]
    exact y422Orthogonal3C322Lift_fixed w

/-- Every actual original C322 element acts on the source Cartan subspace by its faithful action. -/
theorem y422Orthogonal3C322Hom_intertwines (x : Y322Presentation) :
    (y422Orthogonal3C322Hom x).val * y422Orthogonal3C322Embedding =
      y422Orthogonal3C322Embedding * (y322Orthogonal3Hom x).val := by
  induction x using PresentedGroup.induction_on with
  | H w =>
    change ((y422Orthogonal3C322Hom.comp (PresentedGroup.mk y322Relations)) w).val *
      y422Orthogonal3C322Embedding = y422Orthogonal3C322Embedding *
        ((y322Orthogonal3Hom.comp (PresentedGroup.mk y322Relations)) w).val
    rw [y422Orthogonal3C322Hom_quotient, y322Orthogonal3Hom_quotient]
    exact y422Orthogonal3C322Lift_intertwines w

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
