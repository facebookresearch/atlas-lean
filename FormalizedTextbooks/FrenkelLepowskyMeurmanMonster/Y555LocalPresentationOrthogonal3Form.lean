/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual original-source finite representation preserves its nonsingular Cartan form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Hom

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every lifted original source word preserves the actual characteristic-three Cartan form. -/
theorem y322Orthogonal3Lift_preserves (w : FreeGroup (Fin 8)) :
    (FreeGroup.lift y322Orthogonal3Generator w).val.transpose * y322Orthogonal3Gram *
      (FreeGroup.lift y322Orthogonal3Generator w).val = y322Orthogonal3Gram := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i =>
    simp only [FreeGroup.lift_apply_of, y322Orthogonal3Generator_matrix]
    exact y322Orthogonal3Reflection_preserves i
  | inv_of i _ =>
    simp only [map_inv, FreeGroup.lift_apply_of]
    change (y322Orthogonal3Reflection i).transpose * y322Orthogonal3Gram *
      y322Orthogonal3Reflection i = y322Orthogonal3Gram
    exact y322Orthogonal3Reflection_preserves i
  | mul a b ha hb =>
    simp only [map_mul, Units.val_mul, Matrix.transpose_mul]
    calc
      _ = (FreeGroup.lift y322Orthogonal3Generator b).val.transpose *
          ((FreeGroup.lift y322Orthogonal3Generator a).val.transpose *
            y322Orthogonal3Gram * (FreeGroup.lift y322Orthogonal3Generator a).val) *
          (FreeGroup.lift y322Orthogonal3Generator b).val := by simp only [mul_assoc]
      _ = y322Orthogonal3Gram := by rw [ha, hb]

/-- Every element of the genuine C322 presentation has actual form-preserving finite image. -/
theorem y322Orthogonal3Hom_preserves (x : Y322Presentation) :
    (y322Orthogonal3Hom x).val.transpose * y322Orthogonal3Gram *
      (y322Orthogonal3Hom x).val = y322Orthogonal3Gram := by
  induction x using PresentedGroup.induction_on with
  | H w =>
    change ((y322Orthogonal3Hom.comp (PresentedGroup.mk y322Relations)) w).val.transpose *
      y322Orthogonal3Gram * ((y322Orthogonal3Hom.comp (PresentedGroup.mk y322Relations)) w).val =
      y322Orthogonal3Gram
    rw [y322Orthogonal3Hom_quotient]
    exact y322Orthogonal3Lift_preserves w

/-- The actual finite source image consists of isometries of the explicit nonsingular form. -/
theorem y322Orthogonal3Image_preserves
    (x : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) (hx : x ∈ y322Orthogonal3Image) :
    x.val.transpose * y322Orthogonal3Gram * x.val = y322Orthogonal3Gram := by
  obtain ⟨g, rfl⟩ := hx
  exact y322Orthogonal3Hom_preserves g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
