/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ZeroFiberLocalization
public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# The actual additive image of the original identity row

The original row A→A→0 maps through F. Its canonical row Iso has the
identity on both image objects and mapZeroObject on the given quotient.
The first and last squares follow from F.map_id and F.map_zero. No row
Iso or matrix/source calibration outcome is supplied as an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uC vC uD vD

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive]

private def originalIdentityRowImageComputed (A : Core C) :
    (zeroRow A).toExtension.row.map F ≅ (zeroRow (F.core.obj A)).toExtension.row := by
  refine ShortComplex.isoMk (Iso.refl (F.obj A.of)) (Iso.refl (F.obj A.of))
    F.mapZeroObject ?_ ?_
  · change (𝟙 (F.obj A.of)) ≫ (𝟙 (F.obj A.of)) =
      F.map (𝟙 A.of) ≫ (𝟙 (F.obj A.of))
    rw [F.map_id]
  · change (𝟙 (F.obj A.of)) ≫ (0 : F.obj A.of ⟶ (0 : D)) =
      F.map (0 : A.of ⟶ (0 : C)) ≫ F.mapZeroObject.hom
    rw [F.map_zero]
    exact (Category.id_comp (0 : F.obj A.of ⟶ (0 : D))).trans
      (zero_comp : (0 : F.obj A.of ⟶ F.obj (0 : C)) ≫ F.mapZeroObject.hom = 0).symm

/-- The mapped identity row has identity coordinates and the canonical zero Iso. -/
public def mapZeroIdentityRowIso (A : Core C) :
    (zeroRow A).toExtension.row.map F ≅ (zeroRow (F.core.obj A)).toExtension.row :=
  originalIdentityRowImageComputed F A

private theorem originalIdentityRowImageComponents (A : Core C) :
    HEq (mapZeroIdentityRowIso F A).hom.τ₁ (𝟙 (F.obj A.of)) ∧
      HEq (mapZeroIdentityRowIso F A).hom.τ₂ (𝟙 (F.obj A.of)) ∧
      HEq (mapZeroIdentityRowIso F A).hom.τ₃ F.mapZeroObject.hom ∧
      HEq (mapZeroIdentityRowIso F A).inv.τ₁ (𝟙 (F.obj A.of)) ∧
      HEq (mapZeroIdentityRowIso F A).inv.τ₂ (𝟙 (F.obj A.of)) ∧
      HEq (mapZeroIdentityRowIso F A).inv.τ₃ F.mapZeroObject.inv :=
  ⟨heq_of_eq rfl, heq_of_eq rfl, heq_of_eq rfl,
    heq_of_eq rfl, heq_of_eq rfl, heq_of_eq rfl⟩

/-- All six forward/inverse row components have their literal canonical values. -/
public theorem mapZeroIdentityRowIso_components (A : Core C) :
    HEq (mapZeroIdentityRowIso F A).hom.τ₁ (𝟙 (F.obj A.of)) ∧
      HEq (mapZeroIdentityRowIso F A).hom.τ₂ (𝟙 (F.obj A.of)) ∧
      HEq (mapZeroIdentityRowIso F A).hom.τ₃ F.mapZeroObject.hom ∧
      HEq (mapZeroIdentityRowIso F A).inv.τ₁ (𝟙 (F.obj A.of)) ∧
      HEq (mapZeroIdentityRowIso F A).inv.τ₂ (𝟙 (F.obj A.of)) ∧
      HEq (mapZeroIdentityRowIso F A).inv.τ₃ F.mapZeroObject.inv :=
  originalIdentityRowImageComponents F A

end AlgebraicKTheory.FixedTargetExtension

end
