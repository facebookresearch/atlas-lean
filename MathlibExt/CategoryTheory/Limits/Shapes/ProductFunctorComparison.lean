/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Functor comparison for product reindexing

The native product comparison commutes with reindexing and the maps on the
individual factors. The source and target products can have different index
types. This applies to shifts of towers and to product presentations of faces.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The native product comparison commutes with arbitrary reindexing and
maps on the individual factors. -/
@[reassoc]
theorem Pi.map'_piComparison
    (F : C ⥤ D) {I : Type w₁} {J : Type w₂}
    {f : I → C} {g : J → C}
    [HasProduct f] [HasProduct g]
    [HasProduct (fun i => F.obj (f i))]
    [HasProduct (fun j => F.obj (g j))]
    (p : J → I) (q : ∀ j, f (p j) ⟶ g j) :
    F.map (Pi.map' p q) ≫ piComparison F g =
      piComparison F f ≫ Pi.map' p (fun j => F.map (q j)) := by
  change F.map (Pi.lift (fun j => Pi.π f (p j) ≫ q j)) ≫
    piComparison F g = _
  rw [map_lift_piComparison]
  apply Pi.hom_ext
  intro j
  simp only [Pi.lift_comp_π, Functor.map_comp, Category.assoc,
    Pi.map'_comp_π, piComparison_comp_π_assoc]

/-- The same comparison for products indexed by the same type. -/
@[reassoc]
theorem Pi.map_piComparison
    (F : C ⥤ D) {I : Type w₁} {f g : I → C}
    [HasProduct f] [HasProduct g]
    [HasProduct (fun i => F.obj (f i))]
    [HasProduct (fun i => F.obj (g i))]
    (q : ∀ i, f i ⟶ g i) :
    F.map (Pi.map q) ≫ piComparison F g =
      piComparison F f ≫ Pi.map (fun i => F.map (q i)) := by
  simpa only [Pi.map'_id] using Pi.map'_piComparison F id q

end CategoryTheory.Limits
