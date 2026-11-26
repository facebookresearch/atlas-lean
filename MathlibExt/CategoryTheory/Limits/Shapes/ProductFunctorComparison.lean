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
# Product comparisons under reindexing

Let F : C ⥤ D be a functor, f : I → C and g : J → C families, p : J → I a reindexing and q_j :
f(p(j)) → g(j) component maps. Suppose the products of f, g and their images under F exist.
The comparison κ_f : F(∏ᵢf(i)) → ∏ᵢF(f(i)) commutes with the reindexed product map:
F(Pi.map'(p,q)) ≫ κ_g = κ_f ≫ Pi.map'(p,F(q)).

The same equation applies to maps of products indexed by one type. The indexing, object and
morphism universes are independent; the comparison equation does not require F to preserve
products.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Product comparison for reindexed component maps.

Let F : C ⥤ D, p : J → I and q_j : f(p(j)) → g(j). If the products of f, g and their F-images
exist, their comparison maps satisfy F(Pi.map'(p,q)) ≫ κ_g = κ_f ≫ Pi.map'(p,F(q)). This
follows from the equation on each target projection and does not require product preservation. -/
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

/-- Product comparison for a common indexing type.

Let f,g : I → C and q_i : f(i) → g(i), with both products and their F-images defined. For any
functor F : C ⥤ D, the product comparison maps satisfy F(Pi.map(q)) ≫ κ_g = κ_f ≫
Pi.map(F(q)), where κ is the canonical map from the image of a product to the product of the
images. -/
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
