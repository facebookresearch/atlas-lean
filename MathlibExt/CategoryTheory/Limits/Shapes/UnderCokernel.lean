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

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Cokernels and the zero-arrow adjunction

Let C have zero morphisms and cokernels, and fix I : C. An object of Under I is an arrow α : I
→ X. Sending it to Coker(α), and a commuting under morphism to the induced map on cokernels,
defines a functor K : Under I ⥤ C. The functor Z : C ⥤ Under I sends Y to the zero arrow I → Y
and acts by the given underlying morphisms.

There is an adjunction K ⊣ Z. Its unit at α is the under morphism with right component q_α : X
→ Coker(α), and its counit at Y is the isomorphism Coker(0 : I → Y) ≅ Y. The hom equivalence
sends m : Coker(α) → Y to q_α ≫ m and its inverse takes the cokernel descendant of an under
morphism. Thus K preserves colimits of every indexing size. These constructions use zero
morphisms and cokernels, with independent object, morphism and indexing universes.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

noncomputable section

universe v u w w'

namespace CategoryTheory.Limits

open CategoryTheory Category

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C] (I : C)

/-- Cokernel functor on arrows with a fixed source.

In a category with zero morphisms and cokernels, fix I. Send α : I → X in Under I to Coker(α).
For an under morphism f : α → β, use the cokernel descendant of f.right ≫ cokernel.π(β), whose
composite with α is zero. -/
def underCokernel : Under I ⥤ C where
  obj X := cokernel X.hom
  map f := cokernel.desc _ (f.right ≫ cokernel.π _) (by
    rw [← Category.assoc, Under.w f, cokernel.condition])
  map_id X := by
    apply (cancel_epi (cokernel.π X.hom)).1
    simp only [cokernel.π_desc, Under.id_right, Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply (cancel_epi (cokernel.π _)).1
    simp only [cokernel.π_desc, cokernel.π_desc_assoc, Under.comp_right, Category.assoc]

/-- Object value of the fixed-source cokernel functor.

For α : I → X regarded as an object of Under I in a category with zero morphisms and
cokernels, underCokernel I takes α to Coker(α). -/
@[simp]
theorem underCokernel_obj (X : Under I) : (underCokernel I).obj X = cokernel X.hom := rfl

/-- Morphism value of the fixed-source cokernel functor.

For f : α → β in Under I, the map Coker(α) → Coker(β) is cokernel.desc α (f.right ≫ cokernel.π
β). The under-square equation and the cokernel condition show that α annihilates this
composite. -/
theorem underCokernel_map {X Y : Under I} (f : X ⟶ Y) :
    (underCokernel I).map f = cokernel.desc X.hom (f.right ≫ cokernel.π Y.hom)
      (by rw [← Category.assoc, Under.w f, cokernel.condition]) := rfl

/-- Projection equation for an under-category cokernel map.

For f : α → β in Under I, the induced cokernel map K(f) satisfies cokernel.π α ≫ K(f) =
f.right ≫ cokernel.π β. The category has zero morphisms and cokernels. -/
@[reassoc]
theorem underCokernel_π_map {X Y : Under I} (f : X ⟶ Y) :
    cokernel.π X.hom ≫ (underCokernel I).map f = f.right ≫ cokernel.π Y.hom :=
  cokernel.π_desc _ _ _

/-- Functor assigning the zero arrow from a fixed object.

For an object I in a category with zero morphisms, send Y to (0 : I → Y) in Under I. A map f :
X → Y becomes the under morphism with right component f. -/
def zeroUnder : C ⥤ Under I where
  obj Y := Under.mk (0 : I ⟶ Y)
  map f := Under.homMk f (by simp)
  map_id Y := Under.UnderMorphism.ext rfl
  map_comp f g := Under.UnderMorphism.ext rfl

omit [HasCokernels C] in
/-- Underlying target of a zero-arrow object.

For a category with zero morphisms and I,Y : C, the right object of zeroUnder I applied to Y
is Y itself. -/
@[simp]
theorem zeroUnder_obj_right (Y : C) : ((zeroUnder I).obj Y).right = Y := rfl

omit [HasCokernels C] in
/-- Structural arrow of a zero-arrow object.

For a category with zero morphisms and I,Y : C, the arrow defining zeroUnder I applied to Y is
0 : I → Y. -/
@[simp]
theorem zeroUnder_obj_hom (Y : C) : ((zeroUnder I).obj Y).hom = (0 : I ⟶ Y) := rfl

omit [HasCokernels C] in
/-- Underlying map of the zero-arrow functor.

For f : X → Y in a category with zero morphisms, the right component of zeroUnder I applied to
f is exactly f. -/
@[simp]
theorem zeroUnder_map_right {X Y : C} (f : X ⟶ Y) : ((zeroUnder I).map f).right = f := rfl

/-- Unit map from an arrow to its zero-arrow cokernel.

For C with zero morphisms and cokernels and fixed I, the natural transformation id_{Under I} →
underCokernel I ⋙ zeroUnder I has at α : I → X the under morphism whose right component is q_α
: X → Coker(α). The equation α ≫ q_α = 0 makes it an under morphism. -/
def underCokernelUnit : 𝟭 (Under I) ⟶ underCokernel I ⋙ zeroUnder I where
  app X := Under.homMk (cokernel.π X.hom) (cokernel.condition X.hom)
  naturality X Y f := by
    apply Under.UnderMorphism.ext
    change f.right ≫ cokernel.π Y.hom = cokernel.π X.hom ≫ (underCokernel I).map f
    exact (underCokernel_π_map I f).symm

/-- Right component of the fixed-source cokernel unit.

At α : I → X in Under I, the right component of underCokernelUnit I is the cokernel projection
q_α : X → Coker(α). -/
@[simp]
theorem underCokernelUnit_app_right (X : Under I) :
    ((underCokernelUnit I).app X).right = cokernel.π X.hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Counit from the cokernel of a zero arrow.

In a category with zero morphisms and cokernels, the natural transformation zeroUnder I ⋙
underCokernel I → id_C has component ε_Y : Coker(0 : I → Y) → Y, the hom of the canonical
zero-arrow cokernel isomorphism. -/
def underCokernelCounit : zeroUnder I ⋙ underCokernel I ⟶ 𝟭 C where
  app Y := (cokernelZeroIsoTarget (X := I) (Y := Y)).hom
  naturality X Y f := by
    apply (cancel_epi (cokernel.π (0 : I ⟶ X))).1
    change cokernel.π (0 : I ⟶ X) ≫
        ((underCokernel I).map ((zeroUnder I).map f) ≫
          (cokernelZeroIsoTarget (X := I) (Y := Y)).hom) =
      cokernel.π (0 : I ⟶ X) ≫ ((cokernelZeroIsoTarget (X := I) (Y := X)).hom ≫ f)
    erw [← Category.assoc, underCokernel_π_map I ((zeroUnder I).map f)]
    simp only [zeroUnder_map_right, zeroUnder_obj_hom, zeroUnder_obj_right,
      Category.assoc, cokernelZeroIsoTarget_hom,
      cokernel.π_desc, cokernel.π_desc_assoc, Category.comp_id, Category.id_comp]

/-- Component formula for the zero-arrow cokernel counit.

For Y : C, the component of underCokernelCounit I is the hom of cokernelZeroIsoTarget :
Coker(0 : I → Y) ≅ Y. -/
@[simp]
theorem underCokernelCounit_app (Y : C) :
    (underCokernelCounit I).app Y = (cokernelZeroIsoTarget (X := I) (Y := Y)).hom := rfl

/-- Counit equation with the zero-arrow cokernel projection.

For ε_Y : Coker(0 : I → Y) → Y, the counit satisfies cokernel.π(0 : I → Y) ≫ ε_Y = id_Y. The
category has zero morphisms and cokernels. -/
@[reassoc]
theorem underCokernelCounit_π (Y : C) :
    cokernel.π (0 : I ⟶ Y) ≫ (underCokernelCounit I).app Y = 𝟙 Y := by
  rw [underCokernelCounit_app, cokernelZeroIsoTarget_hom, cokernel.π_desc]

/-- Invertibility of each zero-arrow cokernel counit.

In a category with zero morphisms and cokernels, the component ε_Y : Coker(0 : I → Y) → Y of
underCokernelCounit I is invertible, since it is the hom of cokernelZeroIsoTarget. -/
instance underCokernelCounit_app_isIso (Y : C) : IsIso ((underCokernelCounit I).app Y) := by
  change IsIso ((cokernelZeroIsoTarget (X := I) (Y := Y)).hom)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Adjunction between fixed-source cokernels and zero arrows.

For C with zero morphisms and cokernels and I : C, underCokernel I is left adjoint to
zeroUnder I. Its unit has right component q_α : X → Coker(α), and its counit is Coker(0 : I →
Y) ≅ Y; the cokernel projection equations give the triangle identities. -/
def underCokernelAdjunction : underCokernel I ⊣ zeroUnder I where
  unit := underCokernelUnit I
  counit := underCokernelCounit I
  left_triangle_components X := by
    apply (cancel_epi (cokernel.π X.hom)).1
    erw [← Category.assoc, underCokernel_π_map I ((underCokernelUnit I).app X),
      underCokernelUnit_app_right, Category.assoc]
    erw [underCokernelCounit_π, Category.comp_id]
  right_triangle_components Y := by
    apply Under.UnderMorphism.ext
    change cokernel.π (0 : I ⟶ Y) ≫ (underCokernelCounit I).app Y = 𝟙 Y
    exact underCokernelCounit_π I Y

/-- Underlying unit component of the cokernel adjunction.

For α : I → X in Under I, the unit of underCokernel I ⊣ zeroUnder I has right component
cokernel.π α : X → Coker(α). -/
@[simp]
theorem underCokernelAdjunction_unit_app_right (X : Under I) :
    (((underCokernelAdjunction I).unit).app X).right = cokernel.π X.hom := rfl

/-- Counit component of the fixed-source cokernel adjunction.

At Y : C, the counit of underCokernel I ⊣ zeroUnder I is the hom of the canonical isomorphism
Coker(0 : I → Y) ≅ Y. -/
@[simp]
theorem underCokernelAdjunction_counit_app (Y : C) :
    ((underCokernelAdjunction I).counit).app Y =
      (cokernelZeroIsoTarget (X := I) (Y := Y)).hom := rfl

/-- Forward hom equivalence of the cokernel adjunction.

For α : I → X and m : Coker(α) → Y, the adjunction hom equivalence sends m to an under
morphism α → (0 : I → Y) with right component cokernel.π α ≫ m. -/
theorem underCokernelAdjunction_homEquiv_right (X : Under I) (Y : C)
    (f : (underCokernel I).obj X ⟶ Y) :
    ((underCokernelAdjunction I).homEquiv X Y f).right = cokernel.π X.hom ≫ f := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Inverse hom equivalence as a cokernel descendant.

For an under morphism f : α → (0 : I → Y), the inverse adjunction hom equivalence is
cokernel.desc α f.right. The under-square equation α ≫ f.right = 0 is precisely the
factorization condition for this descendant. -/
theorem underCokernelAdjunction_homEquiv_symm_apply (X : Under I) (Y : C)
    (f : X ⟶ (zeroUnder I).obj Y) :
    ((underCokernelAdjunction I).homEquiv X Y).symm f =
      cokernel.desc X.hom f.right (Under.w f) := by
  apply (cancel_epi (cokernel.π X.hom)).1
  change cokernel.π X.hom ≫
      ((underCokernel I).map f ≫ (underCokernelCounit I).app Y) =
    cokernel.π X.hom ≫ cokernel.desc X.hom f.right (Under.w f)
  erw [← Category.assoc, underCokernel_π_map I f, Category.assoc,
    underCokernelCounit_π, Category.comp_id, cokernel.π_desc]

/-- Colimit preservation by the fixed-source cokernel functor.

In a category with zero morphisms and cokernels, underCokernel I : Under I ⥤ C preserves
colimits of any indexing object and morphism universes. This follows from its adjunction as
the left adjoint to zeroUnder I. -/
instance underCokernel_preservesColimitsOfSize :
    PreservesColimitsOfSize.{w, w'} (underCokernel I) :=
  (underCokernelAdjunction I).leftAdjoint_preservesColimits

end CategoryTheory.Limits
