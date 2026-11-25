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
# The cokernel adjunction for a fixed under category

For an arbitrary object `I`, taking the actual cokernel of an arrow
`I ⟶ X` is left adjoint to sending `Y` to the zero arrow `I ⟶ Y`.
The construction uses zero morphisms and cokernels, with no zero-object
or abelian-category hypothesis. Its unit is the original cokernel
projection, and its counit is the original zero-arrow cokernel isomorphism.
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

/-- The actual cokernel of each arrow with the fixed source `I`. -/
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

@[simp]
theorem underCokernel_obj (X : Under I) : (underCokernel I).obj X = cokernel X.hom := rfl

/-- The map is the original cokernel descendant of the right component. -/
theorem underCokernel_map {X Y : Under I} (f : X ⟶ Y) :
    (underCokernel I).map f = cokernel.desc X.hom (f.right ≫ cokernel.π Y.hom)
      (by rw [← Category.assoc, Under.w f, cokernel.condition]) := rfl

/-- The original right component gives the actual cokernel projection square. -/
@[reassoc]
theorem underCokernel_π_map {X Y : Under I} (f : X ⟶ Y) :
    cokernel.π X.hom ≫ (underCokernel I).map f = f.right ≫ cokernel.π Y.hom :=
  cokernel.π_desc _ _ _

/-- The zero arrow from the same fixed source `I`, on actual underlying morphisms. -/
def zeroUnder : C ⥤ Under I where
  obj Y := Under.mk (0 : I ⟶ Y)
  map f := Under.homMk f (by simp)
  map_id Y := Under.UnderMorphism.ext rfl
  map_comp f g := Under.UnderMorphism.ext rfl

omit [HasCokernels C] in
@[simp]
theorem zeroUnder_obj_right (Y : C) : ((zeroUnder I).obj Y).right = Y := rfl

omit [HasCokernels C] in
@[simp]
theorem zeroUnder_obj_hom (Y : C) : ((zeroUnder I).obj Y).hom = (0 : I ⟶ Y) := rfl

omit [HasCokernels C] in
@[simp]
theorem zeroUnder_map_right {X Y : C} (f : X ⟶ Y) : ((zeroUnder I).map f).right = f := rfl

/-- The actual original cokernel projection, as the unit in `Under I`. -/
def underCokernelUnit : 𝟭 (Under I) ⟶ underCokernel I ⋙ zeroUnder I where
  app X := Under.homMk (cokernel.π X.hom) (cokernel.condition X.hom)
  naturality X Y f := by
    apply Under.UnderMorphism.ext
    change f.right ≫ cokernel.π Y.hom = cokernel.π X.hom ≫ (underCokernel I).map f
    exact (underCokernel_π_map I f).symm

@[simp]
theorem underCokernelUnit_app_right (X : Under I) :
    ((underCokernelUnit I).app X).right = cokernel.π X.hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original zero-arrow cokernel isomorphism is the counit. -/
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

@[simp]
theorem underCokernelCounit_app (Y : C) :
    (underCokernelCounit I).app Y = (cokernelZeroIsoTarget (X := I) (Y := Y)).hom := rfl

/-- The counit reverses the original zero-arrow cokernel projection. -/
@[reassoc]
theorem underCokernelCounit_π (Y : C) :
    cokernel.π (0 : I ⟶ Y) ≫ (underCokernelCounit I).app Y = 𝟙 Y := by
  rw [underCokernelCounit_app, cokernelZeroIsoTarget_hom, cokernel.π_desc]

instance underCokernelCounit_app_isIso (Y : C) : IsIso ((underCokernelCounit I).app Y) := by
  change IsIso ((cokernelZeroIsoTarget (X := I) (Y := Y)).hom)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Taking a cokernel is left adjoint to the actual zero-arrow functor from the same source. -/
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

@[simp]
theorem underCokernelAdjunction_unit_app_right (X : Under I) :
    (((underCokernelAdjunction I).unit).app X).right = cokernel.π X.hom := rfl

@[simp]
theorem underCokernelAdjunction_counit_app (Y : C) :
    ((underCokernelAdjunction I).counit).app Y =
      (cokernelZeroIsoTarget (X := I) (Y := Y)).hom := rfl

/-- The forward hom equivalence is composition with the original cokernel projection. -/
theorem underCokernelAdjunction_homEquiv_right (X : Under I) (Y : C)
    (f : (underCokernel I).obj X ⟶ Y) :
    ((underCokernelAdjunction I).homEquiv X Y f).right = cokernel.π X.hom ≫ f := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse hom equivalence is the actual cokernel descendant of the right component. -/
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

/-- The actual fixed-source cokernel left adjoint preserves colimits of every size. -/
instance underCokernel_preservesColimitsOfSize :
    PreservesColimitsOfSize.{w, w'} (underCokernel I) :=
  (underCokernelAdjunction I).leftAdjoint_preservesColimits

end CategoryTheory.Limits
