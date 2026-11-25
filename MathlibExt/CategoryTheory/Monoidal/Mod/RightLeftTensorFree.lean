/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorHom

/-!
# Naturality of balanced tensor with a free module

For a right module carrier `N` and a base object `X`, `freeTensorIso`
identifies the balanced tensor of `N` with the free left module on `X`
with `N.X ⊗ X`.
The isomorphism is natural jointly in morphisms of right module carriers
and maps of generators, and gives natural isomorphisms of tensor functors.
`freeCoefficientArrowIso` and `freeGeneratorArrowIso` express the same
comparisons in the arrow category, while the inverse formula uses the
free–forgetful adjunction unit and the balanced-tensor projection.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.RightLeftTensor

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A] [HasColimitsOfSize.{0, 0} C]

omit [HasColimitsOfSize.{0, 0} C] in
theorem freeModuleMap_carrier {X Y : C} (g : X ⟶ Y) :
    ((Mod.free A).map g).hom = A ◁ g := rfl

/-- Every original right coefficient and base map occurs in the same reduction square. -/
theorem freeTensorIso_naturality {N N' : RightModuleFree.Carrier A}
    (f : N ⟶ N') {X Y : C} (g : X ⟶ Y) :
    tensorMap f ((Mod.free A).map g) ≫ (freeTensorIso N' Y).hom =
      (freeTensorIso N X).hom ≫ (f.hom ⊗ₘ g) := by
  apply tensor_hom_ext N ((Mod.free A).obj X)
  rw [← Category.assoc, tensorMap_projection, Category.assoc, freeTensorIso_projection]
  change (f.hom ⊗ₘ (A ◁ g)) ≫ monadicAction N' Y =
    projection N ((Mod.free A).obj X) ≫ ((freeTensorIso N X).hom ≫ (f.hom ⊗ₘ g))
  rw [← Category.assoc (projection N ((Mod.free A).obj X)) (freeTensorIso N X).hom
    (f.hom ⊗ₘ g), freeTensorIso_projection]
  change (f.hom ⊗ₘ (A ◁ g)) ≫ monadicAction N' Y =
    monadicAction N X ≫ (f.hom ⊗ₘ g)
  rw [tensorHom_def', tensorHom_def']
  rw [Category.assoc, monadicAction_map, ← Category.assoc,
    monadicAction_naturality, Category.assoc]

/-- The original free module functor followed by relative tensor is the actual base tensor. -/
def freeTensorNatIso (N : RightModuleFree.Carrier A) :
    Mod.free A ⋙ leftTensorFunctor N ≅ tensorLeft N.X :=
  NatIso.ofComponents (freeTensorIso N) (by
    intro X Y g
    change tensorMap (𝟙 N) ((Mod.free A).map g) ≫ (freeTensorIso N Y).hom =
      (freeTensorIso N X).hom ≫ (N.X ◁ g)
    simpa only [Mod.id_hom', tensorHom_def', id_whiskerRight, Category.comp_id] using
      freeTensorIso_naturality (𝟙 N) g)

theorem freeTensorIso_coefficient_naturality {N N' : RightModuleFree.Carrier A}
    (f : N ⟶ N') (X : C) :
    (rightTensorFunctor ((Mod.free A).obj X)).map f ≫ (freeTensorIso N' X).hom =
      (freeTensorIso N X).hom ≫ (f.hom ▷ X) := by
  change tensorMap f (𝟙 ((Mod.free A).obj X)) ≫ (freeTensorIso N' X).hom = _
  simpa only [CategoryTheory.Functor.map_id, tensorHom_def, whiskerLeft_id,
    Category.comp_id] using freeTensorIso_naturality f (𝟙 X)

/-- The whole original right coefficient Arrow becomes the original base tensor of that map. -/
def freeCoefficientArrowIso {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (X : C) :
    Arrow.mk ((rightTensorFunctor ((Mod.free A).obj X)).map f) ≅ Arrow.mk (f.hom ▷ X) :=
  Arrow.isoMk (freeTensorIso N X) (freeTensorIso N' X)
    (freeTensorIso_coefficient_naturality f X).symm

/-- The whole original free generator Arrow becomes the same scalar-free base tensor. -/
def freeGeneratorArrowIso (N : RightModuleFree.Carrier A) {X Y : C} (g : X ⟶ Y) :
    Arrow.mk ((leftTensorFunctor N).map ((Mod.free A).map g)) ≅ Arrow.mk (N.X ◁ g) :=
  Arrow.isoMk (freeTensorIso N X) (freeTensorIso N Y)
    ((freeTensorNatIso N).hom.naturality g).symm

/-- The actual free coefficient unit is the inverse reduction before its original quotient. -/
theorem freeTensorNatIso_inv_generator (N : RightModuleFree.Carrier A) (X : C) :
    (freeTensorNatIso N).inv.app X =
      (N.X ◁ ((Mod.freeForgetAdjunction A).unit.app X)) ≫ projection N ((Mod.free A).obj X) := by
  change (freeTensorIso N X).inv = _
  rw [freeTensorIso_inv, Mod.freeForgetAdjunction_unit_app]
  change (N.X ◁ ((λ_ X).inv ≫ (η[A] ▷ X))) ≫ projection N ((Mod.free A).obj X) =
    (N.X ◁ ((λ_ X).inv ≫ (η[A] ▷ X) ≫ 𝟙 (A ⊗ X))) ≫ projection N ((Mod.free A).obj X)
  rw [Category.comp_id]

end CategoryTheory.Mod.RightLeftTensor
