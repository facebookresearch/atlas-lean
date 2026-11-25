/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorAdjunctionSource
public import MathlibExt.CategoryTheory.Localization.ParametrizedHomExtension

/-!
# The complete chosen derived tensor–internal-Hom adjunction

The original Q/R Hom bijections and all three original-variable naturalities
construct the full parametrized adjunction through the reusable heterogeneous
localization extension. The same actual maps supply all units, counits and
triangles on the whole canonical homotopy category.

Source: Hovey, *Model Categories*, Proposition 4.3.1.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MorphismProperty Functor Opposite
open scoped MonoidalCategory MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorAdjunction
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
local notation "Ho" => MorphismProperty.Localization (weakEquivalences C)
local notation "π" => MorphismProperty.Q (weakEquivalences C)
open DerivedTensorConstructions DerivedTensorAdjunctionSource

/-- Every original homotopy object has the actual Q/R tensor-Hom bijection. -/
def homEquiv (d : GeneratedFunctorialReplacements.Data (C := C)) (A B Z : Ho) :
    (((tensor d).obj A).obj B ⟶ Z) ≃ (B ⟶ ((derivedInternalHom d).obj (op A)).obj Z) :=
  Localization.ParametrizedHomExtension.homEquiv
    (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (tensor d) (derivedInternalHom d) (representedHomEquiv d) A B Z

/-- This full function retains the exact original represented Q/R Hom function. -/
theorem homEquiv_source (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C) :
    homEquiv d ((π).obj X) ((π).obj Y) ((π).obj Z) = representedHomEquiv d X Y Z := rfl

/-- The actual full Hom function is natural in every homotopy-category second-variable arrow. -/
theorem homEquiv_naturality_source (d : GeneratedFunctorialReplacements.Data (C := C))
    (A : Ho) {B B' : Ho} (f : B ⟶ B') (Z : Ho) (g : ((tensor d).obj A).obj B' ⟶ Z) :
    homEquiv d A B Z (((tensor d).obj A).map f ≫ g) = f ≫ homEquiv d A B' Z g :=
  Localization.ParametrizedHomExtension.homEquiv_naturality_source
    (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (tensor d) (derivedInternalHom d) (representedHomEquiv d) (representedHomEquiv_source d) A f Z g

/-- The same full Hom function is natural in every homotopy-category target arrow. -/
theorem homEquiv_naturality_target (d : GeneratedFunctorialReplacements.Data (C := C))
    (A B : Ho) {Z Z' : Ho} (f : Z ⟶ Z') (g : ((tensor d).obj A).obj B ⟶ Z) :
    homEquiv d A B Z' (g ≫ f) = homEquiv d A B Z g ≫ ((derivedInternalHom d).obj (op A)).map f :=
  Localization.ParametrizedHomExtension.homEquiv_naturality_target
    (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (tensor d) (derivedInternalHom d) (representedHomEquiv d) (representedHomEquiv_target d) A B f g

/-- Parameter naturality holds for every homotopy-category tensor-parameter arrow. -/
theorem homEquiv_naturality_parameter (d : GeneratedFunctorialReplacements.Data (C := C))
    {A A' : Ho} (f : A ⟶ A') (B Z : Ho) (g : ((tensor d).obj A').obj B ⟶ Z) :
    homEquiv d A B Z (((tensor d).map f).app B ≫ g) =
      homEquiv d A' B Z g ≫ ((derivedInternalHom d).map f.op).app Z :=
  Localization.ParametrizedHomExtension.homEquiv_naturality_parameter
    (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (tensor d) (derivedInternalHom d) (representedHomEquiv d) (representedHomEquiv_parameter d) f B
        Z g

/-- Each actual derived tensor parameter has the full constructed tensor–Hom adjunction. -/
def adjunction (d : GeneratedFunctorialReplacements.Data (C := C)) (A : Ho) :
    (tensor d).obj A ⊣ (derivedInternalHom d).obj (op A) :=
  Localization.ParametrizedHomExtension.adjunction
    (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (tensor d) (derivedInternalHom d) (representedHomEquiv d)
    (representedHomEquiv_source d) (representedHomEquiv_target d) A

/-- The actual adjunction has the same complete original Q/R Hom function. -/
theorem adjunction_homEquiv (d : GeneratedFunctorialReplacements.Data (C := C)) (A B Z : Ho)
    (f : ((tensor d).obj A).obj B ⟶ Z) :
    (adjunction d A).homEquiv B Z f = homEquiv d A B Z f :=
  Localization.ParametrizedHomExtension.adjunction_homEquiv
    (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (tensor d) (derivedInternalHom d) (representedHomEquiv d)
    (representedHomEquiv_source d) (representedHomEquiv_target d) A B Z f

/-- The complete two-variable derived tensor–internal-Hom adjunction. -/
def parametrizedAdjunction (d : GeneratedFunctorialReplacements.Data (C := C)) :
    tensor d ⊣₂ derivedInternalHom d :=
  Localization.ParametrizedHomExtension.parametrizedAdjunction
    (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (tensor d) (derivedInternalHom d) (representedHomEquiv d)
    (representedHomEquiv_source d) (representedHomEquiv_target d) (representedHomEquiv_parameter d)

/-- Every original represented triple keeps the original constructed Q/R bijection. -/
theorem parametrizedAdjunction_homEquiv_source (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) (f : ((tensor d).obj ((π).obj X)).obj ((π).obj Y) ⟶ (π).obj Z) :
    (parametrizedAdjunction d).homEquiv f = representedHomEquiv d X Y Z f :=
  Localization.ParametrizedHomExtension.parametrizedAdjunction_source
    (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (tensor d) (derivedInternalHom d) (representedHomEquiv d)
    (representedHomEquiv_source d) (representedHomEquiv_target d) (representedHomEquiv_parameter d)
        X Y Z f

/-- Every actual derived tensor parameter keeps the complete unit/counit left triangle. -/
theorem left_triangle (d : GeneratedFunctorialReplacements.Data (C := C)) (A B : Ho) :
    ((tensor d).obj A).map ((adjunction d A).unit.app B) ≫
      (adjunction d A).counit.app (((tensor d).obj A).obj B) = 𝟙 _ :=
  (adjunction d A).left_triangle_components B

/-- Every actual derived internal-Hom parameter keeps the full right triangle. -/
theorem right_triangle (d : GeneratedFunctorialReplacements.Data (C := C)) (A Z : Ho) :
    (adjunction d A).unit.app (((derivedInternalHom d).obj (op A)).obj Z) ≫
      ((derivedInternalHom d).obj (op A)).map ((adjunction d A).counit.app Z) = 𝟙 _ :=
  (adjunction d A).right_triangle_components Z
end HomotopicalAlgebra.DerivedTensorAdjunction
