/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.DerivedRightLeftTensorAdjunctionSource
public import MathlibExt.CategoryTheory.Localization.ParametrizedHomExtension

/-!
# The complete actual derived relative tensor-Hom adjunction

The original represented Hom functions and their three proved naturalities
extend to the actual three localized categories. All units, counits and
triangles belong to the original balanced tensor and module Hom functors,
derived with their independently generated replacement ranks. The right,
left and base carriers are retained without an identification of modules
in a homotopy category with the homotopy category of modules.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v wR wL wC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty CategoryTheory.SmallObject HomotopicalAlgebra
open CategoryTheory.MonoidalOpposite Opposite Functor
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.DerivedRightLeftTensor

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [ModelCategory C] [IsClosedSymmetricMonoidalModelCategory C]
  {A : C} [MonObj A] [HasColimitsOfSize.{0, 0} C] [IsCofibrant A]
  [HasColimitsOfSize.{wR, wR} C]
  {IR JR IL JL : MorphismProperty C}
  {sIR : UniformRelativeSourceSmallness.{wR} (IR.strictMap (RightModuleFree.functor A))}
  {sJR : UniformRelativeSourceSmallness.{wR} (JR.strictMap (RightModuleFree.functor A))}
  {sIL : UniformRelativeSourceSmallness.{wL} (IL.strictMap (Mod.free A))}
  {sJL : UniformRelativeSourceSmallness.{wL} (JL.strictMap (Mod.free A))}
  (tR : RightTransfer.FullModelTransfer (RightModuleFree.functor A)
    (Mod.forget (D := C) (mop A)) IR JR sIR sJR)
  (tL : RightTransfer.FullModelTransfer (Mod.free A) (Mod.forget (D := C) A) IL JL sIL sJL)
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  (dC : CofibrantGenerationData C κC) (hIR : IR.rlp = trivialFibrations C)

local notation "CR" => RightModuleFree.Carrier A
local notation "CL" => Mod C A
local notation "WR" => rightWeak tR
local notation "WL" => leftWeak tL
local notation "WC" => weakEquivalences C
local notation "HR" => MorphismProperty.Localization WR
local notation "HL" => MorphismProperty.Localization WL
local notation "HC" => MorphismProperty.Localization WC
local notation "πR" => MorphismProperty.Q WR
local notation "πL" => MorphismProperty.Q WL
local notation "πC" => MorphismProperty.Q WC

/-- Every actual homotopy object has the original derived relative tensor-Hom bijection. -/
def homEquiv (N : HR) (M : HL) (X : HC) :
    (((tensor tR tL hIR).obj N).obj M ⟶ X) ≃
      (M ⟶ ((hom tR tL dC hIR).obj (op N)).obj X) := by
  letI : ModelCategory CR := tR.model
  letI : ModelCategory CL := tL.model
  exact Localization.ParametrizedHomExtension.homEquiv WR WL WC
    (tensor tR tL hIR) (hom tR tL dC hIR) (representedHomEquiv tR tL dC hIR) N M X

/-- The full Hom function preserves the exact original represented Q/R function. -/
theorem homEquiv_source (N : CR) (M : CL) (X : C) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    homEquiv tR tL dC hIR ((πR).obj N) ((πL).obj M) ((πC).obj X) =
      representedHomEquiv tR tL dC hIR N M X := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  rfl

/-- Source naturality holds for every arrow of the actual left-module homotopy category. -/
theorem homEquiv_naturality_source (N : HR) {M M' : HL} (g : M ⟶ M') (X : HC)
    (f : ((tensor tR tL hIR).obj N).obj M' ⟶ X) :
    homEquiv tR tL dC hIR N M X (((tensor tR tL hIR).obj N).map g ≫ f) =
      g ≫ homEquiv tR tL dC hIR N M' X f := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact Localization.ParametrizedHomExtension.homEquiv_naturality_source WR WL WC
    (tensor tR tL hIR) (hom tR tL dC hIR) (representedHomEquiv tR tL dC hIR)
    (representedHomEquiv_source tR tL dC hIR) N g X f

/-- Target naturality holds for every arrow of the actual base homotopy category. -/
theorem homEquiv_naturality_target (N : HR) (M : HL) {X X' : HC} (g : X ⟶ X')
    (f : ((tensor tR tL hIR).obj N).obj M ⟶ X) :
    homEquiv tR tL dC hIR N M X' (f ≫ g) =
      homEquiv tR tL dC hIR N M X f ≫ ((hom tR tL dC hIR).obj (op N)).map g := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact Localization.ParametrizedHomExtension.homEquiv_naturality_target WR WL WC
    (tensor tR tL hIR) (hom tR tL dC hIR) (representedHomEquiv tR tL dC hIR)
    (representedHomEquiv_target tR tL dC hIR) N M g f

/-- Parameter naturality holds for every arrow of the actual right-module homotopy category. -/
theorem homEquiv_naturality_parameter {N N' : HR} (g : N ⟶ N') (M : HL) (X : HC)
    (f : ((tensor tR tL hIR).obj N').obj M ⟶ X) :
    homEquiv tR tL dC hIR N M X (((tensor tR tL hIR).map g).app M ≫ f) =
      homEquiv tR tL dC hIR N' M X f ≫ ((hom tR tL dC hIR).map g.op).app X := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact Localization.ParametrizedHomExtension.homEquiv_naturality_parameter WR WL WC
    (tensor tR tL hIR) (hom tR tL dC hIR) (representedHomEquiv tR tL dC hIR)
    (representedHomEquiv_parameter tR tL dC hIR) g M X f

/-- Every actual localized right module has the full constructed relative tensor-Hom adjunction. -/
def adjunction (N : HR) : (tensor tR tL hIR).obj N ⊣ (hom tR tL dC hIR).obj (op N) := by
  letI : ModelCategory CR := tR.model
  letI : ModelCategory CL := tL.model
  exact Localization.ParametrizedHomExtension.adjunction WR WL WC
    (tensor tR tL hIR) (hom tR tL dC hIR) (representedHomEquiv tR tL dC hIR)
    (representedHomEquiv_source tR tL dC hIR) (representedHomEquiv_target tR tL dC hIR) N

/-- The complete parametrized adjunction is built from the actual three original naturality functions. -/
def parametrizedAdjunction : tensor tR tL hIR ⊣₂ hom tR tL dC hIR := by
  letI : ModelCategory CR := tR.model
  letI : ModelCategory CL := tL.model
  exact Localization.ParametrizedHomExtension.parametrizedAdjunction WR WL WC
    (tensor tR tL hIR) (hom tR tL dC hIR) (representedHomEquiv tR tL dC hIR)
    (representedHomEquiv_source tR tL dC hIR) (representedHomEquiv_target tR tL dC hIR)
    (representedHomEquiv_parameter tR tL dC hIR)

/-- All represented module/base objects retain their original Q/R Hom function. -/
theorem parametrizedAdjunction_source (N : CR) (M : CL) (X : C)
    (f : ((tensor tR tL hIR).obj ((πR).obj N)).obj ((πL).obj M) ⟶ (πC).obj X) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    (parametrizedAdjunction tR tL dC hIR).homEquiv f = representedHomEquiv tR tL dC hIR N M X f := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact Localization.ParametrizedHomExtension.parametrizedAdjunction_source WR WL WC
    (tensor tR tL hIR) (hom tR tL dC hIR) (representedHomEquiv tR tL dC hIR)
    (representedHomEquiv_source tR tL dC hIR) (representedHomEquiv_target tR tL dC hIR)
    (representedHomEquiv_parameter tR tL dC hIR) N M X f

/-- The left triangle holds at every actual localized left module. -/
theorem left_triangle (N : HR) (M : HL) :
    ((tensor tR tL hIR).obj N).map ((adjunction tR tL dC hIR N).unit.app M) ≫
      (adjunction tR tL dC hIR N).counit.app (((tensor tR tL hIR).obj N).obj M) = 𝟙 _ :=
  (adjunction tR tL dC hIR N).left_triangle_components M

/-- The right triangle holds at every actual localized base object. -/
theorem right_triangle (N : HR) (X : HC) :
    (adjunction tR tL dC hIR N).unit.app (((hom tR tL dC hIR).obj (op N)).obj X) ≫
      ((hom tR tL dC hIR).obj (op N)).map ((adjunction tR tL dC hIR N).counit.app X) = 𝟙 _ :=
  (adjunction tR tL dC hIR N).right_triangle_components X

end HomotopicalAlgebra.ModuleTransfer.DerivedRightLeftTensor
