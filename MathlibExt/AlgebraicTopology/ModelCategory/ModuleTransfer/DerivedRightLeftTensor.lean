/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.RightLeftTensorBrown
public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.ScalarChange
public import Mathlib.CategoryTheory.Localization.Bifunctor

/-!
# The actual derived right-left module tensor and Hom

The right and left module replacements are constructed from their original
full transfers at the respective returned source ranks. The base replacement
is constructed from the original base generation. Localization uses the
unchanged balanced tensor, module Hom action, coefficient maps and target
maps. The three homotopy categories retain their distinct actual carriers.
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
  (dC : CofibrantGenerationData C κC)

open CategoryTheory.Mod.RightLeftTensor

/-- The actual right module rank and original I/J generation construct both replacement factories. -/
def rightReplacements :
    letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
    GeneratedFunctorialReplacements.Data (C := RightModuleFree.Carrier A) := by
  letI : ModelCategory (RightModuleFree.Carrier A) := tR.model
  letI : Fact tR.generationCardinal.cardinal.IsRegular := tR.generationCardinal.regular
  letI : OrderBot tR.generationCardinal.cardinal.ord.ToType := tR.generationCardinal.orderBot
  exact GeneratedFunctorialReplacements.fromGeneration tR.generation

local notation "qR" => rightReplacements tR
local notation "qL" => ScalarChange.replacementsOfTransfer tL
local notation "rC" => GeneratedFunctorialReplacements.fromGeneration dC
local notation "CR" => RightModuleFree.Carrier A
local notation "CL" => Mod C A
/-- Weak equivalences in the right-module model returned by its original source-bound transfer. -/
abbrev rightWeak : MorphismProperty CR :=
  letI : ModelCategory CR := tR.model
  weakEquivalences CR

/-- Weak equivalences in the left-module model returned by its original source-bound transfer. -/
abbrev leftWeak : MorphismProperty CL :=
  letI : ModelCategory CL := tL.model
  weakEquivalences CL

local notation "WR" => rightWeak tR
local notation "WL" => leftWeak tL
local notation "HR" => MorphismProperty.Localization WR
local notation "HL" => MorphismProperty.Localization WL
local notation "HC" => MorphismProperty.Localization (weakEquivalences C)
local notation "πR" => MorphismProperty.Q WR
local notation "πL" => MorphismProperty.Q WL
local notation "πC" => MorphismProperty.Q (weakEquivalences C)

/-- The original balanced tensor is evaluated at both independently constructed module replacements. -/
def replacedTensor : CR ⥤ CL ⥤ C := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact (qR).Q ⋙ tensorCurried (A := A) ⋙ (whiskeringLeft CL CL C).obj (qL).Q

/-- The raw derived tensor keeps the canonical projection of the same balanced quotient. -/
def rawTensor : CR ⥤ CL ⥤ HC :=
  replacedTensor tR tL ⋙ (whiskeringRight CL C HC).obj πC

/-- Both actual replacement maps and both original tensor-variable maps invert source weak arrows. -/
theorem rawTensor_inverts (hIR : IR.rlp = trivialFibrations C) :
    MorphismProperty.IsInvertedBy₂ WR WL (rawTensor tR tL) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  rintro ⟨N, M⟩ ⟨N', M'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have h₁ := RightLeftTensorBrown.rightTensor_weak_of_cofibrant tR tL hIR ((qL).Q.obj M) ((qR).Q.map f)
    ((qL).q_cofibrant M) ((qR).q_cofibrant N) ((qR).q_cofibrant N') ((qR).q_map_weak f hf)
  have h₂ := RightLeftTensorBrown.leftTensor_weak_of_cofibrant tR tL hIR ((qR).Q.obj N') ((qL).Q.map g)
    ((qR).q_cofibrant N') ((qL).q_cofibrant M) ((qL).q_cofibrant M') ((qL).q_map_weak g hg)
  change IsIso ((πC).map (tensorMap ((qR).Q.map f) (𝟙 ((qL).Q.obj M))) ≫
    (πC).map (tensorMap (𝟙 ((qR).Q.obj N')) ((qL).Q.map g)))
  rw [← (πC).map_comp]
  exact Localization.inverts πC (weakEquivalences C) _ ((weakEquivalences C).comp_mem _ _ h₁ h₂)

/-- The full derived tensor is a bifunctor on the actual localized right and left module categories. -/
def tensor (hIR : IR.rlp = trivialFibrations C) : HR ⥤ HL ⥤ HC :=
by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact Localization.lift₂ (rawTensor tR tL) (rawTensor_inverts tR tL hIR) πR πL

instance tensorLifting (hIR : IR.rlp = trivialFibrations C) :
    Localization.Lifting₂ πR πL WR WL
      (rawTensor tR tL) (tensor tR tL hIR) :=
by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  unfold tensor
  infer_instance

/-- The entire original two-variable source calculation is a natural projection isomorphism. -/
def tensorProjectionIso (hIR : IR.rlp = trivialFibrations C) :
    (((whiskeringLeft₂ HC).obj πR).obj πL).obj (tensor tR tL hIR) ≅ rawTensor tR tL :=
  Localization.Lifting₂.iso πR πL WR WL
    (rawTensor tR tL) (tensor tR tL hIR)

/-- Each original pair computes the original balanced tensor of the two chosen Q objects. -/
def tensorComparison (hIR : IR.rlp = trivialFibrations C) (N : CR) (M : CL) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    ((tensor tR tL hIR).obj ((πR).obj N)).obj ((πL).obj M) ≅
      (πC).obj (tensorObject ((qR).Q.obj N) ((qL).Q.obj M)) :=
by
  letI : ModelCategory CR := tR.model
  letI : ModelCategory CL := tL.model
  exact ((evaluation CL HC).obj M).mapIso ((tensorProjectionIso tR tL hIR).app N)

/-- The same original right replacement and original base R act on the actual module Hom functor. -/
def replacedHom : CRᵒᵖ ⥤ C ⥤ CL := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact (qR).Q.op ⋙ homContravariant (A := A) ⋙ (whiskeringLeft C C CL).obj (rC).R

/-- The raw derived Hom retains the same original left-module action and canonical module projection. -/
def rawHom : CRᵒᵖ ⥤ C ⥤ HL :=
  replacedHom tR tL dC ⋙ (whiskeringRight C CL HL).obj πL

/-- Actual cofibrant source pre-maps and fibrant target maps invert both original Hom-variable weak arrows. -/
theorem rawHom_inverts (hIR : IR.rlp = trivialFibrations C) :
    MorphismProperty.IsInvertedBy₂ (WR).op (weakEquivalences C) (rawHom tR tL dC) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  rintro ⟨N, X⟩ ⟨N', X'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have h₁ := RightLeftTensorBrown.homPre_weak_of_cofibrant tR tL hIR ((qR).Q.map f.unop) ((rC).R.obj X)
    ((qR).q_cofibrant N'.unop) ((qR).q_cofibrant N.unop) ((rC).r_fibrant X) ((qR).q_map_weak f.unop hf)
  have h₂ := RightLeftTensorBrown.homFunctor_weak_of_fibrant tR tL hIR ((qR).Q.obj N'.unop) ((rC).R.map g)
    ((qR).q_cofibrant N'.unop) ((rC).r_fibrant X) ((rC).r_fibrant X') ((rC).r_map_weak g hg)
  change IsIso ((πL).map (homPre ((qR).Q.map f.unop) ((rC).R.obj X)) ≫
    (πL).map ((homFunctor ((qR).Q.obj N'.unop)).map ((rC).R.map g)))
  rw [← (πL).map_comp]
  exact Localization.inverts πL WL _ ((weakEquivalences CL).comp_mem _ _ h₁ h₂)

/-- The actual derived Hom lands in the actual localized left-module category. -/
def hom (hIR : IR.rlp = trivialFibrations C) : HRᵒᵖ ⥤ HC ⥤ HL :=
by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact Localization.lift₂ (rawHom tR tL dC) (rawHom_inverts tR tL dC hIR) (πR).op πC

instance homLifting (hIR : IR.rlp = trivialFibrations C) :
    Localization.Lifting₂ (πR).op πC (WR).op (weakEquivalences C)
      (rawHom tR tL dC) (hom tR tL dC hIR) :=
by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  unfold hom
  infer_instance

/-- All original coefficient and target maps retain the complete raw Hom calculation. -/
def homProjectionIso (hIR : IR.rlp = trivialFibrations C) :
    (((whiskeringLeft₂ HL).obj (πR).op).obj πC).obj (hom tR tL dC hIR) ≅ rawHom tR tL dC :=
  Localization.Lifting₂.iso (πR).op πC (WR).op (weakEquivalences C)
    (rawHom tR tL dC) (hom tR tL dC hIR)

/-- Every original right-module/base pair keeps the exact chosen-Q/chosen-R module Hom object. -/
def homComparison (hIR : IR.rlp = trivialFibrations C) (N : CR) (X : C) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    ((hom tR tL dC hIR).obj (op ((πR).obj N))).obj ((πC).obj X) ≅
      (πL).obj (homObject ((qR).Q.obj N) ((rC).R.obj X)) :=
by
  letI : ModelCategory CR := tR.model
  letI : ModelCategory CL := tL.model
  exact ((evaluation C HL).obj X).mapIso ((homProjectionIso tR tL dC hIR).app (op N))

/-- Every original right-module map retains the complete chosen tensor comparison square. -/
theorem tensorComparison_naturality_left (hIR : IR.rlp = trivialFibrations C)
    {N N' : CR} (f : N ⟶ N') (M : CL) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    ((tensor tR tL hIR).map ((πR).map f)).app ((πL).obj M) ≫
        (tensorComparison tR tL hIR N' M).hom =
      (tensorComparison tR tL hIR N M).hom ≫
        (πC).map (tensorMap ((qR).Q.map f) (𝟙 ((qL).Q.obj M))) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact congrArg (fun a => a.app M) ((tensorProjectionIso tR tL hIR).hom.naturality f)

/-- Every original left-module map retains the same actual tensor comparison. -/
theorem tensorComparison_naturality_right (hIR : IR.rlp = trivialFibrations C)
    (N : CR) {M M' : CL} (g : M ⟶ M') :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    ((tensor tR tL hIR).obj ((πR).obj N)).map ((πL).map g) ≫
        (tensorComparison tR tL hIR N M').hom =
      (tensorComparison tR tL hIR N M).hom ≫
        (πC).map (tensorMap (𝟙 ((qR).Q.obj N)) ((qL).Q.map g)) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact ((tensorProjectionIso tR tL hIR).hom.app N).naturality g

/-- The inverse tensor source comparison retains the same original right Q map. -/
theorem tensorComparison_inv_naturality_left (hIR : IR.rlp = trivialFibrations C)
    {N N' : CR} (f : N ⟶ N') (M : CL) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    (πC).map (tensorMap ((qR).Q.map f) (𝟙 ((qL).Q.obj M))) ≫
        (tensorComparison tR tL hIR N' M).inv =
      (tensorComparison tR tL hIR N M).inv ≫
        ((tensor tR tL hIR).map ((πR).map f)).app ((πL).obj M) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact congrArg (fun a => a.app M) ((tensorProjectionIso tR tL hIR).inv.naturality f)

/-- The inverse tensor target comparison retains the original left Q map. -/
theorem tensorComparison_inv_naturality_right (hIR : IR.rlp = trivialFibrations C)
    (N : CR) {M M' : CL} (g : M ⟶ M') :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    (πC).map (tensorMap (𝟙 ((qR).Q.obj N)) ((qL).Q.map g)) ≫
        (tensorComparison tR tL hIR N M').inv =
      (tensorComparison tR tL hIR N M).inv ≫
        ((tensor tR tL hIR).obj ((πR).obj N)).map ((πL).map g) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact ((tensorProjectionIso tR tL hIR).inv.app N).naturality g

/-- The actual Hom target comparison retains every original base R map. -/
theorem homComparison_inv_naturality_target (hIR : IR.rlp = trivialFibrations C)
    (N : CR) {X X' : C} (g : X ⟶ X') :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    (πL).map ((homFunctor ((qR).Q.obj N)).map ((rC).R.map g)) ≫
        (homComparison tR tL dC hIR N X').inv =
      (homComparison tR tL dC hIR N X).inv ≫
        ((hom tR tL dC hIR).obj (op ((πR).obj N))).map ((πC).map g) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact ((homProjectionIso tR tL dC hIR).inv.app (op N)).naturality g

/-- The full contravariant Hom comparison retains every original right-module Q pre-map. -/
theorem homComparison_inv_naturality_parameter (hIR : IR.rlp = trivialFibrations C)
    {N N' : CR} (f : N ⟶ N') (X : C) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    (πL).map (homPre ((qR).Q.map f) ((rC).R.obj X)) ≫
        (homComparison tR tL dC hIR N X).inv =
      (homComparison tR tL dC hIR N' X).inv ≫
        ((hom tR tL dC hIR).map ((πR).map f).op).app ((πC).obj X) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  exact congrArg (fun a => a.app X) ((homProjectionIso tR tL dC hIR).inv.naturality f.op)

end HomotopicalAlgebra.ModuleTransfer.DerivedRightLeftTensor
