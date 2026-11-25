/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.DerivedRightLeftTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorCoherence
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom

/-!
# Original represented Hom functions for the relative derived tensor

The actual tensor-Hom adjunction gives the Hom bijection on the original
cofibrant module replacements and fibrant base replacement. The original
module Q counit, base R unit and complete tensor/Hom projection comparisons
give the represented derived Hom function. Source, target and coefficient
naturality are proved on those actual maps.
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

local notation "qR" => rightReplacements tR
local notation "qL" => ScalarChange.replacementsOfTransfer tL
local notation "rC" => GeneratedFunctorialReplacements.fromGeneration dC
local notation "CR" => RightModuleFree.Carrier A
local notation "CL" => Mod C A
local notation "HR" => MorphismProperty.Localization (rightWeak tR)
local notation "HL" => MorphismProperty.Localization (leftWeak tL)
local notation "HC" => MorphismProperty.Localization (weakEquivalences C)
local notation "πR" => MorphismProperty.Q (rightWeak tR)
local notation "πL" => MorphismProperty.Q (leftWeak tL)
local notation "πC" => MorphismProperty.Q (weakEquivalences C)

/-- The actual full left-module Q counit is an isomorphism after its original projection. -/
def leftQProjectionIso :
    letI : ModelCategory CL := tL.model
    (qL).Q ⋙ πL ≅ πL := by
  letI : ModelCategory CL := tL.model
  letI : IsIso (whiskerRight (qL).q πL) := DerivedFunctorCoherence.qLocalized_isIso (qL)
  exact asIso (whiskerRight (qL).q πL) ≪≫ (πL).leftUnitor

/-- The actual base R unit gives its complete original projection isomorphism. -/
def baseRProjectionIso : πC ≅ (rC).R ⋙ πC := by
  letI : IsIso (whiskerRight (rC).r πC) := DerivedFunctorCoherence.rLocalized_isIso (rC)
  exact (πC).leftUnitor.symm ≪≫ asIso (whiskerRight (rC).r πC)

/-- The original tensor-Hom adjunction is evaluated on the exact module Q objects and base R object. -/
def originalHomEquiv (hIR : IR.rlp = trivialFibrations C) (N : CR) (M : CL) (X : C) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    ((πC).obj (tensorObject ((qR).Q.obj N) ((qL).Q.obj M)) ⟶ (πC).obj ((rC).R.obj X)) ≃
      ((πL).obj ((qL).Q.obj M) ⟶ (πL).obj (homObject ((qR).Q.obj N) ((rC).R.obj X))) := by
  letI : ModelCategory CR := tR.model
  letI : ModelCategory CL := tL.model
  letI : IsCofibrant ((qL).Q.obj M) := (qL).q_cofibrant M
  letI : IsFibrant ((rC).R.obj X) := (rC).r_fibrant X
  letI : (tensorHomAdjunction ((qR).Q.obj N)).IsQuillenAdjunction :=
    RightLeftTensorQuillen.tensorHom_isQuillen_of_transfers tR tL hIR ((qR).Q.obj N) ((qR).q_cofibrant N)
  exact QuillenOrdinaryHoHom.homEquiv (tensorHomAdjunction ((qR).Q.obj N)) ((qL).Q.obj M) ((rC).R.obj X)

/-- All original represented objects retain the actual two-replacement tensor-Hom bijection. -/
def representedHomEquiv (hIR : IR.rlp = trivialFibrations C) (N : CR) (M : CL) (X : C) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    (((tensor tR tL hIR).obj ((πR).obj N)).obj ((πL).obj M) ⟶ (πC).obj X) ≃
      ((πL).obj M ⟶ ((hom tR tL dC hIR).obj (op ((πR).obj N))).obj ((πC).obj X)) := by
  letI : ModelCategory CR := tR.model
  letI : ModelCategory CL := tL.model
  exact ((Iso.homCongr (tensorComparison tR tL hIR N M) ((baseRProjectionIso dC).app X)).trans
    (originalHomEquiv tR tL dC hIR N M X)).trans
      (Iso.homCongr ((leftQProjectionIso tL).app M) (homComparison tR tL dC hIR N X).symm)

/-- The complete forward Hom function retains both original Q/R arrows and the original adjunct. -/
theorem representedHomEquiv_apply (hIR : IR.rlp = trivialFibrations C) (N : CR) (M : CL) (X : C)
    (f : ((tensor tR tL hIR).obj ((πR).obj N)).obj ((πL).obj M) ⟶ (πC).obj X) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    representedHomEquiv tR tL dC hIR N M X f =
      (leftQProjectionIso tL).inv.app M ≫
        originalHomEquiv tR tL dC hIR N M X
          ((tensorComparison tR tL hIR N M).inv ≫ f ≫ (baseRProjectionIso dC).hom.app X) ≫
        (homComparison tR tL dC hIR N X).inv := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  rfl

/-- The original ordinary-Ho function keeps every original left-module Q map. -/
theorem originalHomEquiv_source (hIR : IR.rlp = trivialFibrations C) (N : CR)
    {M M' : CL} (g : M ⟶ M') (X : C) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    ∀ f : (πC).obj (tensorObject ((qR).Q.obj N) ((qL).Q.obj M')) ⟶ (πC).obj ((rC).R.obj X),
    originalHomEquiv tR tL dC hIR N M X
        ((πC).map (tensorMap (𝟙 ((qR).Q.obj N)) ((qL).Q.map g)) ≫ f) =
      (πL).map ((qL).Q.map g) ≫ originalHomEquiv tR tL dC hIR N M' X f := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  let : IsCofibrant ((qL).Q.obj M) := (qL).q_cofibrant M
  let : IsCofibrant ((qL).Q.obj M') := (qL).q_cofibrant M'
  let : IsFibrant ((rC).R.obj X) := (rC).r_fibrant X
  let : (tensorHomAdjunction ((qR).Q.obj N)).IsQuillenAdjunction :=
    RightLeftTensorQuillen.tensorHom_isQuillen_of_transfers tR tL hIR ((qR).Q.obj N) ((qR).q_cofibrant N)
  intro f
  exact QuillenOrdinaryHoHom.homEquiv_naturality_left (tensorHomAdjunction ((qR).Q.obj N))
    ((rC).R.obj X) ((qL).Q.map g) f

/-- The original ordinary-Ho function keeps every original base R target map. -/
theorem originalHomEquiv_target (hIR : IR.rlp = trivialFibrations C) (N : CR) (M : CL)
    {X X' : C} (g : X ⟶ X') :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    ∀ f : (πC).obj (tensorObject ((qR).Q.obj N) ((qL).Q.obj M)) ⟶ (πC).obj ((rC).R.obj X),
    originalHomEquiv tR tL dC hIR N M X' (f ≫ (πC).map ((rC).R.map g)) =
      originalHomEquiv tR tL dC hIR N M X f ≫
        (πL).map ((homFunctor ((qR).Q.obj N)).map ((rC).R.map g)) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  let : IsCofibrant ((qL).Q.obj M) := (qL).q_cofibrant M
  let : IsFibrant ((rC).R.obj X) := (rC).r_fibrant X
  let : IsFibrant ((rC).R.obj X') := (rC).r_fibrant X'
  let : (tensorHomAdjunction ((qR).Q.obj N)).IsQuillenAdjunction :=
    RightLeftTensorQuillen.tensorHom_isQuillen_of_transfers tR tL hIR ((qR).Q.obj N) ((qR).q_cofibrant N)
  intro f
  exact QuillenOrdinaryHoHom.homEquiv_naturality_right (tensorHomAdjunction ((qR).Q.obj N))
    ((qL).Q.obj M) f ((rC).R.map g)

/-- The ordinary-Ho parameter function is the original coefficient mate on every actual Q map. -/
theorem originalHomEquiv_parameter (hIR : IR.rlp = trivialFibrations C)
    {N N' : CR} (g : N ⟶ N') (M : CL) (X : C) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    ∀ f : (πC).obj (tensorObject ((qR).Q.obj N') ((qL).Q.obj M)) ⟶ (πC).obj ((rC).R.obj X),
    originalHomEquiv tR tL dC hIR N M X
        ((πC).map (tensorMap ((qR).Q.map g) (𝟙 ((qL).Q.obj M))) ≫ f) =
      originalHomEquiv tR tL dC hIR N' M X f ≫
        (πL).map (homPre ((qR).Q.map g) ((rC).R.obj X)) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  let : IsCofibrant ((qL).Q.obj M) := (qL).q_cofibrant M
  let : IsFibrant ((rC).R.obj X) := (rC).r_fibrant X
  let : (tensorHomAdjunction ((qR).Q.obj N)).IsQuillenAdjunction :=
    RightLeftTensorQuillen.tensorHom_isQuillen_of_transfers tR tL hIR ((qR).Q.obj N) ((qR).q_cofibrant N)
  let : (tensorHomAdjunction ((qR).Q.obj N')).IsQuillenAdjunction :=
    RightLeftTensorQuillen.tensorHom_isQuillen_of_transfers tR tL hIR ((qR).Q.obj N') ((qR).q_cofibrant N')
  let : IsCofibrant (tensorObject ((qR).Q.obj N') ((qL).Q.obj M)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := tensorHomAdjunction ((qR).Q.obj N')) (inferInstance : IsCofibrant ((qL).Q.obj M))
  intro f
  obtain ⟨h, hh⟩ := map_surjective_of_isLocalization πC
    (tensorObject ((qR).Q.obj N') ((qL).Q.obj M)) ((rC).R.obj X) f
  rw [← hh, ← (πC).map_comp]
  change QuillenOrdinaryHoHom.homEquiv (tensorHomAdjunction ((qR).Q.obj N)) _ _
      ((πC).map (tensorMap ((qR).Q.map g) (𝟙 ((qL).Q.obj M)) ≫ h)) =
    QuillenOrdinaryHoHom.homEquiv (tensorHomAdjunction ((qR).Q.obj N')) _ _ ((πC).map h) ≫ _
  rw [QuillenOrdinaryHoHom.homEquiv_map, QuillenOrdinaryHoHom.homEquiv_map, ← (πL).map_comp]
  exact (πL).congr_map (tensorHomParametrized.homEquiv_naturality_one ((qR).Q.map g) h)

/-- The complete represented Hom function retains every original left-module arrow. -/
theorem representedHomEquiv_source (hIR : IR.rlp = trivialFibrations C) (N : CR)
    {M M' : CL} (g : M ⟶ M') (X : C)
    (f : ((tensor tR tL hIR).obj ((πR).obj N)).obj ((πL).obj M') ⟶ (πC).obj X) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    representedHomEquiv tR tL dC hIR N M X
        (((tensor tR tL hIR).obj ((πR).obj N)).map ((πL).map g) ≫ f) =
      (πL).map g ≫ representedHomEquiv tR tL dC hIR N M' X f := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  have hArg : (tensorComparison tR tL hIR N M).inv ≫
      (((tensor tR tL hIR).obj ((πR).obj N)).map ((πL).map g) ≫ f) ≫
        (baseRProjectionIso dC).hom.app X =
      (πC).map (tensorMap (𝟙 ((qR).Q.obj N)) ((qL).Q.map g)) ≫
        ((tensorComparison tR tL hIR N M').inv ≫ f ≫ (baseRProjectionIso dC).hom.app X) := by
    simp only [Category.assoc]
    rw [reassoc_of% (tensorComparison_inv_naturality_right tR tL hIR N g).symm]
  have hQ : (leftQProjectionIso tL).inv.app M ≫ (πL).map ((qL).Q.map g) =
      (πL).map g ≫ (leftQProjectionIso tL).inv.app M' :=
    ((leftQProjectionIso tL).inv.naturality g).symm
  rw [representedHomEquiv_apply, representedHomEquiv_apply, hArg, originalHomEquiv_source]
  simp only [Category.assoc]
  rw [reassoc_of% hQ]

/-- The represented Hom function retains the complete original base-target naturality square. -/
theorem representedHomEquiv_target (hIR : IR.rlp = trivialFibrations C) (N : CR) (M : CL)
    {X X' : C} (g : X ⟶ X')
    (f : ((tensor tR tL hIR).obj ((πR).obj N)).obj ((πL).obj M) ⟶ (πC).obj X) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    representedHomEquiv tR tL dC hIR N M X' (f ≫ (πC).map g) =
      representedHomEquiv tR tL dC hIR N M X f ≫
        ((hom tR tL dC hIR).obj (op ((πR).obj N))).map ((πC).map g) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  have hR : (πC).map g ≫ (baseRProjectionIso dC).hom.app X' =
      (baseRProjectionIso dC).hom.app X ≫ (πC).map ((rC).R.map g) :=
    (baseRProjectionIso dC).hom.naturality g
  have hArg : (tensorComparison tR tL hIR N M).inv ≫ (f ≫ (πC).map g) ≫
        (baseRProjectionIso dC).hom.app X' =
      ((tensorComparison tR tL hIR N M).inv ≫ f ≫ (baseRProjectionIso dC).hom.app X) ≫
        (πC).map ((rC).R.map g) := by
    simp only [Category.assoc]
    rw [hR]
  have hHom : (πL).map ((homFunctor ((qR).Q.obj N)).map ((rC).R.map g)) ≫
        (homComparison tR tL dC hIR N X').inv =
      (homComparison tR tL dC hIR N X).inv ≫
        ((hom tR tL dC hIR).obj (op ((πR).obj N))).map ((πC).map g) :=
    homComparison_inv_naturality_target tR tL dC hIR N g
  rw [representedHomEquiv_apply, representedHomEquiv_apply, hArg, originalHomEquiv_target]
  simp only [Category.assoc]
  rw [hHom]

/-- The full represented Hom function retains every original right-module coefficient map. -/
theorem representedHomEquiv_parameter (hIR : IR.rlp = trivialFibrations C)
    {N N' : CR} (g : N ⟶ N') (M : CL) (X : C)
    (f : ((tensor tR tL hIR).obj ((πR).obj N')).obj ((πL).obj M) ⟶ (πC).obj X) :
    letI : ModelCategory CR := tR.model
    letI : ModelCategory CL := tL.model
    representedHomEquiv tR tL dC hIR N M X
        (((tensor tR tL hIR).map ((πR).map g)).app ((πL).obj M) ≫ f) =
      representedHomEquiv tR tL dC hIR N' M X f ≫
        ((hom tR tL dC hIR).map ((πR).map g).op).app ((πC).obj X) := by
  let : ModelCategory CR := tR.model
  let : ModelCategory CL := tL.model
  have hArg : (tensorComparison tR tL hIR N M).inv ≫
      (((tensor tR tL hIR).map ((πR).map g)).app ((πL).obj M) ≫ f) ≫
        (baseRProjectionIso dC).hom.app X =
      (πC).map (tensorMap ((qR).Q.map g) (𝟙 ((qL).Q.obj M))) ≫
        ((tensorComparison tR tL hIR N' M).inv ≫ f ≫ (baseRProjectionIso dC).hom.app X) := by
    simp only [Category.assoc]
    rw [reassoc_of% (tensorComparison_inv_naturality_left tR tL hIR g M).symm]
  have hHom : (πL).map (homPre ((qR).Q.map g) ((rC).R.obj X)) ≫
        (homComparison tR tL dC hIR N X).inv =
      (homComparison tR tL dC hIR N' X).inv ≫
        ((hom tR tL dC hIR).map ((πR).map g).op).app ((πC).obj X) :=
    homComparison_inv_naturality_parameter tR tL dC hIR g X
  rw [representedHomEquiv_apply, representedHomEquiv_apply, hArg, originalHomEquiv_parameter]
  simp only [Category.assoc]
  rw [hHom]

end HomotopicalAlgebra.ModuleTransfer.DerivedRightLeftTensor
