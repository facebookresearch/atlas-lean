/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.DerivedAmbientAssociatorSource

/-!
# The full actual external derived module associator

The two actual module-action brackets are the liftings of their original
three-variable Q source functors. The complete source associator therefore
lifts to all coefficient and module homotopy objects and all their arrows.
The base tensor is the qualified actual chosen QQ tensor at the original
base generation; the module carrier is its original localization.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v wA wC

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MorphismProperty Functor
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  {A : C} [MonObj A] {I J : MorphismProperty C}
  {κA : Cardinal.{wA}} [Fact κA.IsRegular] [OrderBot κA.ord.ToType]
  (tA : RightTransfer.OriginalRankModelTransfer (Mod.free A) (Mod.forget (D := C) A) I J κA)
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  (dC : CofibrantGenerationData C κC)

local notation "qC" => GeneratedFunctorialReplacements.fromGeneration dC
local notation "M" => Mod C A
local notation "WC" => weakEquivalences C
local notation "WA" => moduleWeak tA
local notation "HA" => MorphismProperty.Localization WA
local notation "HC" => MorphismProperty.Localization WC
local notation "πA" => MorphismProperty.Q WA
local notation "πC" => MorphismProperty.Q WC

/-- The actual base QQ tensor followed by the original action retains its whole original source bracket. -/
instance leftBracketLifting :
    Localization.Lifting₃ πC πC πA WC WC WA (rawLeftBracket tA dC)
      (bifunctorComp₁₂ (DerivedTensorConstructions.tensor (qC)) (action tA dC)) := by
  let : ModelCategory M := tA.model
  let : Localization.Lifting₂ πC πC WC WC
      (DerivedTensorConstructions.replacedTensor (qC) ⋙ (whiskeringRight C C HC).obj πC)
      (DerivedTensorConstructions.tensor (qC)) := by
    change Localization.Lifting₂ πC πC WC WC
      (DerivedTensorConstructions.raw (qC)) (DerivedTensorConstructions.tensor (qC))
    infer_instance
  let : Localization.Lifting₂ πC πA WC WA
      (replaced tA dC ⋙ (whiskeringRight M M HA).obj πA) (action tA dC) := by
    change Localization.Lifting₂ πC πA WC WA (raw tA dC) (action tA dC)
    infer_instance
  exact Localization.Lifting₃.bifunctorComp₁₂ πC πC πA πC πA WC WC WA WC
    (DerivedTensorConstructions.replacedTensor (qC)) (replaced tA dC)
    (DerivedTensorConstructions.tensor (qC)) (action tA dC)

/-- Iterating the same original actual action retains its complete original module-replacement source bracket. -/
instance rightBracketLifting :
    Localization.Lifting₃ πC πC πA WC WC WA (rawRightBracket tA dC)
      (bifunctorComp₂₃ (action tA dC) (action tA dC)) := by
  let : ModelCategory M := tA.model
  let : Localization.Lifting₂ πC πA WC WA
      (replaced tA dC ⋙ (whiskeringRight M M HA).obj πA) (action tA dC) := by
    change Localization.Lifting₂ πC πA WC WA (raw tA dC) (action tA dC)
    infer_instance
  exact Localization.Lifting₃.bifunctorComp₂₃ πC πC πA πA πA WC WC WA WA
    (replaced tA dC) (replaced tA dC) (action tA dC) (action tA dC)

/-- The full natural external derived associator on every original localized coefficient and module. -/
def derivedAssociator :
    bifunctorComp₁₂ (DerivedTensorConstructions.tensor (qC)) (action tA dC) ≅
      bifunctorComp₂₃ (action tA dC) (action tA dC) := by
  letI : ModelCategory M := tA.model
  exact Localization.lift₃NatIso πC πC πA WC WC WA
    (rawLeftBracket tA dC) (rawRightBracket tA dC)
    (bifunctorComp₁₂ (DerivedTensorConstructions.tensor (qC)) (action tA dC))
    (bifunctorComp₂₃ (action tA dC) (action tA dC)) (rawBracketAssociator tA dC)

/-- Every original projected triple retains the entire source associator and both actual bracket liftings. -/
theorem derivedAssociator_hom_app (U V : C) (N : M) :
    (((derivedAssociator tA dC).hom.app ((πC).obj U)).app ((πC).obj V)).app ((πA).obj N) =
      (((Localization.Lifting₃.iso πC πC πA WC WC WA (rawLeftBracket tA dC)
        (bifunctorComp₁₂ (DerivedTensorConstructions.tensor (qC)) (action tA dC))).hom.app U).app V).app N ≫
      (((rawBracketAssociator tA dC).hom.app U).app V).app N ≫
      (((Localization.Lifting₃.iso πC πC πA WC WC WA (rawRightBracket tA dC)
        (bifunctorComp₂₃ (action tA dC) (action tA dC))).inv.app U).app V).app N := by
  let : ModelCategory M := tA.model
  exact Localization.lift₃NatTrans_app_app_app πC πC πA WC WC WA
    (rawLeftBracket tA dC) (rawRightBracket tA dC)
    (bifunctorComp₁₂ (DerivedTensorConstructions.tensor (qC)) (action tA dC))
    (bifunctorComp₂₃ (action tA dC) (action tA dC)) (rawBracketAssociator tA dC).hom U V N

end HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction
