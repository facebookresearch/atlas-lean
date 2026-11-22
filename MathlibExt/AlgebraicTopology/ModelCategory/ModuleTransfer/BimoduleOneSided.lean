/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer.OriginalRank
public import MathlibExt.AlgebraicTopology.ModelCategory.StructuredReplacementComparisons
public import MathlibExt.CategoryTheory.Monoidal.Bimod.OneSidedColimits
public import MathlibExt.CategoryTheory.Monoidal.Bimod.RegularFree
public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.RightForgetCofibrations

/-!
# One-sided cofibrancy from the original bimodule cells

The original free bimodule generators become free one-sided generators
with a cofibrant outer coefficient. The actual colimit functors preserve
all original cell histories, so the full original lifting classes have
the same cofibration image. The bimodule and one-sided source ranks are
independent. The regular bimodule itself is never assumed cofibrant.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v wAB wR wL

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalOpposite
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.BimoduleOneSided

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
  {A B : Mon C} {I J : MorphismProperty C}
  {κAB : Cardinal.{wAB}} [Fact κAB.IsRegular] [OrderBot κAB.ord.ToType]
  (tAB : RightTransfer.OriginalRankModelTransfer (Bimod.free A B)
    (Bimod.forget (B := B) A) I J κAB)
  {κR : Cardinal.{wR}} [Fact κR.IsRegular] [OrderBot κR.ord.ToType]
  (tR : RightTransfer.OriginalRankModelTransfer (RightModuleFree.functor B.X)
    (Mod.forget (D := C) (mop B.X)) I J κR)

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original right free adjunction is Quillen in the actual original-rank one-sided model. -/
theorem rightFreeQuillen :
    letI : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
    (RightModuleFree.adjunction B.X).IsQuillenAdjunction := by
  let : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
  exact StructuredReplacementComparisons.actualQuillen
    (Mod.forget (D := C) (mop B.X)) tR.weak_eq (RightModuleFree.adjunction B.X) tR.fibrations_eq

section Right

variable [IsCofibrant A.X]

/-- Every original free-I bimodule generator is a cofibration in the original right-module model. -/
theorem originalFreeI_rightModule_cofibration (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
    I.strictMap (Bimod.free A B) ≤
      (cofibrations (RightModuleFree.Carrier B.X)).inverseImage (Bimod.rightModuleFunctor A B) := by
  let : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
  let : (RightModuleFree.adjunction B.X).IsQuillenAdjunction := rightFreeQuillen tR
  let : (ihom.adjunction A.X).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant A.X
  intro M N f hf
  cases hf with
  | @map X Y i hi =>
    change cofibrations (RightModuleFree.Carrier B.X)
      ((RightModuleFree.functor B.X).map (A.X ◁ i))
    have h := I.le_llp_rlp i hi
    rw [hI, trivialFibrations_llp] at h
    exact Adjunction.IsQuillenAdjunction.preservesCofibrations
      (adj := RightModuleFree.adjunction B.X) _
      (Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := ihom.adjunction A.X) i h)

variable [HasColimitsOfSize.{wAB, wAB} C]

/-- The entire original bimodule cell and retract class forgets to original right-module cofibrations. -/
theorem rightModule_cofibrations (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
    cofibrations (Bimod A B) ≤
      (cofibrations (RightModuleFree.Carrier B.X)).inverseImage (Bimod.rightModuleFunctor A B) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
  let : HasColimitsOfSize.{wAB, wAB} (Bimod A B) := tAB.cocomplete
  let : HasColimitsOfSize.{wAB, wAB} (RightModuleFree.Carrier B.X) :=
    RightModuleFree.hasColimits B.X
  let U := Bimod.rightModuleFunctor A B
  let : PreservesColimitsOfSize.{wAB, wAB} U := Bimod.rightModuleFunctor_preservesColimits A B
  let : PreservesWellOrderContinuousOfShape κAB.ord.ToType U :=
    { preservesColimitsOfShape := fun _ _ => by infer_instance }
  let : (I.strictMap (Bimod.free A B)).IsCardinalForSmallObjectArgument κAB := by
    rw [← tAB.generation_I]
    exact tAB.generation.I_smallObject
  let : (cofibrations (RightModuleFree.Carrier B.X)).IsStableUnderCoproducts.{wAB} := by
    rw [← trivialFibrations_llp]
    infer_instance
  let : (cofibrations (RightModuleFree.Carrier B.X)).IsStableUnderCobaseChange := by
    rw [← trivialFibrations_llp]
    infer_instance
  let : (cofibrations (RightModuleFree.Carrier B.X)).IsStableUnderTransfiniteCompositionOfShape
      κAB.ord.ToType := by
    rw [← trivialFibrations_llp]
    infer_instance
  have hCof : cofibrations (Bimod A B) = (I.strictMap (Bimod.free A B)).rlp.llp := by
    rw [← tAB.generation_I, tAB.generation.I_rlp, trivialFibrations_llp]
  rw [hCof]
  exact MorphismProperty.rlp_llp_le_inverseImage_of_cardinal_closure
    (I.strictMap (Bimod.free A B)) (cofibrations (RightModuleFree.Carrier B.X)) U κAB
    (originalFreeI_rightModule_cofibration tR hI)

/-- A cofibrant original bimodule has cofibrant original right module after forgetting its left action. -/
theorem rightModule_isCofibrant (hI : I.rlp = trivialFibrations C) (M : Bimod A B) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
    IsCofibrant M → IsCofibrant (Bimod.toRightModule M) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
  let : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeOfUnivLE.{wAB, wAB} C
  let U := Bimod.rightModuleFunctor A B
  let : PreservesColimitsOfSize.{0, 0} U := Bimod.rightModuleFunctor_preservesColimits A B
  intro hM
  let : IsCofibrant M := hM
  have hi := rightModule_cofibrations tAB tR hI (initial.to M) (mem_cofibrations (initial.to M))
  let : Cofibration (U.map (initial.to M)) := (cofibration_iff _).mpr hi
  exact (isCofibrant_iff_of_isInitial (U.map (initial.to M))
    (initialIsInitial.isInitialObj U)).mpr inferInstance

end Right

variable {κL : Cardinal.{wL}} [Fact κL.IsRegular] [OrderBot κL.ord.ToType]
  (tL : RightTransfer.OriginalRankModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X) I J κL)

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original left free adjunction is Quillen in its actual independently ranked model. -/
theorem leftFreeQuillen :
    letI : ModelCategory (Mod C A.X) := tL.model
    (Mod.freeForgetAdjunction A.X).IsQuillenAdjunction := by
  let : ModelCategory (Mod C A.X) := tL.model
  exact StructuredReplacementComparisons.actualQuillen
    (Mod.forget (D := C) A.X) tL.weak_eq (Mod.freeForgetAdjunction A.X) tL.fibrations_eq

section Left

variable [IsCofibrant B.X]

/-- Every original free-I bimodule generator is a cofibration in the actual left-module model. -/
theorem originalFreeI_leftModule_cofibration (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (Mod C A.X) := tL.model
    I.strictMap (Bimod.free A B) ≤
      (cofibrations (Mod C A.X)).inverseImage (Bimod.leftModuleFunctor A B) := by
  let : ModelCategory (Mod C A.X) := tL.model
  let : (Mod.freeForgetAdjunction A.X).IsQuillenAdjunction := leftFreeQuillen tL
  intro M N f hf
  cases hf with
  | @map X Y i hi =>
    have hBase : cofibrations C (i ▷ B.X) :=
      RightForgetCofibrations.originalRightFreeI_underlying_cofibration (A := B.X) I hI
        ((RightModuleFree.functor B.X).map i)
        (I.map_mem_strictMap (RightModuleFree.functor B.X) i hi)
    have hFree := Adjunction.IsQuillenAdjunction.preservesCofibrations
      (adj := Mod.freeForgetAdjunction A.X) _ hBase
    let e : Arrow.mk ((Bimod.leftModuleFunctor A B).map ((Bimod.free A B).map i)) ≅
        Arrow.mk ((Mod.free A.X).map (i ▷ B.X)) :=
      Arrow.isoMk (Bimod.freeLeftModuleIso A B X) (Bimod.freeLeftModuleIso A B Y)
        ((Bimod.freeLeftModuleNatIso A B).hom.naturality i).symm
    exact ((cofibrations (Mod C A.X)).arrow_mk_iso_iff e).mpr hFree

variable [HasColimitsOfSize.{wAB, wAB} C]

/-- The full original bimodule cell and retract class retains its actual left-module cofibration image. -/
theorem leftModule_cofibrations (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Mod C A.X) := tL.model
    cofibrations (Bimod A B) ≤
      (cofibrations (Mod C A.X)).inverseImage (Bimod.leftModuleFunctor A B) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Mod C A.X) := tL.model
  let : HasColimitsOfSize.{wAB, wAB} (Bimod A B) := tAB.cocomplete
  let : HasColimitsOfSize.{wAB, wAB} (Mod C A.X) := Mod.hasColimits A.X
  let U := Bimod.leftModuleFunctor A B
  let : PreservesColimitsOfSize.{wAB, wAB} U := Bimod.leftModuleFunctor_preservesColimits A B
  let : PreservesWellOrderContinuousOfShape κAB.ord.ToType U :=
    { preservesColimitsOfShape := fun _ _ => by infer_instance }
  let : (I.strictMap (Bimod.free A B)).IsCardinalForSmallObjectArgument κAB := by
    rw [← tAB.generation_I]
    exact tAB.generation.I_smallObject
  let : (cofibrations (Mod C A.X)).IsStableUnderCoproducts.{wAB} := by
    rw [← trivialFibrations_llp]
    infer_instance
  let : (cofibrations (Mod C A.X)).IsStableUnderCobaseChange := by
    rw [← trivialFibrations_llp]
    infer_instance
  let : (cofibrations (Mod C A.X)).IsStableUnderTransfiniteCompositionOfShape κAB.ord.ToType := by
    rw [← trivialFibrations_llp]
    infer_instance
  have hCof : cofibrations (Bimod A B) = (I.strictMap (Bimod.free A B)).rlp.llp := by
    rw [← tAB.generation_I, tAB.generation.I_rlp, trivialFibrations_llp]
  rw [hCof]
  exact MorphismProperty.rlp_llp_le_inverseImage_of_cardinal_closure
    (I.strictMap (Bimod.free A B)) (cofibrations (Mod C A.X)) U κAB
    (originalFreeI_leftModule_cofibration tL hI)

/-- A cofibrant original bimodule has cofibrant original left module after forgetting its right action. -/
theorem leftModule_isCofibrant (hI : I.rlp = trivialFibrations C) (M : Bimod A B) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Mod C A.X) := tL.model
    IsCofibrant M → IsCofibrant (Bimod.toLeftModule M) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Mod C A.X) := tL.model
  let : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeOfUnivLE.{wAB, wAB} C
  let U := Bimod.leftModuleFunctor A B
  let : PreservesColimitsOfSize.{0, 0} U := Bimod.leftModuleFunctor_preservesColimits A B
  intro hM
  let : IsCofibrant M := hM
  have hi := leftModule_cofibrations tAB tL hI (initial.to M) (mem_cofibrations (initial.to M))
  let : Cofibration (U.map (initial.to M)) := (cofibration_iff _).mpr hi
  exact (isCofibrant_iff_of_isInitial (U.map (initial.to M))
    (initialIsInitial.isInitialObj U)).mpr inferInstance

end Left

section Regular

variable [IsCofibrant (𝟙_ C)]

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original regular right module is cofibrant as free on the cofibrant base unit. -/
theorem regularRight_isCofibrant :
    letI : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
    IsCofibrant (Bimod.toRightModule (Bimod.regular B)) := by
  let : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
  let : (RightModuleFree.adjunction B.X).IsQuillenAdjunction := rightFreeQuillen tR
  let : IsCofibrant ((RightModuleFree.functor B.X).obj (𝟙_ C)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := RightModuleFree.adjunction B.X)
      inferInstance
  exact isCofibrant_of_cofibration (Bimod.regularRightFreeIso B).hom

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original regular left module is cofibrant by the other actual free-unit comparison. -/
theorem regularLeft_isCofibrant :
    letI : ModelCategory (Mod C A.X) := tL.model
    IsCofibrant (Bimod.toLeftModule (Bimod.regular A)) := by
  let : ModelCategory (Mod C A.X) := tL.model
  let : (Mod.freeForgetAdjunction A.X).IsQuillenAdjunction := leftFreeQuillen tL
  let : IsCofibrant ((Mod.free A.X).obj (𝟙_ C)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := Mod.freeForgetAdjunction A.X)
      inferInstance
  exact isCofibrant_of_cofibration (Bimod.regularLeftFreeIso A).hom

end Regular

end HomotopicalAlgebra.ModuleTransfer.BimoduleOneSided
