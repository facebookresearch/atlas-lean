/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAdjunctionBase
public import MathlibExt.CategoryTheory.Monoidal.RightModuleRelativeTensor

/-!
# Typed selected enriched Day source

Named source data and typed accessors retain the selected categories, limits,
coefficient monoid, relative tensor, and complete quotient function.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open scoped MonoidalClosed CategoryTheory.MonObj

universe uV vV uI vI

namespace CategoryTheory.Enriched.ModuleMappingR
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

variable (V : Type uV) [categoryV : Category.{vV} V]
  [monoidalV : MonoidalCategory V] [symmetricV : SymmetricCategory V]
  [closedV : MonoidalClosed V]
  (I : Type uI) [categoryI : Category.{vI} I]
  [monoidalI : MonoidalCategory I] [symmetricI : SymmetricCategory I]
  [enrichment : EnrichedOrdinaryCategory V I]
  [colimits : HasColimitsOfSize.{uI, uI} V]
  [products : HasProducts.{uI} V] [equalizers : HasEqualizers V]

/-- The selected enriched Day data and its actual braided lax coefficient functor.
The ambient categories, enrichment, and limit dictionaries are typed parameters of the
record, so its accessors retain their selected values without inspecting a constructor. -/
structure SelectedSource (V : Type uV) [categoryV : Category.{vV} V]
    [monoidalV : MonoidalCategory V] [symmetricV : SymmetricCategory V]
    [closedV : MonoidalClosed V] (I : Type uI) [categoryI : Category.{vI} I]
    [monoidalI : MonoidalCategory I] [symmetricI : SymmetricCategory I]
    [enrichment : EnrichedOrdinaryCategory V I]
    [colimits : HasColimitsOfSize.{uI, uI} V]
    [products : HasProducts.{uI} V] [equalizers : HasEqualizers V] where
  /-- The selected whole enriched tensor on the index. -/
  monoidalData : EnrichedMonoidalCategoryData V I
  /-- The selected enriched braid for that tensor. -/
  braidedData : EnrichedBraidedMonoidalCategoryData V I monoidalData
  /-- The complete original coefficient functor. -/
  coefficientFunctor : EnrichedFunctor V I V
  /-- Its original lax monoidal data. -/
  coefficientMonoidal : EnrichedFunctor.LaxMonoidalData monoidalData
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) coefficientFunctor
  /-- Its original compatibility with the complete braid. -/
  coefficientBraided : EnrichedFunctor.LaxBraidedData coefficientMonoidal

namespace SelectedSource
variable {V I}

/-- The selected coefficient-base category. -/
@[instance_reducible]
def baseCategory (_q : SelectedSource V I) : Category.{vV} V := categoryV
/-- The selected coefficient-base tensor. -/
@[instance_reducible]
def baseMonoidal (_q : SelectedSource V I) : MonoidalCategory V := monoidalV
/-- The selected coefficient-base symmetry. -/
@[instance_reducible]
def baseSymmetric (_q : SelectedSource V I) : SymmetricCategory V := symmetricV
/-- The selected coefficient-base closed structure. -/
@[instance_reducible]
def baseClosed (_q : SelectedSource V I) : MonoidalClosed V := closedV
/-- The selected ordinary index category. -/
@[instance_reducible]
def indexCategory (_q : SelectedSource V I) : Category.{vI} I := categoryI
/-- The selected whole index tensor. -/
@[instance_reducible]
def indexMonoidal (_q : SelectedSource V I) : MonoidalCategory I := monoidalI
/-- The selected index symmetry. -/
@[instance_reducible]
def indexSymmetric (_q : SelectedSource V I) : SymmetricCategory I := symmetricI
/-- The selected complete ordinary enrichment. -/
@[instance_reducible]
def ordinaryEnrichment (_q : SelectedSource V I) : EnrichedOrdinaryCategory V I := enrichment
/-- The selected pointwise-colimit input. -/
theorem hasColimits (_q : SelectedSource V I) : HasColimitsOfSize.{uI, uI} V := colimits
/-- The selected full product input. -/
theorem hasProducts (_q : SelectedSource V I) : HasProducts.{uI} V := products
/-- The selected equalizer input. -/
theorem hasEqualizers (_q : SelectedSource V I) : HasEqualizers V := equalizers

/-- The ordinary category of the selected enriched Day diagrams, in the original dictionaries. -/
@[instance_reducible]
def dayCategory (_q : SelectedSource V I) : Category (EnrichedFunctorCat V I) := inferInstance

/-- The whole actual enriched Day coefficient object. -/
abbrev coefficient (q : SelectedSource V I) : EnrichedFunctorCat V I :=
  ⟨q.coefficientFunctor⟩
/-- The actual Day tensor from the named enriched data. -/
@[instance_reducible]
def dayMonoidal (q : SelectedSource V I) : MonoidalCategory (EnrichedFunctorCat V I) :=
  EnrichedDayKernel.ColimitMonoidal.monoidalCategory q.monoidalData

/-- The complete selected Day tensor object operation. -/
def dayTensorObj (q : SelectedSource V I) (X Y : EnrichedFunctorCat V I) : EnrichedFunctorCat V I :=
  @MonoidalCategoryStruct.tensorObj _ q.dayCategory q.dayMonoidal.toMonoidalCategoryStruct X Y

/-- The complete selected Day tensor morphism operation, with all objects and arrows retained. -/
def dayTensorHom (q : SelectedSource V I) :
    letI := q.dayCategory
    letI := q.dayMonoidal
    ∀ {X X' Y Y' : EnrichedFunctorCat V I}, (X ⟶ X') → (Y ⟶ Y') → (X ⊗ Y ⟶ X' ⊗ Y') :=
  @MonoidalCategoryStruct.tensorHom _ q.dayCategory q.dayMonoidal.toMonoidalCategoryStruct

/-- The actual Day braid from the named enriched data. -/
@[instance_reducible]
def daySymmetric (q : SelectedSource V I) :
    letI := q.dayMonoidal
    SymmetricCategory (EnrichedFunctorCat V I) :=
  EnrichedDayKernel.BraidingMonoidal.symmetricCategory q.monoidalData q.braidedData
/-- The actual closed Day structure from the same named tensor. -/
@[instance_reducible]
def dayClosed (q : SelectedSource V I) :
    letI := q.dayMonoidal
    MonoidalClosed (EnrichedFunctorCat V I) :=
  EnrichedDayKernel.Closed.monoidalClosed q.monoidalData
/-- The original whole coefficient monoid. -/
@[instance_reducible]
def coefficientMonObj (q : SelectedSource V I) :
    letI := q.dayMonoidal
    MonObj q.coefficient :=
  EnrichedDayKernel.LaxMonoid.monObj q.monoidalData q.coefficientFunctor q.coefficientMonoidal
/-- The original coefficient commutativity from the entire enriched braid. -/
theorem coefficientIsComm (q : SelectedSource V I) :
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.coefficientMonObj
    IsCommMonObj q.coefficient :=
  EnrichedDayKernel.LaxMonoid.isCommMonObj q.monoidalData q.braidedData
    q.coefficientFunctor q.coefficientMonoidal q.coefficientBraided
/-- The actual stock module category of the selected coefficient. -/
abbrev Module (q : SelectedSource V I) :=
  ModuleMappingR.Module q.monoidalData q.coefficientFunctor q.coefficientMonoidal
/-- The complete Day category has its original coequalizers. -/
abbrev DayCoequalizersType (_q : SelectedSource V I) : Prop :=
  HasCoequalizers (EnrichedFunctorCat V I)
/-- The original selected pointwise colimits supply Day coequalizers. -/
theorem dayCoequalizers (q : SelectedSource V I) : q.DayCoequalizersType := by
  infer_instance

/-- The entire original left tensor preserves every small colimit, for every object. -/
abbrev DayTensorLeftPreservationType (q : SelectedSource V I) : Prop :=
  letI := q.dayMonoidal
  ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)
/-- The original closed Day preservation family retains every future tensor factor. -/
theorem dayTensorLeftPreserves (q : SelectedSource V I) : q.DayTensorLeftPreservationType := by
  let := q.dayMonoidal
  exact (EnrichedDayKernel.Closed.smallTensorPreservationFamilies
    q.monoidalData q.braidedData).1
/-- The entire original right tensor preserves every small colimit, for every object. -/
abbrev DayTensorRightPreservationType (q : SelectedSource V I) : Prop :=
  letI := q.dayMonoidal
  ∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)
/-- The original closed Day preservation family retains every future tensor factor. -/
theorem dayTensorRightPreserves (q : SelectedSource V I) : q.DayTensorRightPreservationType := by
  let := q.dayMonoidal
  exact (EnrichedDayKernel.Closed.smallTensorPreservationFamilies
    q.monoidalData q.braidedData).2

/-- The exact stock right-module category of the selected full coefficient. -/
@[instance_reducible]
def moduleCategory (q : SelectedSource V I) : Category q.Module :=
  SphereModuleMappingEnd.moduleCategory q.monoidalData q.coefficientFunctor q.coefficientMonoidal
/-- The whole relative tensor assembled by the original typed source constructor. -/
@[instance_reducible]
def moduleMonoidal (q : SelectedSource V I) :
    @MonoidalCategory q.Module q.moduleCategory :=
  ModuleMappingR.moduleMonoidal q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided

/-- The entire quotient function type, written using the named selected data. -/
def ProjectionType (q : SelectedSource V I) :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y : q.Module), X.X ⊗ Y.X ⟶ (X ⊗ Y).X

/-- The complete canonical quotient function of the selected source tensor. -/
def projection (q : SelectedSource V I) : q.ProjectionType := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.moduleMonoidal
  exact RightModuleFree.relativeTensorπ q.coefficient

end SelectedSource
end CategoryTheory.Enriched.ModuleMappingR

namespace CategoryTheory.Enriched.ModuleMappingR.SelectedSource
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [categoryV : Category.{vV} V]
  [monoidalV : MonoidalCategory V] [symmetricV : SymmetricCategory V]
  [closedV : MonoidalClosed V]
  {I : Type uI} [categoryI : Category.{vI} I]
  [monoidalI : MonoidalCategory I] [symmetricI : SymmetricCategory I]
  [enrichment : EnrichedOrdinaryCategory V I]
  [colimits : HasColimitsOfSize.{uI, uI} V]
  [products : HasProducts.{uI} V] [equalizers : HasEqualizers V]

/-- The same source tensor exposed at its canonical primitive constructor. -/
@[instance_reducible]
def primitiveMonoidal (q : SelectedSource V I) : MonoidalCategory q.Module := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  exact RightModuleFree.tensorMonoidal q.coefficient
/-- The named source tensor and its original primitive tensor are the same whole structure. -/
theorem moduleMonoidal_eq_primitive (q : SelectedSource V I) :
    q.moduleMonoidal = q.primitiveMonoidal := rfl
/-- The original source-module symmetry uses the same selected relative tensor. -/
@[instance_reducible]
def moduleSymmetric (q : SelectedSource V I) :
    letI := q.moduleMonoidal
    @SymmetricCategory q.Module q.moduleCategory q.moduleMonoidal :=
  ModuleMappingR.moduleSymmetric q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided
end CategoryTheory.Enriched.ModuleMappingR.SelectedSource

namespace CategoryTheory.Enriched.ModuleMappingR.SelectedSource
open CategoryTheory Limits MonoidalCategory
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
attribute [local instance] SelectedSource.moduleCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]

/-- The entire actual translated Mapping_R functor, including every selected module map. -/
def mappingFunctor (q : SelectedSource V I) (M : q.Module) :
    @Functor q.Module q.moduleCategory q.Module q.moduleCategory :=
  ModuleMappingR.functor q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided M

/-- The selected source closed structure is the original full translated action equalizer. -/
@[instance_reducible]
def moduleClosed (q : SelectedSource V I) :
    letI := q.moduleMonoidal
    @MonoidalClosed q.Module q.moduleCategory q.moduleMonoidal :=
  ModuleMappingR.moduleClosed q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided

/-- The complete selected adjunction family retains the original named category and tensor. -/
def LeftAdjunctionType (q : SelectedSource V I) :=
  letI := q.moduleMonoidal
  ∀ M : q.Module,
    @Adjunction q.Module q.moduleCategory q.Module q.moduleCategory
      (@tensorLeft q.Module q.moduleCategory q.moduleMonoidal M) (q.mappingFunctor M)

/-- The chosen closed structure supplies the entire original selected adjunction family. -/
def leftAdjunctionFamily (q : SelectedSource V I) : q.LeftAdjunctionType := by
  letI := q.moduleMonoidal
  letI := q.moduleClosed
  exact fun M => ihom.adjunction M

/-- The original balanced source adjunction for the whole chosen Mapping_R. -/
def leftAdjunction (q : SelectedSource V I) (M : q.Module) :
    letI := q.moduleMonoidal
    @Adjunction q.Module q.moduleCategory q.Module q.moduleCategory
      (@tensorLeft q.Module q.moduleCategory q.moduleMonoidal M) (q.mappingFunctor M) :=
  q.leftAdjunctionFamily M

/-- The entire chosen internal Hom is the actual selected Mapping_R functor. -/
theorem moduleClosed_ihom (q : SelectedSource V I) (M : q.Module) :
    letI := q.moduleMonoidal
    letI := q.moduleClosed
    ihom M = q.mappingFunctor M := rfl

/-- The entire chosen source adjunction record is the original balanced adjunction. -/
theorem moduleClosed_adjunction (q : SelectedSource V I) (M : q.Module) :
    letI := q.moduleMonoidal
    letI := q.moduleClosed
    ihom.adjunction M = q.leftAdjunction M := rfl

/-- The chosen closed carrier retains the complete original translated action equalizer diagram. -/
theorem moduleClosed_diagram (q : SelectedSource V I) (M N : q.Module) :
    letI := q.moduleMonoidal
    letI := q.moduleClosed
    SphereModuleMappingEnd.diagram q.monoidalData q.coefficientFunctor q.coefficientMonoidal
        ((ihom M).obj N) =
      ModuleMappingR.diagram q.monoidalData q.braidedData q.coefficientFunctor
        q.coefficientMonoidal M N :=
  ModuleMappingR.moduleClosed_diagram q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided M N

/-- Every whole target module arrow acts by the original equalizer postcomposition map. -/
theorem moduleClosed_map (q : SelectedSource V I) (M : q.Module)
    {N N' : q.Module} (g : N ⟶ N') :
    letI := q.moduleMonoidal
    letI := q.moduleClosed
    SphereModuleMappingEnd.moduleMap q.monoidalData q.coefficientFunctor q.coefficientMonoidal
        ((ihom M).map g) =
      ModuleMappingR.post q.monoidalData q.braidedData q.coefficientFunctor
        q.coefficientMonoidal M g :=
  ModuleMappingR.moduleClosed_map q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided M g

end CategoryTheory.Enriched.ModuleMappingR.SelectedSource

namespace CategoryTheory.Enriched.ModuleMappingR.SelectedSource
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]

/-- The complete original selected-source carrierEqCoequalizer family. -/
def CarrierEqCoequalizerType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y : q.Module), (X ⊗ Y).X =
      coequalizer (RightModuleFree.balanceFirst q.coefficient X Y)
        (RightModuleFree.balanceSecond q.coefficient X Y)

/-- The original canonical supplier for the whole carrierEqCoequalizer family. -/
theorem carrierEqCoequalizer (q : SelectedSource V I) : q.CarrierEqCoequalizerType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  exact RightModuleFree.relativeTensor_carrier q.coefficient

/-- The complete original selected-source projectionBalance family. -/
def ProjectionBalanceType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y : q.Module),
      (X.action ▷ Y.X) ≫ q.projection X Y =
        (α_ X.X q.coefficient Y.X).hom ≫
          (X.X ◁ CommutativeModuleConversion.leftAction q.coefficient Y) ≫ q.projection X Y

/-- The original canonical supplier for the whole projectionBalance family. -/
theorem projectionBalance (q : SelectedSource V I) : q.ProjectionBalanceType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  exact RightModuleFree.relativeTensorπ_balance q.coefficient

/-- The complete original selected-source quotientIsColimit family. -/
def QuotientIsColimitType (q : SelectedSource V I) :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y : q.Module), IsColimit (RightModuleFree.relativeTensorCofork q.coefficient X Y)

/-- The original canonical supplier for the whole quotientIsColimit family. -/
def quotientIsColimit (q : SelectedSource V I) : q.QuotientIsColimitType := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.moduleMonoidal
  exact RightModuleFree.relativeTensorCoforkIsColimit q.coefficient

/-- The complete original selected-source projectionAction family. -/
def ProjectionActionType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y : q.Module),
      (q.projection X Y ▷ q.coefficient) ≫ (X ⊗ Y).action =
        (α_ X.X Y.X q.coefficient).hom ≫ (X.X ◁ Y.action) ≫ q.projection X Y

/-- The original canonical supplier for the whole projectionAction family. -/
theorem projectionAction (q : SelectedSource V I) : q.ProjectionActionType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  exact RightModuleFree.relativeTensorπ_action q.coefficient

/-- The complete original selected-source projectionEpi family. -/
def ProjectionEpiType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y : q.Module), Epi (q.projection X Y)

/-- The original canonical supplier for the whole projectionEpi family. -/
theorem projectionEpi (q : SelectedSource V I) : q.ProjectionEpiType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  exact RightModuleFree.relativeTensorπ_epi q.coefficient

/-- The complete original selected-source projectionMap family. -/
def ProjectionMapType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ {X X' Y Y' : q.Module} (f : X ⟶ X') (g : Y ⟶ Y'),
      q.projection X Y ≫ (f ⊗ₘ g).hom =
        (f.hom ⊗ₘ g.hom) ≫ q.projection X' Y'

/-- The original canonical supplier for the whole projectionMap family. -/
theorem projectionMap (q : SelectedSource V I) : q.ProjectionMapType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  exact fun {X X' Y Y'} f g => RightModuleFree.relativeTensorMap_π q.coefficient f g

/-- The complete original selected-source descBalanced family. -/
def DescBalancedType (q : SelectedSource V I) :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y Z : q.Module),
      RightModuleFree.BalancedRightLinearMap q.coefficient X Y Z → (X ⊗ Y ⟶ Z)

/-- The original canonical supplier for the whole descBalanced family. -/
def descBalanced (q : SelectedSource V I) : q.DescBalancedType := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.moduleMonoidal
  exact RightModuleFree.relativeTensorDescBalanced q.coefficient

/-- The complete original selected-source homEquiv family. -/
def HomEquivType (q : SelectedSource V I) :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y Z : q.Module),
      (X ⊗ Y ⟶ Z) ≃ RightModuleFree.BalancedRightLinearMap q.coefficient X Y Z

/-- The original canonical supplier for the whole homEquiv family. -/
def homEquiv (q : SelectedSource V I) : q.HomEquivType := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.moduleMonoidal
  exact RightModuleFree.relativeTensorHomEquiv q.coefficient

/-- The complete original selected-source homEquiv_hom family. -/
def HomEquivHomType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y Z : q.Module) (f : X ⊗ Y ⟶ Z),
      (q.homEquiv X Y Z f).hom = q.projection X Y ≫ f.hom

/-- The original canonical supplier for the whole homEquiv_hom family. -/
theorem homEquiv_hom (q : SelectedSource V I) : q.HomEquivHomType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  exact RightModuleFree.relativeTensorHomEquiv_hom q.coefficient

/-- The complete original selected-source homEquiv_symm family. -/
def HomEquivSymmType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y Z : q.Module) (f : RightModuleFree.BalancedRightLinearMap q.coefficient X Y Z),
      (q.homEquiv X Y Z).symm f = q.descBalanced X Y Z f

/-- The original canonical supplier for the whole homEquiv_symm family. -/
theorem homEquiv_symm (q : SelectedSource V I) : q.HomEquivSymmType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  exact RightModuleFree.relativeTensorHomEquiv_symm q.coefficient

/-- The complete original selected-source projection_homEquiv_symm family. -/
def ProjectionHomEquivSymmType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y Z : q.Module) (f : RightModuleFree.BalancedRightLinearMap q.coefficient X Y Z),
      q.projection X Y ≫ ((q.homEquiv X Y Z).symm f).hom = f.hom

/-- The original canonical supplier for the whole projection_homEquiv_symm family. -/
theorem projection_homEquiv_symm (q : SelectedSource V I) : q.ProjectionHomEquivSymmType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  exact RightModuleFree.relativeTensorDescBalanced_π q.coefficient

end CategoryTheory.Enriched.ModuleMappingR.SelectedSource

namespace CategoryTheory.Enriched.ModuleMappingR.SelectedSource
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]

/-- The complete selected-source coend generator function, with every isometry coefficient. -/
def CoendGeneratorType (q : SelectedSource V I) :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y : q.Module) (k : I) (a : I × I),
      EnrichedDayKernel.objects q.monoidalData.tensorEnrichedFunctor
        X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a ⟶
          (X ⊗ Y).X.toEnrichedFunctor.obj k

/-- Each entire Day generator is followed by the original complete sphere quotient. -/
def coendGenerator (q : SelectedSource V I) : q.CoendGeneratorType := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.moduleMonoidal
  exact fun X Y k a =>
    EnrichedDayKernel.gen q.monoidalData.tensorEnrichedFunctor
      X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a ≫
        EnrichedFunctorCat.component (q.projection X Y) k

end CategoryTheory.Enriched.ModuleMappingR.SelectedSource

namespace CategoryTheory.Enriched.ModuleMappingR.SelectedSource
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]

/-- Every selected coend generator is the whole Day generator followed by the scalar quotient. -/
def CoendGeneratorFormulaType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y : q.Module) (k : I) (a : I × I),
      q.coendGenerator X Y k a =
        EnrichedDayKernel.gen q.monoidalData.tensorEnrichedFunctor
          X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a ≫
            EnrichedFunctorCat.component (q.projection X Y) k

/-- The selected generator computes the original whole coend and quotient formula. -/
theorem coendGenerator_formula (q : SelectedSource V I) : q.CoendGeneratorFormulaType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  intro X Y k a
  rfl

/-- The full output-enriched Hom acts naturally on every selected quotient projection. -/
def ProjectionFullHomType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y : q.Module) (k l : I),
      MonoidalClosed.uncurry ((X.X ⊗ Y.X).toEnrichedFunctor.map k l) ≫
          EnrichedFunctorCat.component (q.projection X Y) l =
        (EnrichedFunctorCat.component (q.projection X Y) k ⊗ₘ 𝟙 (k ⟶[V] l)) ≫
          MonoidalClosed.uncurry ((X ⊗ Y).X.toEnrichedFunctor.map k l)

/-- The original full enriched naturality of the selected quotient supplies the formula. -/
theorem projection_fullHom (q : SelectedSource V I) : q.ProjectionFullHomType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  exact fun X Y k l => (q.projection X Y).uncurriedNaturality k l

/-- Every selected generator balances over the entire original product-enriched Hom. -/
def CoendBalancedType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y : q.Module) (k : I),
      EnrichedDayKernel.Balanced q.monoidalData.tensorEnrichedFunctor
        X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k (q.coendGenerator X Y k)

/-- The original full Day universal property preserves all generator balancing relations. -/
theorem coendGenerators_balanced (q : SelectedSource V I) : q.CoendBalancedType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  intro X Y k
  exact ((EnrichedDayKernel.homEquiv q.monoidalData.tensorEnrichedFunctor
    X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k ((X ⊗ Y).X.toEnrichedFunctor.obj k))
      (EnrichedFunctorCat.component (q.projection X Y) k)).property

/-- The complete original coefficient map equation of the selected coend generators. -/
def CoendGeneratorMapType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ {X X' Y Y' : q.Module} (f : X ⟶ X') (g : Y ⟶ Y') (k : I) (a : I × I),
      q.coendGenerator X Y k a ≫ EnrichedFunctorCat.component (f ⊗ₘ g).hom k =
        (𝟙 (q.monoidalData.tensorEnrichedFunctor.obj a ⟶[V] k) ⊗ₘ
          (EnrichedFunctorCat.component f.hom a.1 ⊗ₘ
            EnrichedFunctorCat.component g.hom a.2)) ≫
          q.coendGenerator X' Y' k a

/-- The original quotient map law and the entire Day input map law supply the equation. -/
theorem coendGenerator_map (q : SelectedSource V I) : q.CoendGeneratorMapType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  intro X X' Y Y' f g k a
  have h := congrArg (fun p => EnrichedFunctorCat.component p k)
    (q.projectionMap f g)
  rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp] at h
  have ht := EnrichedDayKernel.ColimitMonoidal.tensorHom_eq q.monoidalData f.hom g.hom
  have hc := congrArg (fun p => EnrichedFunctorCat.component p k) ht
  have hm := EnrichedDayKernel.Input.bifunctor_map_component
    q.monoidalData.tensorEnrichedFunctor f.hom g.hom k
  have hg := EnrichedDayKernel.Input.gen_mapAt
    q.monoidalData.tensorEnrichedFunctor f.hom g.hom k a
  let sourceGen := EnrichedDayKernel.gen q.monoidalData.tensorEnrichedFunctor
    X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a
  have hg' := (congrArg (fun p => sourceGen ≫ p) (hc.trans hm)).trans hg
  have h' := congrArg (fun p => sourceGen ≫ p) h
  have ha := Category.assoc sourceGen (EnrichedFunctorCat.component (f.hom ⊗ₘ g.hom) k)
    (EnrichedFunctorCat.component (q.projection X' Y') k)
  have h'' := h'.trans (ha.symm.trans
    (congrArg (fun p => p ≫ EnrichedFunctorCat.component (q.projection X' Y') k) hg'))
  have ha' := Category.assoc
    (𝟙 (q.monoidalData.tensorEnrichedFunctor.obj a ⟶[V] k) ⊗ₘ
      (EnrichedFunctorCat.component f.hom a.1 ⊗ₘ EnrichedFunctorCat.component g.hom a.2))
    (EnrichedDayKernel.gen q.monoidalData.tensorEnrichedFunctor X'.X.toEnrichedFunctor
      Y'.X.toEnrichedFunctor k a)
    (EnrichedFunctorCat.component (q.projection X' Y') k)
  have ha₀ := Category.assoc sourceGen
    (EnrichedFunctorCat.component (q.projection X Y) k)
    (EnrichedFunctorCat.component (f ⊗ₘ g).hom k)
  exact (congrArg (fun p => p ≫ EnrichedFunctorCat.component (f ⊗ₘ g).hom k)
    (q.coendGenerator_formula X Y k a)).trans ((ha₀.trans (h''.trans ha')).trans
      (congrArg (fun p =>
        (𝟙 (q.monoidalData.tensorEnrichedFunctor.obj a ⟶[V] k) ⊗ₘ
          (EnrichedFunctorCat.component f.hom a.1 ⊗ₘ
            EnrichedFunctorCat.component g.hom a.2)) ≫ p)
        (q.coendGenerator_formula X' Y' k a).symm))

/-- Each entire original coend integrand is retained by the inverse balanced Hom function. -/
def GeneratorHomEquivSymmType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y Z : q.Module) (f : RightModuleFree.BalancedRightLinearMap q.coefficient X Y Z)
      (k : I) (a : I × I),
      q.coendGenerator X Y k a ≫
          EnrichedFunctorCat.component ((q.homEquiv X Y Z).symm f).hom k =
        EnrichedDayKernel.gen q.monoidalData.tensorEnrichedFunctor
          X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a ≫ EnrichedFunctorCat.component f.hom k

/-- The original quotient descent equation is preserved on every complete integrand. -/
theorem generator_homEquiv_symm (q : SelectedSource V I) : q.GeneratorHomEquivSymmType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  intro X Y Z f k a
  have h := congrArg (fun p => EnrichedFunctorCat.component p k)
    (q.projection_homEquiv_symm X Y Z f)
  rw [EnrichedFunctorCat.component_comp] at h
  exact (congrArg (fun p => p ≫
    EnrichedFunctorCat.component ((q.homEquiv X Y Z).symm f).hom k)
      (q.coendGenerator_formula X Y k a)).trans
    ((Category.assoc
      (EnrichedDayKernel.gen q.monoidalData.tensorEnrichedFunctor
        X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a)
      (EnrichedFunctorCat.component (q.projection X Y) k)
      (EnrichedFunctorCat.component ((q.homEquiv X Y Z).symm f).hom k)).trans
      (congrArg (fun p => EnrichedDayKernel.gen q.monoidalData.tensorEnrichedFunctor
        X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k a ≫ p) h))

/-- Actual selected tensor arrows are determined by all original coend-integrand values. -/
def HomExtType (q : SelectedSource V I) : Prop :=
    letI := q.dayMonoidal
    letI := q.daySymmetric
    letI := q.dayClosed
    letI := q.coefficientMonObj
    letI := q.coefficientIsComm
    letI := q.moduleMonoidal
    ∀ (X Y Z : q.Module) (f g : X ⊗ Y ⟶ Z)
      (_h : ∀ (k : I) (a : I × I),
        q.coendGenerator X Y k a ≫ EnrichedFunctorCat.component f.hom k =
          q.coendGenerator X Y k a ≫ EnrichedFunctorCat.component g.hom k), f = g

/-- The original quotient epimorphism and complete Day generators supply tensor extensionality. -/
theorem hom_ext (q : SelectedSource V I) : q.HomExtType := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.moduleMonoidal
  intro X Y Z f g h
  let : Epi (q.projection X Y) := q.projectionEpi X Y
  apply Mod.hom_ext
  apply (cancel_epi (q.projection X Y)).mp
  apply EnrichedFunctorCat.hom_ext
  intro k
  rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp]
  apply EnrichedDayKernel.hom_ext q.monoidalData.tensorEnrichedFunctor
    X.X.toEnrichedFunctor Y.X.toEnrichedFunctor k
  intro a
  have hc := h k a
  rw [q.coendGenerator_formula X Y k a] at hc
  simpa only [Category.assoc] using hc

end CategoryTheory.Enriched.ModuleMappingR.SelectedSource
