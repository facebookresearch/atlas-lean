/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalLocalizedCarrier
import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence

/-!
# Original I/K factor records on the computed orthogonal localization

Both entire original factor algorithms pass through the same actual
native/tagged identity equivalence. Their middle functors, every Arrow
map, all four natural factor legs and factor equations retain the original
values. The full model class laws classify those same records as the two
localized model factorizations.

The original realized cardinal and caller's ordinal bottom are the ones
in the original records. The exact original comparison proposition is
used only to construct the localization and classify its intersections.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalLocalizedFactors

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

variable (hComparison : ComparisonHomBijections.{u, v} (B := B))

/-- The entire original I record is transported through the actual identity equivalence. -/
def givenI : FunctorialFactorizationData
    (stableCofibrations.inverseImage (ConditionalLocalizedCarrier.toNative hComparison))
    (originalI.rlp.inverseImage (ConditionalLocalizedCarrier.toNative hComparison)) :=
  originalIFactorizationData.ofEquivalence
    (ConditionalLocalizedCarrier.equivalence hComparison).symm

/-- The same complete original paired K record keeps all source Arrow and factor maps. -/
def givenK : FunctorialFactorizationData
    (originalK.rlp.llp.inverseImage (ConditionalLocalizedCarrier.toNative hComparison))
    (stableFibrations.inverseImage (ConditionalLocalizedCarrier.toNative hComparison)) :=
  originalKFactorizationData.ofEquivalence
    (ConditionalLocalizedCarrier.equivalence hComparison).symm

/-- The full localized ordinary/trivial-right factor is the same transported original I record. -/
def IFactorizationData : FunctorialFactorizationData
    (cofibrations (ConditionalLocalization.Carrier hComparison))
    (trivialFibrations (ConditionalLocalization.Carrier hComparison)) where
  Z := (givenI hComparison).Z
  i := (givenI hComparison).i
  p := (givenI hComparison).p
  fac := (givenI hComparison).fac
  hi F := by
    rw [ConditionalLocalizedCarrier.cofibrations_eq hComparison]
    exact (givenI hComparison).hi F
  hp F := by
    rw [ConditionalLocalizedCarrier.trivialFibrations_eq hComparison]
    exact (givenI hComparison).hp F

/-- The full localized trivial-left/fibration factor is the same original paired K record. -/
def KFactorizationData : FunctorialFactorizationData
    (trivialCofibrations (ConditionalLocalization.Carrier hComparison))
    (fibrations (ConditionalLocalization.Carrier hComparison)) where
  Z := (givenK hComparison).Z
  i := (givenK hComparison).i
  p := (givenK hComparison).p
  fac := (givenK hComparison).fac
  hi F := by
    rw [ConditionalLocalizedCarrier.trivialCofibrations_eq hComparison]
    exact (givenK hComparison).hi F
  hp F := by
    rw [ConditionalLocalizedCarrier.fibrations_eq hComparison]
    exact (givenK hComparison).hp F

/-- Classifying both records preserves every original middle functor and natural leg. -/
theorem given_fields :
    (IFactorizationData hComparison).Z = (givenI hComparison).Z ∧
      (IFactorizationData hComparison).i = (givenI hComparison).i ∧
      (IFactorizationData hComparison).p = (givenI hComparison).p ∧
      (KFactorizationData hComparison).Z = (givenK hComparison).Z ∧
      (KFactorizationData hComparison).i = (givenK hComparison).i ∧
      (KFactorizationData hComparison).p = (givenK hComparison).p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Both entire middle functors retain the original cardinal-shaped native algorithms. -/
theorem original_middle :
    (IFactorizationData hComparison).Z =
        (ConditionalLocalizedCarrier.toNative hComparison).mapArrow ⋙
          originalIFactorizationData.Z ⋙ ConditionalLocalizedCarrier.ofNative hComparison ∧
      (KFactorizationData hComparison).Z =
        (ConditionalLocalizedCarrier.toNative hComparison).mapArrow ⋙
          originalKFactorizationData.Z ⋙ ConditionalLocalizedCarrier.ofNative hComparison :=
  ⟨rfl, rfl⟩

/-- Every complete input Arrow square retains both entire original middle maps. -/
theorem original_maps
    {F G : CategoryTheory.Arrow (ConditionalLocalization.Carrier hComparison)} (f : F ⟶ G) :
    (ConditionalLocalizedCarrier.toNative hComparison).map
        ((IFactorizationData hComparison).Z.map f) =
      originalIFactorizationData.Z.map
        ((ConditionalLocalizedCarrier.toNative hComparison).mapArrow.map f) ∧
      (ConditionalLocalizedCarrier.toNative hComparison).map
          ((KFactorizationData hComparison).Z.map f) =
        originalKFactorizationData.Z.map
          ((ConditionalLocalizedCarrier.toNative hComparison).mapArrow.map f) := ⟨rfl, rfl⟩

/-- Both full original left factor functions survive the actual inverse-unit comparisons. -/
theorem original_left_legs
    (F : CategoryTheory.Arrow (ConditionalLocalization.Carrier hComparison)) :
    (ConditionalLocalizedCarrier.toNative hComparison).map
        ((IFactorizationData hComparison).i.app F) =
      originalIFactorizationData.i.app
        ((ConditionalLocalizedCarrier.toNative hComparison).mapArrow.obj F) ∧
      (ConditionalLocalizedCarrier.toNative hComparison).map
          ((KFactorizationData hComparison).i.app F) =
        originalKFactorizationData.i.app
          ((ConditionalLocalizedCarrier.toNative hComparison).mapArrow.obj F) := by
  constructor
  · let e := (ConditionalLocalizedCarrier.equivalence hComparison).symm
    have h := originalIFactorizationData.ofEquivalence_mapped_i e F
    have he : (originalIFactorizationData.ofEquivalenceZComparisonIso e).hom.app F =
        𝟙 _ := rfl
    have h' := (congrArg
      (fun q => e.functor.map ((originalIFactorizationData.ofEquivalence e).i.app F) ≫ q)
      he).symm.trans h
    exact (Category.comp_id _).symm.trans h'
  · let e := (ConditionalLocalizedCarrier.equivalence hComparison).symm
    have h := originalKFactorizationData.ofEquivalence_mapped_i e F
    have he : (originalKFactorizationData.ofEquivalenceZComparisonIso e).hom.app F =
        𝟙 _ := rfl
    have h' := (congrArg
      (fun q => e.functor.map ((originalKFactorizationData.ofEquivalence e).i.app F) ≫ q)
      he).symm.trans h
    exact (Category.comp_id _).symm.trans h'

/-- Both full original right factor functions survive the actual forward-unit comparisons. -/
theorem original_right_legs
    (F : CategoryTheory.Arrow (ConditionalLocalization.Carrier hComparison)) :
    (ConditionalLocalizedCarrier.toNative hComparison).map
        ((IFactorizationData hComparison).p.app F) =
      originalIFactorizationData.p.app
        ((ConditionalLocalizedCarrier.toNative hComparison).mapArrow.obj F) ∧
      (ConditionalLocalizedCarrier.toNative hComparison).map
          ((KFactorizationData hComparison).p.app F) =
        originalKFactorizationData.p.app
          ((ConditionalLocalizedCarrier.toNative hComparison).mapArrow.obj F) := by
  constructor
  · let e := (ConditionalLocalizedCarrier.equivalence hComparison).symm
    have h := originalIFactorizationData.ofEquivalence_mapped_p e F
    have he : (originalIFactorizationData.ofEquivalenceZComparisonIso e).hom.app F =
        𝟙 _ := rfl
    have h' := (congrArg
      (fun q => q ≫ originalIFactorizationData.p.app (e.functor.mapArrow.obj F))
      he).symm.trans h
    exact h'.symm.trans (Category.id_comp _)
  · let e := (ConditionalLocalizedCarrier.equivalence hComparison).symm
    have h := originalKFactorizationData.ofEquivalence_mapped_p e F
    have he : (originalKFactorizationData.ofEquivalenceZComparisonIso e).hom.app F =
        𝟙 _ := rfl
    have h' := (congrArg
      (fun q => q ≫ originalKFactorizationData.p.app (e.functor.mapArrow.obj F))
      he).symm.trans h
    exact h'.symm.trans (Category.id_comp _)

/-- Both actual original algorithms factor every complete localized input Arrow. -/
theorem factorization_fac
    (F : CategoryTheory.Arrow (ConditionalLocalization.Carrier hComparison)) :
    (IFactorizationData hComparison).i.app F ≫ (IFactorizationData hComparison).p.app F =
        F.hom ∧
      (KFactorizationData hComparison).i.app F ≫ (KFactorizationData hComparison).p.app F =
        F.hom :=
  ⟨(IFactorizationData hComparison).fac_app, (KFactorizationData hComparison).fac_app⟩

/-- Every full original input square retains all four factor naturality equations. -/
theorem factorization_naturality
    {F G : CategoryTheory.Arrow (ConditionalLocalization.Carrier hComparison)} (f : F ⟶ G) :
    f.left ≫ (IFactorizationData hComparison).i.app G =
        (IFactorizationData hComparison).i.app F ≫ (IFactorizationData hComparison).Z.map f ∧
      (IFactorizationData hComparison).Z.map f ≫ (IFactorizationData hComparison).p.app G =
        (IFactorizationData hComparison).p.app F ≫ f.right ∧
      f.left ≫ (KFactorizationData hComparison).i.app G =
        (KFactorizationData hComparison).i.app F ≫ (KFactorizationData hComparison).Z.map f ∧
      (KFactorizationData hComparison).Z.map f ≫ (KFactorizationData hComparison).p.app G =
        (KFactorizationData hComparison).p.app F ≫ f.right :=
  ⟨(IFactorizationData hComparison).i.naturality f,
    (IFactorizationData hComparison).p.naturality f,
    (KFactorizationData hComparison).i.naturality f,
    (KFactorizationData hComparison).p.naturality f⟩

/-- Both complete original records give their actual full localized model class memberships. -/
theorem factorization_membership
    (F : CategoryTheory.Arrow (ConditionalLocalization.Carrier hComparison)) :
    cofibrations (ConditionalLocalization.Carrier hComparison)
        ((IFactorizationData hComparison).i.app F) ∧
      trivialFibrations (ConditionalLocalization.Carrier hComparison)
        ((IFactorizationData hComparison).p.app F) ∧
      trivialCofibrations (ConditionalLocalization.Carrier hComparison)
        ((KFactorizationData hComparison).i.app F) ∧
      fibrations (ConditionalLocalization.Carrier hComparison)
        ((KFactorizationData hComparison).p.app F) :=
  ⟨(IFactorizationData hComparison).hi F, (IFactorizationData hComparison).hp F,
    (KFactorizationData hComparison).hi F, (KFactorizationData hComparison).hp F⟩

end PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalLocalizedFactors
