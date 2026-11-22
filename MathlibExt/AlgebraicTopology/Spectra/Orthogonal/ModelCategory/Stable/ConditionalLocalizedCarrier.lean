/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalLocalization

/-!
# The computed orthogonal localization and the same conditional native model

The family-keyed localization carrier comes from the proved conditional
localization data for the entire original orthogonal stabilization family.
The original identity functions give a categorical equivalence with the
unchanged native carrier. All five model classes are the same original
I/K and Omega-test properties on every underlying native map.

The identity from the original level model is Quillen. With the existing
conditional native stable model value, the same categorical equivalence
is a Quillen equivalence. Both statements retain the exact original
comparison proposition, and no unconditional native model is installed.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalLocalizedCarrier

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf

private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

variable (hComparison : ComparisonHomBijections.{u, v} (B := B))

/-- The same native object and full native map acquire their actual localization tag. -/
def ofNative : C.{u, v} ⥤ ConditionalLocalization.Carrier hComparison :=
  LeftLocalized.ofBase (ConditionalLocalization.data hComparison)

/-- Forgetting the proved family tag retains the entire original native object and map. -/
def toNative : ConditionalLocalization.Carrier hComparison ⥤ C.{u, v} :=
  LeftLocalized.toBase (ConditionalLocalization.data hComparison)

/-- Both complete original identity functors supply this same categorical equivalence. -/
def equivalence : C.{u, v} ≌ ConditionalLocalization.Carrier hComparison :=
  LeftLocalized.equivalence (ConditionalLocalization.data hComparison)

/-- The forward functor is the unchanged full native identity with its family tag. -/
theorem equivalence_functor : (equivalence hComparison).functor = ofNative hComparison := rfl

/-- The inverse functor is the same original full native forgetful identity. -/
theorem equivalence_inverse : (equivalence hComparison).inverse = toNative hComparison := rfl

/-- Every original native source and target object survives the whole forward round trip. -/
theorem ofNative_comp_toNative :
    ofNative hComparison ⋙ toNative hComparison = 𝟭 C.{u, v} := rfl

/-- Every family-tagged object and arrow survives the complete inverse round trip. -/
theorem toNative_comp_ofNative :
    toNative hComparison ⋙ ofNative hComparison =
      𝟭 (ConditionalLocalization.Carrier hComparison) := rfl

/-- Every original native object is the literal same object after forgetting its tag. -/
theorem ofNative_obj (X : C.{u, v}) :
    (toNative hComparison).obj ((ofNative hComparison).obj X) = X := rfl

/-- Every original native arrow retains its entire original enriched transformation. -/
theorem ofNative_map {X Y : C.{u, v}} (f : X ⟶ Y) :
    (toNative hComparison).map ((ofNative hComparison).map f) = f := rfl

/-- Every localized original arrow retains its whole native map in the inverse round trip. -/
theorem toNative_map {X Y : ConditionalLocalization.Carrier hComparison} (f : X ⟶ Y) :
    (ofNative hComparison).map ((toNative hComparison).map f) = f := rfl

/-- The original forward unit is the identity of every full native object. -/
theorem unit_hom (X : C.{u, v}) :
    (equivalence hComparison).unitIso.hom.app X = 𝟙 X := rfl

/-- The original inverse unit is the same full native identity map. -/
theorem unit_inv (X : C.{u, v}) :
    (equivalence hComparison).unitIso.inv.app X = 𝟙 X := rfl

/-- The forward counit retains the identity on every original native level and label. -/
theorem counit_hom (X : ConditionalLocalization.Carrier hComparison) :
    (toNative hComparison).map ((equivalence hComparison).counitIso.hom.app X) =
      𝟙 ((toNative hComparison).obj X) := rfl

/-- The inverse counit retains that same entire original identity transformation. -/
theorem counit_inv (X : ConditionalLocalization.Carrier hComparison) :
    (toNative hComparison).map ((equivalence hComparison).counitIso.inv.app X) =
      𝟙 ((toNative hComparison).obj X) := rfl

/-- The complete forward Hom function is the same original native map. -/
theorem homEquiv (X : C.{u, v}) (Y : ConditionalLocalization.Carrier hComparison)
    (f : (ofNative hComparison).obj X ⟶ Y) :
    (equivalence hComparison).toAdjunction.homEquiv X Y f =
      (toNative hComparison).map f := by
  change 𝟙 X ≫ (toNative hComparison).map f = _
  exact Category.id_comp _

/-- The complete inverse Hom function is the original native map with its actual tag. -/
theorem homEquiv_symm (X : C.{u, v}) (Y : ConditionalLocalization.Carrier hComparison)
    (f : X ⟶ (toNative hComparison).obj Y) :
    ((equivalence hComparison).toAdjunction.homEquiv X Y).symm f =
      (ofNative hComparison).map f := by
  change (ofNative hComparison).map f ≫ 𝟙 Y = _
  exact Category.comp_id _

/-- Its weak class is the entire original native Omega test property after forgetting the tag. -/
theorem weakEquivalences_eq :
    weakEquivalences (ConditionalLocalization.Carrier hComparison) =
      stableWeakEquivalences.inverseImage (toNative hComparison) := by
  change (localEquivalences ConditionalLocalization.originalArrows).inverseImage
      (toNative hComparison) = _
  rw [ConditionalLocalization.localEquivalences_eq]

/-- Its cofibrations are exactly the same full original I-left property on native maps. -/
theorem cofibrations_eq :
    cofibrations (ConditionalLocalization.Carrier hComparison) =
      stableCofibrations.inverseImage (toNative hComparison) := by
  change (cofibrations C.{u, v}).inverseImage (toNative hComparison) = _
  rw [← stableCofibrations_eq_level]

/-- Its fibrations are exactly the complete original paired K-right property. -/
theorem fibrations_eq :
    fibrations (ConditionalLocalization.Carrier hComparison) =
      stableFibrations.inverseImage (toNative hComparison) := by
  change (localizedFibrations ConditionalLocalization.originalArrows).inverseImage
      (toNative hComparison) = _
  rw [ConditionalLocalization.localizedFibrations_eq hComparison]

/-- Its trivial cofibrations retain the entire actual original paired K-left class. -/
theorem trivialCofibrations_eq :
    trivialCofibrations (ConditionalLocalization.Carrier hComparison) =
      originalK.rlp.llp.inverseImage (toNative hComparison) := by
  change (cofibrations C.{u, v} ⊓
      localEquivalences ConditionalLocalization.originalArrows).inverseImage
        (toNative hComparison) = _
  rw [ConditionalLocalization.localTrivialCofibrations_eq,
    ← ConditionalRecognition.left_class_eq hComparison]

/-- Its trivial fibrations are exactly the same original full I-right class. -/
theorem trivialFibrations_eq :
    trivialFibrations (ConditionalLocalization.Carrier hComparison) =
      originalI.rlp.inverseImage (toNative hComparison) := by
  change (localizedFibrations ConditionalLocalization.originalArrows ⊓
      localEquivalences ConditionalLocalization.originalArrows).inverseImage
        (toNative hComparison) = _
  rw [ConditionalLocalization.localizedTrivialFibrations_eq hComparison,
    ← HomotopicalAlgebra.EnrichedProjective.Native.Data.generatorsI_rlp]

/-- All five actual classes belong to this same computed original localization value. -/
theorem five_classes :
    weakEquivalences (ConditionalLocalization.Carrier hComparison) =
        stableWeakEquivalences.inverseImage (toNative hComparison) ∧
      cofibrations (ConditionalLocalization.Carrier hComparison) =
        stableCofibrations.inverseImage (toNative hComparison) ∧
      fibrations (ConditionalLocalization.Carrier hComparison) =
        stableFibrations.inverseImage (toNative hComparison) ∧
      trivialCofibrations (ConditionalLocalization.Carrier hComparison) =
        originalK.rlp.llp.inverseImage (toNative hComparison) ∧
      trivialFibrations (ConditionalLocalization.Carrier hComparison) =
        originalI.rlp.inverseImage (toNative hComparison) :=
  ⟨weakEquivalences_eq hComparison, cofibrations_eq hComparison,
    fibrations_eq hComparison, trivialCofibrations_eq hComparison,
    trivialFibrations_eq hComparison⟩

/-- Every full localized native map has exactly its unchanged original Omega Hom tests. -/
theorem weak_iff {X Y : ConditionalLocalization.Carrier hComparison} (f : X ⟶ Y) :
    weakEquivalences (ConditionalLocalization.Carrier hComparison) f ↔
      stableWeakEquivalences ((toNative hComparison).map f) := by
  rw [weakEquivalences_eq hComparison]
  rfl

/-- Every full localized native map has the same original ordinary cofibration property. -/
theorem cofibration_iff {X Y : ConditionalLocalization.Carrier hComparison} (f : X ⟶ Y) :
    cofibrations (ConditionalLocalization.Carrier hComparison) f ↔
      stableCofibrations ((toNative hComparison).map f) := by
  rw [cofibrations_eq hComparison]
  rfl

/-- Every full localized native fibration retains all original paired right lifting tests. -/
theorem fibration_iff {X Y : ConditionalLocalization.Carrier hComparison} (f : X ⟶ Y) :
    fibrations (ConditionalLocalization.Carrier hComparison) f ↔
      stableFibrations ((toNative hComparison).map f) := by
  rw [fibrations_eq hComparison]
  rfl

/-- Every full localized trivial cofibration is the actual original K-left map. -/
theorem trivialCofibration_iff
    {X Y : ConditionalLocalization.Carrier hComparison} (f : X ⟶ Y) :
    trivialCofibrations (ConditionalLocalization.Carrier hComparison) f ↔
      originalK.rlp.llp ((toNative hComparison).map f) := by
  rw [trivialCofibrations_eq hComparison]
  rfl

/-- Every localized trivial fibration retains exactly the original I-right lifting class. -/
theorem trivialFibration_iff
    {X Y : ConditionalLocalization.Carrier hComparison} (f : X ⟶ Y) :
    trivialFibrations (ConditionalLocalization.Carrier hComparison) f ↔
      originalI.rlp ((toNative hComparison).map f) := by
  rw [trivialFibrations_eq hComparison]
  rfl

/-- Fibrancy is exactly the complete original Omega structure on the same native object. -/
theorem isFibrant_iff_isOmega (X : ConditionalLocalization.Carrier hComparison) :
    IsFibrant X ↔ NativeK.IsOmega orthogonalFamily ((toNative hComparison).obj X) :=
  (LeftLocalized.fibrant_iff (ConditionalLocalization.data hComparison) X).trans
    (DerivedLocalMapping.isLocalFibrant_iff_isOmega orthogonalFamily X.1)

/-- The original level-to-localized identity is the actual Quillen adjunction. -/
theorem level_isQuillen : (equivalence hComparison).toAdjunction.IsQuillenAdjunction :=
  LeftLocalized.ofBase_isLeftQuillen (ConditionalLocalization.data hComparison)

/-- The same identity equivalence is Quillen for the existing conditional native stable value. -/
theorem stable_isQuillen :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    (equivalence hComparison).toAdjunction.IsQuillenAdjunction := by
  let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
  exact
    { preservesCofibrations := by
        intro X Y f hf
        change stableCofibrations f at hf
        exact (cofibration_iff hComparison ((ofNative hComparison).map f)).mpr hf
      preservesTrivialCofibrations := by
        intro X Y f hf
        change stableTrivialCofibrations f at hf
        apply (trivialCofibration_iff hComparison ((ofNative hComparison).map f)).mpr
        exact (ConditionalRecognition.left_class_eq hComparison).symm ▸ hf }

/-- Both actual native model presentations have the same full weak class on every Hom adjunct. -/
theorem stable_isQuillenEquivalence :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    (equivalence hComparison).toAdjunction.IsQuillenEquivalence := by
  let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
  refine
    { toIsQuillenAdjunction := stable_isQuillen hComparison
      homEquiv_weakEquivalence_iff := ?_ }
  intro X Y _ _ f
  rw [weak_iff hComparison]
  change stableWeakEquivalences ((toNative hComparison).map f) ↔
    stableWeakEquivalences ((equivalence hComparison).toAdjunction.homEquiv X Y f)
  have h := homEquiv hComparison X Y f
  exact ⟨fun hf => h.symm ▸ hf, fun hf => h ▸ hf⟩

end PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalLocalizedCarrier
