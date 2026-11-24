/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRFree

/-!
# Actual noncommutative free-source end clients

The entire original generator, arbitrary source arrow, and every genuine
V-parameter family are retained at the literal right-translation index.
These clients do not assume that the coefficient monoid is commutative.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingRFreeTests

open EnrichedFunctorCat EnrichedDayKernel ModuleMappingR

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- The original source free mapping value is the actual full translated weighted end. -/
def originalFreeEnd (F : EnrichedFunctorCat V I) (N : Module d S L) (c : I) :
    value d b S L (freeModule d S L F) N c ≅
      WeightedEndVariance.object F (Closed.translatedTarget d
        (SphereModuleMappingEnd.diagram d S L N) c) :=
  freeSourceValueIso d b S L F N c

/-- The complete actual free-source forward map retains the original generator at every j. -/
theorem generator_projection (F : EnrichedFunctorCat V I) (N : Module d S L) (c j : I) :
    (originalFreeEnd d b S L F N c).hom ≫
        Closed.π d F (SphereModuleMappingEnd.diagram d S L N) c j =
      π d b S L (freeModule d S L F) N c j ≫
        (MonoidalClosed.pre (component (freeUnit d S L F) j)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) :=
  freeSourceValueIso_hom_π d b S L F N c j

/-- Every complete original source arrow is retained through the actual original free unit. -/
theorem whole_source_arrow {F F' : EnrichedFunctorCat V I}
    (f : freeModule d S L F' ⟶ freeModule d S L F) (N : Module d S L) :
    pre d b S L f N ≫ (freeSourceIso d b S L F' N).hom =
      ι d b S L (freeModule d S L F) N ≫
        Closed.pre d (freeUnit d S L F' ≫ SphereModuleMappingEnd.moduleMap d S L f)
          (SphereModuleMappingEnd.diagram d S L N) :=
  freeSourceIso_sourceArrow d b S L f N

/-- Every actual enriched parameter Hom is retained by the full original free-source iso. -/
theorem parameter_Hom (F : EnrichedFunctorCat V I) (N : Module d S L) (c c' : I) :
    parameterAction d b S L (freeModule d S L F) N c c' ≫
        component (freeSourceIso d b S L F N).hom c' =
      (component (freeSourceIso d b S L F N).hom c ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        MonoidalClosed.uncurry
          ((Closed.rightObject d F (SphereModuleMappingEnd.diagram d S L N)).toEnrichedFunctor.map
            c c') :=
  freeSourceIso_parameter d b S L F N c c'

/-- The entire V-parameter map is recovered after forming its original translated family. -/
theorem value_parameter_roundtrip (F : EnrichedFunctorCat V I) (N : Module d S L)
    (c : I) (P : V) (f : P ⟶ value d b S L (freeModule d S L F) N c) :
    (freeValueParameterEquiv d b S L F N c P).symm
      (freeValueParameterEquiv d b S L F N c P f) = f :=
  (freeValueParameterEquiv d b S L F N c P).left_inv f

/-- Every whole genuine translated V-family is recovered by both original maps. -/
theorem value_family_roundtrip (F : EnrichedFunctorCat V I) (N : Module d S L)
    (c : I) (P : V) (t : GradedNatTrans ((Center.ofBraided V).obj P) F.toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor) :
    freeValueParameterEquiv d b S L F N c P
      ((freeValueParameterEquiv d b S L F N c P).symm t) = t :=
  (freeValueParameterEquiv d b S L F N c P).right_inv t

/-- Every original ambient coefficient arrow commutes with the full free-source value family. -/
theorem coefficient_arrow (F : EnrichedFunctorCat V I) (N : Module d S L) (c : I)
    {P Q : V} (r : P ⟶ Q) (f : Q ⟶ value d b S L (freeModule d S L F) N c) :
    freeValueParameterEquiv d b S L F N c P (r ≫ f) =
      GradedNatTrans.regrade ((Center.ofBraided V).map r)
        (freeValueParameterEquiv d b S L F N c Q f) :=
  freeValueParameterEquiv_regrade d b S L F N c r f

end CategoryTheory.Enriched.ModuleMappingRFreeTests
