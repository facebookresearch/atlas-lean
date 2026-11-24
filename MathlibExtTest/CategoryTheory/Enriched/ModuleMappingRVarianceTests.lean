/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRVariance

/-!
# Whole-arrow clients of the raw translated mapping bifunctor

Every source and target arrow is a complete original right-module morphism.
The tested projections retain `j tensor c`, and every parameter Hom acts on
the genuine entire source equalizer. There is no braided-coefficient or
commutative-monoid premise.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingRVarianceTests

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

/-- The full raw mapping bifunctor has the original action equalizer at every module pair. -/
example (M N : Module d S L) :
    ((diagramBifunctor d b S L).obj (Opposite.op M)).obj N = diagram d b S L M N := rfl

/-- Every source transformation retains its full original source carrier component. -/
theorem source_projection {M M' : Module d S L} (f : M' ⟶ M) (N : Module d S L)
    (c j : I) :
    component ((diagramSourceMap d b S L f).app N) c ≫ π d b S L M' N c j =
      π d b S L M N c j ≫
        (MonoidalClosed.pre (component (SphereModuleMappingEnd.moduleMap d S L f) j)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) :=
  pre_π d b S L f N c j

/-- Every complete target arrow acts at exactly the original right-translation index. -/
theorem target_projection (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N')
    (c j : I) :
    component ((diagramFunctor d b S L M).map g) c ≫ π d b S L M N' c j =
      π d b S L M N c j ≫
        (ihom ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)).map
          (component (SphereModuleMappingEnd.moduleMap d S L g) (j ⊗ c)) :=
  post_π d b S L M g c j

/-- Both complete original variances commute on the whole raw end diagram. -/
theorem full_arrow_square {M M' N N' : Module d S L} (f : M' ⟶ M) (g : N ⟶ N') :
    pre d b S L f N ≫ post d b S L M' g = post d b S L M g ≫ pre d b S L f N' :=
  pre_post d b S L f g

/-- Every full source arrow intertwines every original enriched parameter Hom. -/
theorem source_parameter_Hom {M M' : Module d S L} (f : M' ⟶ M) (N : Module d S L)
    (c c' : I) :
    parameterAction d b S L M N c c' ≫ component (pre d b S L f N) c' =
      (component (pre d b S L f N) c ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        parameterAction d b S L M' N c c' :=
  (pre d b S L f N).uncurriedNaturality c c'

/-- Every full target arrow intertwines every original enriched parameter Hom. -/
theorem target_parameter_Hom (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N')
    (c c' : I) :
    parameterAction d b S L M N c c' ≫ component (post d b S L M g) c' =
      (component (post d b S L M g) c ⊗ₘ 𝟙 (c ⟶[V] c')) ≫
        parameterAction d b S L M N' c c' :=
  (post d b S L M g).uncurriedNaturality c c'

/-- The actual source map retains the whole original contravariant composition order. -/
theorem source_order {M M' M'' : Module d S L} (f : M' ⟶ M) (g : M'' ⟶ M')
    (N : Module d S L) : pre d b S L (g ≫ f) N = pre d b S L f N ≫ pre d b S L g N :=
  pre_comp d b S L f g N

end CategoryTheory.Enriched.ModuleMappingRVarianceTests
