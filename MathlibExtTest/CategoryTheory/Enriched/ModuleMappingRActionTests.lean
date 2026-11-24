/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAction

/-!
# Actual translated equalizer module and balanced adjunction clients

Braided lax coefficient data supplies commutativity of the actual Day monoid.
The original equalizer carrier and source relative tensor order are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingRActionTests

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
  (B : EnrichedFunctor.LaxBraidedData L)

/-- The original right mapping module has the literal full translated action equalizer carrier. -/
example (M N : Module d S L) :
    SphereModuleMappingEnd.diagram d S L (moduleObject d b S L B M N) =
      diagram d b S L M N := moduleObject_diagram d b S L B M N

/-- Every complete target arrow retains the original whole raw equalizer map. -/
theorem original_target_arrow (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') :
    SphereModuleMappingEnd.moduleMap d S L ((functor d b S L B M).map g) =
      post d b S L M g := functor_map d b S L B M g

/-- Actual source-module arrows preserve the original translated projections in every degree. -/
@[reassoc]
theorem original_source_projection {M M' : Module d S L} (f : M' ⟶ M) (N : Module d S L)
    (c j : I) :
    component (SphereModuleMappingEnd.moduleMap d S L
        (moduleSourceMap d b S L B f N)) c ≫ π d b S L M' N c j =
      π d b S L M N c j ≫
        (MonoidalClosed.pre (component (SphereModuleMappingEnd.moduleMap d S L f) j)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c)) :=
  moduleSourceMap_π d b S L B f N c j

/-- The source and target arrow square holds on the whole original mapping module. -/
theorem original_variance_square {M M' N N' : Module d S L} (f : M' ⟶ M) (g : N ⟶ N') :
    (functor d b S L B M).map g ≫ moduleSourceMap d b S L B f N' =
      moduleSourceMap d b S L B f N ≫ (functor d b S L B M').map g :=
  moduleSourceMap_naturality d b S L B f g

/-- Every whole coefficient parameter retains the original inherited output action,
end evaluation, target right action and index associator. -/
theorem original_output_projection_parameter (M N : Module d S L) (c a j : I) {P : V}
    (q : P ⟶ value d b S L M N c) :
    MonoidalClosed.uncurry
      ((q ⊗ₘ 𝟙 (S.obj a)) ≫ moduleSigma d b S L B M N c a ≫
        π d b S L M N (c ⊗ a) j) =
    (α_ ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
      P (S.obj a)).inv ≫
      (MonoidalClosed.uncurry (q ≫ π d b S L M N c j) ▷ S.obj a) ≫
      ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
        (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a ≫
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
        (α_ j c a).hom := by
  let X := (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j
  let tail := ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
    (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a ≫
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
      (α_ j c a).hom
  rw [MonoidalClosed.uncurry_natural_left, moduleSigma_π, tensorHom_id]
  calc
    _ = (α_ X P (S.obj a)).inv ≫ ((X ◁ q) ▷ S.obj a) ≫
        (MonoidalClosed.uncurry (π d b S L M N c j) ▷ S.obj a) ≫ tail := by
      simpa only [X, tail, Category.assoc] using congrArg (fun z => z ≫
        (MonoidalClosed.uncurry (π d b S L M N c j) ▷ S.obj a) ≫ tail)
        (associator_inv_naturality_middle X q (S.obj a))
    _ = _ := by
      rw [← comp_whiskerRight_assoc, ← MonoidalClosed.uncurry_natural_left]

/-- The source-order balanced adjunction retains both whole transpose functions. -/
example (M X Y : Module d S L) :
    letI := moduleMonoidal d b S L B
    (X ⊗ M ⟶ Y) ≃ (X ⟶ (functor d b S L B M).obj Y) :=
  (adjunction d b S L B M).homEquiv X Y

/-- Both actual balanced maps recover the entire original source tensor arrow. -/
example (M X Y : Module d S L) :
    letI := moduleMonoidal d b S L B
    ∀ f : X ⊗ M ⟶ Y,
      ((adjunction d b S L B M).homEquiv X Y).symm
        ((adjunction d b S L B M).homEquiv X Y f) = f :=
  ((adjunction d b S L B M).homEquiv X Y).left_inv

/-- Both actual balanced maps recover the whole original mapping-module arrow. -/
example (M X Y : Module d S L) :
    letI := moduleMonoidal d b S L B
    ∀ f : X ⟶ (functor d b S L B M).obj Y,
      (adjunction d b S L B M).homEquiv X Y
        (((adjunction d b S L B M).homEquiv X Y).symm f) = f :=
  ((adjunction d b S L B M).homEquiv X Y).right_inv

end CategoryTheory.Enriched.ModuleMappingRActionTests
