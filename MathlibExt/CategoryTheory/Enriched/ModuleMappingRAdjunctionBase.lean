/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAction

/-!
# Balanced tensor adjunction for the literal translated Mapping_R

The monoidal structure is the original relative right-module tensor over the
actual Day monoid. Its right adjoint is the translated action equalizer, with
the inherited action identified by its complete end projections. The factories
choose the whole translated equalizer functor and the original source
comparison. Component laws are stated separately, against these exact
selected structures.

The raw translated equalizer exists without coefficient commutativity. This
module uses braided lax coefficient data for its module-valued output and
balanced tensor adjunction.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingR

open EnrichedFunctorCat EnrichedDayKernel

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

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

section Factories

attribute [local irreducible] Closed.monoidalClosed
set_option backward.isDefEq.respectTransparency true

/-- The actual relative right-module symmetry for the selected original Day tensor. -/
@[instance_reducible]
def moduleSymmetric :
    letI := moduleMonoidal d b S L B
    SymmetricCategory (Module d S L) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact RightModuleFree.tensorSymmetric (⟨S⟩ : EnrichedFunctorCat V I)

/-- The original balanced stock adjunction, used after the complete source comparison. -/
def stockLeftAdjunction (M : Module d S L) :
    letI := moduleMonoidal d b S L B
    tensorLeft M ⊣ stockFunctor d b S L B M := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI := moduleMonoidal d b S L B
  exact RightModuleMappingEnd.stockAdjunction (⟨S⟩ : EnrichedFunctorCat V I) M

/-- Balanced tensoring on the left is adjoint to the actual translated source equalizer. -/
def leftAdjunction (M : Module d S L) :
    letI := moduleMonoidal d b S L B
    tensorLeft M ⊣ functor d b S L B M := by
  letI := moduleMonoidal d b S L B
  exact (stockLeftAdjunction d b S L B M).ofNatIsoRight
    (comparisonNatIso d b S L B M).symm

/-- Actual closedness of the original relative right-module tensor, with the translated
equalizer chosen as its internal Hom. This is an explicit factory. -/
@[instance_reducible]
def moduleClosed :
    letI := moduleMonoidal d b S L B
    MonoidalClosed (Module d S L) := by
  letI := moduleMonoidal d b S L B
  exact { closed M := {
    rightAdj := functor d b S L B M
    adj := leftAdjunction d b S L B M } }

end Factories

/-- The chosen closed internal Hom is the whole actual translated mapping functor. -/
theorem moduleClosed_ihom (M : Module d S L) :
    letI := moduleMonoidal d b S L B
    letI := moduleClosed d b S L B
    ihom M = functor d b S L B M := rfl

/-- The chosen closed carrier retains the literal complete translated action equalizer. -/
theorem moduleClosed_diagram (M N : Module d S L) :
    letI := moduleMonoidal d b S L B
    letI := moduleClosed d b S L B
    SphereModuleMappingEnd.diagram d S L ((ihom M).obj N) =
      diagram d b S L M N := rfl

/-- Every original target-module arrow acts by the same full raw equalizer postcomposition. -/
theorem moduleClosed_map (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') :
    letI := moduleMonoidal d b S L B
    letI := moduleClosed d b S L B
    SphereModuleMappingEnd.moduleMap d S L ((ihom M).map g) =
      post d b S L M g := functor_map d b S L B M g

end CategoryTheory.Enriched.ModuleMappingR
