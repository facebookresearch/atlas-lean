/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.ExternalTensorMappingEndAdjunction

/-!
# Ordinary compatibility of the original genuine mapping-end enrichment

The existing weighted-end enrichment is retained literally. Its original
positive-grade/end bijection identifies unit-graded genuine transformations
with maps from the tensor unit, including both original composition maps.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe uA uV vV

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.EndOrdinaryEnrichment

open ExternalTensorMappingEndAdjunction.EndEnrichment

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  [HasProducts.{uA} V] [HasEqualizers V]

/-- The same complete genuine transformation/end bijection at the original unit grade. -/
def homEquiv (F G : EnrichedFunctorCat V A) : (F ⟶ G) ≃ (𝟙_ V ⟶ homObject F G) :=
  (GradingConvention.endHomEquiv F.toEnrichedFunctor G.toEnrichedFunctor (𝟙_ V)).symm

/-- Each Hom-equivalence projection is the original unit-graded component. -/
theorem homEquiv_projection {F G : EnrichedFunctorCat V A} (q : F ⟶ G) (a : A) :
    homEquiv F G q ≫ homProjection F G a = q.app a := by
  rw [homEquiv, GradingConvention.endHomEquiv_symm_apply]
  exact GradingConvention.endFromPositive_symmetric_π F.toEnrichedFunctor G.toEnrichedFunctor q a

/-- The ordinary identity corresponds to the same original weighted-end identity. -/
theorem homEquiv_id (F : EnrichedFunctorCat V A) :
    homEquiv F F (𝟙 F) = mappingIdentity F := by
  rw [homEquiv, GradingConvention.endHomEquiv_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original ordinary composition agrees with full weighted-end composition. -/
theorem homEquiv_comp {F G H : EnrichedFunctorCat V A} (p : F ⟶ G) (q : G ⟶ H) :
    homEquiv F H (p ≫ q) =
      (λ_ (𝟙_ V)).inv ≫ (homEquiv F G p ⊗ₘ homEquiv G H q) ≫ mappingComposition F G H := by
  apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor H.toEnrichedFunctor
  intro a
  simp only [Category.assoc]
  rw [homEquiv_projection, mappingComposition_π,
    tensorHom_comp_tensorHom_assoc, homEquiv_projection, homEquiv_projection]
  have h := congrArg (fun t => eHomEquiv V t) (component_comp p q a)
  simp only [component, Equiv.apply_symm_apply, eHomEquiv_comp] at h
  exact h

/-- Construct ordinary compatibility using the original enrichment, identities and composition. -/
@[instance_reducible]
def enrichment : EnrichedOrdinaryCategory V (EnrichedFunctorCat V A) where
  toEnrichedCategory := ExternalTensorMappingEndAdjunction.EndEnrichment.enrichment
  homEquiv := fun {F G} => homEquiv F G
  homEquiv_id := homEquiv_id
  homEquiv_comp := homEquiv_comp

/-- The compatible ordinary enrichment retains the actual original weighted Hom object. -/
theorem homObject_eq (F G : EnrichedFunctorCat V A) :
    letI := enrichment (V := V) (A := A)
    (F ⟶[V] G) = Enriched.weightedEnd F.toEnrichedFunctor G.toEnrichedFunctor := rfl

end CategoryTheory.EnrichedFunctorCat.EndOrdinaryEnrichment
