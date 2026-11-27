/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.NaturalTransformation

/-!
# The category of enriched functors into a closed base

The objects wrap enriched functors. Morphisms are actual unit-graded
transformations, retaining hom-object naturality for a plain enriched source.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uA uV vV

namespace CategoryTheory

open MonoidalCategory
open scoped MonoidalClosed

/-- Enriched functors into the closed self-enrichment, bundled for their
category of genuine unit-graded transformations. -/
structure EnrichedFunctorCat
    (V : Type uV) [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
    (A : Type uA) [EnrichedCategory V A] where
  /-- The actual enriched functor. -/
  toEnrichedFunctor : EnrichedFunctor V A V

namespace EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Full unit-graded transformations give the category of enriched functors.
The instance belongs only to this wrapper type. -/
instance category : Category (EnrichedFunctorCat V A) where
  Hom F G := GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    F.toEnrichedFunctor G.toEnrichedFunctor
  id F := GradedNatTrans.unitId F.toEnrichedFunctor
  comp a b := GradedNatTrans.unitComp a b
  id_comp := by
    intro F G a
    ext X
    apply (eHomEquiv V).symm.injective
    simp only [GradedNatTrans.unitComp_component,
      GradedNatTrans.unitId_component, Category.id_comp]
  comp_id := by
    intro F G a
    ext X
    apply (eHomEquiv V).symm.injective
    simp only [GradedNatTrans.unitComp_component,
      GradedNatTrans.unitId_component, Category.comp_id]
  assoc := by
    intro F G H K a b c
    ext X
    apply (eHomEquiv V).symm.injective
    simp only [GradedNatTrans.unitComp_component, Category.assoc]

/-- An ordinary component of a genuine unit-graded transformation. -/
abbrev component {F G : EnrichedFunctorCat V A} (a : F ⟶ G) (X : A) :
    F.toEnrichedFunctor.obj X ⟶ G.toEnrichedFunctor.obj X :=
  (eHomEquiv V).symm (a.app X)

/-- Identity components are identities of the selected objects. -/
@[simp]
theorem component_id (F : EnrichedFunctorCat V A) (X : A) :
    component (𝟙 F) X = 𝟙 (F.toEnrichedFunctor.obj X) :=
  GradedNatTrans.unitId_component F.toEnrichedFunctor X

/-- Source-first composition composes the actual ordinary components. -/
@[simp]
theorem component_comp {F G H : EnrichedFunctorCat V A}
    (a : F ⟶ G) (b : G ⟶ H) (X : A) :
    component (a ≫ b) X = component a X ≫ component b X :=
  GradedNatTrans.unitComp_component a b X

/-- Genuine transformations are determined by their ordinary components. -/
@[ext]
theorem hom_ext {F G : EnrichedFunctorCat V A} {a b : F ⟶ G}
    (h : ∀ X, component a X = component b X) : a = b := by
  exact GradedNatTrans.ext
    (funext fun X => (eHomEquiv V).symm.injective (h X))

end EnrichedFunctorCat
end CategoryTheory
