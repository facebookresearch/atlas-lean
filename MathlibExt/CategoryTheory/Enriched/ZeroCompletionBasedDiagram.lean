/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.ZeroCompletion
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Strict preservation of the chosen base object by genuine completed diagrams. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalClosed ZeroObject

universe uV vV uA

namespace CategoryTheory.EnrichedZeroCompletion

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [EnrichedCategory V A]

/-- Completed diagrams whose value at the added object is literally the chosen zero of `V`. -/
def basePreserving : ObjectProperty (EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :=
  fun F => F.toEnrichedFunctor.obj zero = (0 : V)

/-- The full category of completed diagrams that literally preserve the chosen added zero. -/
abbrev BasedDiagram := (basePreserving (V := V) (A := A)).FullSubcategory

/-- Extend an original enriched diagram into the literal chosen-zero full subcategory. -/
def strictExtension : EnrichedFunctorCat V A ⥤ BasedDiagram (V := V) (A := A) :=
  (basePreserving (V := V) (A := A)).lift extension (fun _ => rfl)

/-- Forget the strict chosen-zero condition and restrict to the original index. -/
def strictRestriction : BasedDiagram (V := V) (A := A) ⥤ EnrichedFunctorCat V A :=
  (basePreserving (V := V) (A := A)).ι ⋙ restriction

/-- The counit from a normalized strict diagram back to the original strict diagram. -/
def strictCounitIso (F : BasedDiagram (V := V) (A := A)) :
    (strictRestriction ⋙ strictExtension).obj F ≅ F :=
  (basePreserving (V := V) (A := A)).isoMk (counitIso F.obj)

/-- The natural counit of strict extension and restriction. -/
def strictCounitNatIso : strictRestriction (V := V) (A := A) ⋙ strictExtension ≅
    𝟭 (BasedDiagram (V := V) (A := A)) :=
  NatIso.ofComponents strictCounitIso (fun {_ _} f => by
    apply ObjectProperty.hom_ext
    exact counitNatIso.hom.naturality f.hom)

/-- Original enriched diagrams are equivalent to literal chosen-zero completed diagrams. -/
def basedDiagramEquivalence : EnrichedFunctorCat V A ≌ BasedDiagram (V := V) (A := A) where
  functor := strictExtension
  inverse := strictRestriction
  unitIso := unitNatIso
  counitIso := strictCounitNatIso
  functor_unitIso_comp F := by
    apply ObjectProperty.hom_ext
    exact extension_triangle F

/-- Normalize a completed diagram by restriction followed by literal zero extension. -/
def strictNormalization : EnrichedFunctorCat V (EnrichedZeroCompletion V A) ⥤
    BasedDiagram (V := V) (A := A) :=
  (basePreserving (V := V) (A := A)).lift (restriction ⋙ extension) (fun _ => rfl)

/-- Strict diagrams are equivalent to all completed diagrams by inclusion and normalization. -/
def basedInclusionEquivalence : BasedDiagram (V := V) (A := A) ≌
    EnrichedFunctorCat V (EnrichedZeroCompletion V A) where
  functor := (basePreserving (V := V) (A := A)).ι
  inverse := strictNormalization
  unitIso := strictCounitNatIso.symm
  counitIso := counitNatIso
  functor_unitIso_comp F := (counitIso F.obj).inv_hom_id

theorem strictExtension_base (F : EnrichedFunctorCat V A) :
    (strictExtension.obj F).obj.toEnrichedFunctor.obj zero = (0 : V) :=
  (strictExtension.obj F).property

theorem strictNormalization_base
    (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :
    (strictNormalization.obj F).obj.toEnrichedFunctor.obj zero = (0 : V) :=
  (strictNormalization.obj F).property

theorem basedDiagram_extension_triangle (F : EnrichedFunctorCat V A) :
    strictExtension.map (basedDiagramEquivalence.unitIso.hom.app F) ≫
        basedDiagramEquivalence.counitIso.hom.app (strictExtension.obj F) =
      𝟙 (strictExtension.obj F) :=
  basedDiagramEquivalence.functor_unit_comp F

theorem basedDiagram_restriction_triangle (F : BasedDiagram (V := V) (A := A)) :
    basedDiagramEquivalence.unitIso.hom.app (strictRestriction.obj F) ≫
        strictRestriction.map (basedDiagramEquivalence.counitIso.hom.app F) =
      𝟙 (strictRestriction.obj F) :=
  basedDiagramEquivalence.unit_inverse_comp F

theorem basedInclusion_triangle (F : BasedDiagram (V := V) (A := A)) :
    basedInclusionEquivalence.functor.map (basedInclusionEquivalence.unitIso.hom.app F) ≫
        basedInclusionEquivalence.counitIso.hom.app (basedInclusionEquivalence.functor.obj F) =
      𝟙 (basedInclusionEquivalence.functor.obj F) :=
  basedInclusionEquivalence.functor_unit_comp F

theorem normalization_triangle
    (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :
    basedInclusionEquivalence.unitIso.hom.app (strictNormalization.obj F) ≫
        strictNormalization.map (basedInclusionEquivalence.counitIso.hom.app F) =
      𝟙 (strictNormalization.obj F) :=
  basedInclusionEquivalence.unit_inverse_comp F


end CategoryTheory.EnrichedZeroCompletion
