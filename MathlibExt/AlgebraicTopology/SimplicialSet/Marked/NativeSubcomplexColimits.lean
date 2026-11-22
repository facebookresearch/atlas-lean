/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRelativeChartRestriction
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer

/-!
# Actual whole same-base subcomplex colimits and native straightening

Every original subcomplex inclusion carries its unchanged whole minimal
marked map and base projection. True scalar face/intersection colimits
lift to the actual marked slice through minimal marking and slice
colimit reflection. Native straightening preserves these same colimits
through its actual adjunction, without a relative source-cofibration
or presentation outcome.
-/

noncomputable section
universe u v w
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every original simplex subcomplex is its complete minimally marked same-base carrier, with literal native
inclusion maps. -/
def nativeSubcomplexBasisFunctor (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (Δ[n] : SSet.{u}).Subcomplex ⥤ Over (max B) where
  obj A := nativeSubcomplexBasis B n σ A
  map {A D} h := Over.homMk (minimal.map (Subcomplex.homOfLE (leOfHom h))) (Hom.ext rfl)
  map_id A := by apply Over.OverMorphism.ext; apply Hom.ext; rfl
  map_comp f g := by apply Over.OverMorphism.ext; apply Hom.ext; rfl

/-- Its native straightening gives the original full marked subcomplex chart functor. -/
def nativeSubcomplexChartFunctor (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (Δ[n] : SSet.{u}).Subcomplex ⥤ EnrichedDiagram (realization B)ᵒᵖ :=
  nativeSubcomplexBasisFunctor B n σ ⋙ nativeStraightening B

/-- Forgetting only the base keeps precisely the native minimal-marking functor on all original subcomplexes and
inclusions. -/
theorem nativeSubcomplexBasisFunctor_forget (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    nativeSubcomplexBasisFunctor B n σ ⋙ Over.forget (max B) =
      Subcomplex.toSSetFunctor ⋙ minimal := rfl

/-- Every actual scalar subcomplex colimit cocone lifts to the full minimally marked same-base slice cocone. -/
def nativeSubcomplexIsColimit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    {J : Type v} [Category.{w} J] {K : J ⥤ (Δ[n] : SSet.{u}).Subcomplex} (q : Cocone K)
    (hq : IsColimit (Subcomplex.toSSetFunctor.mapCocone q)) :
    IsColimit ((nativeSubcomplexBasisFunctor B n σ).mapCocone q) := by
  let _ : PreservesColimitsOfSize.{w, v} minimal.{u} := minimalAdjunction.leftAdjoint_preservesColimits
  apply isColimitOfReflects (Over.forget (max B))
  exact isColimitOfPreserves minimal hq

/-- Native straightening preserves every such actual original whole face/intersection chart colimit, retaining every
native injection. -/
def nativeSubcomplexChartIsColimit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    {J : Type v} [Category.{w} J] {K : J ⥤ (Δ[n] : SSet.{u}).Subcomplex} (q : Cocone K)
    (hq : IsColimit (Subcomplex.toSSetFunctor.mapCocone q)) :
    IsColimit ((nativeSubcomplexChartFunctor B n σ).mapCocone q) := by
  let _ : PreservesColimitsOfSize.{w, v} (nativeStraightening B) :=
    (nativeStraighteningAdjunction B).leftAdjoint_preservesColimits
  exact isColimitOfPreserves (nativeStraightening B) (nativeSubcomplexIsColimit B n σ q hq)

end SSet.Marked
