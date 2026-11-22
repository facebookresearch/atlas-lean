/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.MappingBifunctorFields
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Free module functors for enriched Day convolution

Given the enriched monoidal index, its braided structure and a lax monoidal
sphere functor, the composite of enriched free evaluation with the free
right-module functor agrees with the primitive free module construction.
The object equality and heterogeneous equality on coefficient maps yield
an equality of the entire functors. The construction retains the stated
closed symmetric monoidal and colimit assumptions.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj



namespace OrthogonalIGeneratorProbe.LiteralFreeExt

attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
  SphereModuleMappingEnd.moduleCategory MonoidalLeftAction.monoidalOppositeLeftAction

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

open EnrichedDayKernel ModuleMappingR

/-- The free module functor defined by its original free objects and coefficient-induced module
maps. -/
def functor (r : I) : V ⥤ Module d S L :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  Free.functor r ⋙ RightModuleFree.functor (⟨S⟩ : EnrichedFunctorCat V I)

/-- The primitive free right-module functor for the original Day tensor and sphere monoid. -/
def original (r : I) : V ⥤ Module d S L :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free
    (⟨S⟩ : EnrichedFunctorCat V I) r

omit [SymmetricCategory I] [HasProducts V] [HasEqualizers V] in
theorem obj_eq (r : I) (K : V) :
    (functor d S L r).obj K = (original d S L r).obj K :=
  PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Internal.freeObject_eq
    d S L r K

omit [SymmetricCategory I] [HasProducts V] [HasEqualizers V] in
theorem map_heq (r : I) {K K' : V} (i : K ⟶ K') :
    HEq ((functor d S L r).map i) ((original d S L r).map i) := HEq.refl _

omit [SymmetricCategory I] [HasProducts V] [HasEqualizers V] in
theorem whole_eq (r : I) : functor d S L r = original d S L r :=
  Functor.hext (obj_eq d S L r) (fun _ _ i => map_heq d S L r i)

omit [SymmetricCategory I] [HasProducts V] [HasEqualizers V] in
theorem whole_heq (r : I) : HEq (functor d S L r) (original d S L r) :=
  heq_of_eq (whole_eq d S L r)


end OrthogonalIGeneratorProbe.LiteralFreeExt
