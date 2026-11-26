/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategoryFunctoriality
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import MathlibExt.CategoryTheory.NerveMonomorphism

/-!
# The composition-preserving scalar nerve

The outer simplicial direction is the native category nerve and hence
retains identity and composition. The inner direction uses the original
enriched scalar operators. The canonical general nerve retains independent object and Hom
universes, with values in their maximum; the original small-object API
specializes this same construction in the Hom universe. Locally monic strict functors that are injective on objects
induce actual monomorphisms of these simplicial spaces.
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory

namespace SSet

/-- The single canonical strict scalar nerve in independent object and Hom universes. -/
def scalarNerveUniverse (C : Type v) [EnrichedCategory SSet.{u} C] :
    SimplicialObject SSet.{max u v} :=
  (scalarCategoryDiagramUniverse C ⋙ nerveFunctor.{u, v}).flip

/-- Every original enriched functor gives the full strict nerve map in the same object universe. -/
def scalarNerveMapUniverse {C D : Type v} [EnrichedCategory SSet.{u} C]
    [EnrichedCategory SSet.{u} D] (P : EnrichedFunctor SSet.{u} C D) :
    scalarNerveUniverse C ⟶ scalarNerveUniverse D :=
  (CategoryTheory.flipFunctor _ _ _).map
    (CategoryTheory.Functor.whiskerRight (scalarCategoryMapUniverse P) nerveFunctor.{u, v})

variable {C D : Type} [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]

/-- The original small scalar category diagram is the canonical general diagram at object universe zero. -/
abbrev scalarCategoryDiagram (C : Type) [EnrichedCategory SSet.{u} C] :
    SimplexCategoryᵒᵖ ⥤ Cat.{u, 0} := scalarCategoryDiagramUniverse C

/-- The original small scalar map specializes the same canonical whole enriched functor. -/
abbrev scalarCategoryMap (P : EnrichedFunctor SSet.{u} C D) :
    scalarCategoryDiagram C ⟶ scalarCategoryDiagram D := scalarCategoryMapUniverse P

/-- The original small-object scalar nerve specializes the single canonical independent-universe nerve. -/
def scalarNerve (C : Type) [EnrichedCategory SSet.{u} C] : SimplicialObject SSet.{u} :=
  scalarNerveUniverse C

/-- The original scalar nerve map specializes that same whole original enriched functor. -/
def scalarNerveMap (P : EnrichedFunctor SSet.{u} C D) : scalarNerve C ⟶ scalarNerve D :=
  scalarNerveMapUniverse P

/-- Local original Hom monomorphisms give faithful ordinary functors at every scalar simplex. -/
instance scalarFunctor_faithful (P : EnrichedFunctor SSet.{u} C D)
    [∀ x y, Mono (P.map x y)] (Δ : SimplexCategoryᵒᵖ) : (scalarFunctor P Δ).Faithful where
  map_injective {x y} := injective_of_mono ((P.map x.obj y.obj).app Δ)

/-- The composition-preserving scalar nerve retains a genuinely monic finite presentation boundary. -/
theorem scalarNerveMap_mono (P : EnrichedFunctor SSet.{u} C D)
    [∀ x y, Mono (P.map x y)] (hobj : Function.Injective P.obj) : Mono (scalarNerveMap P) := by
  have hi : ∀ Δ, Function.Injective (scalarFunctor P Δ).obj := by
    intro Δ x y h
    cases x
    cases y
    congr 1
    exact hobj (congrArg ScalarObject.obj h)
  have h : ∀ n, Mono ((scalarNerveMap P).app n) := by
    intro n
    have hh : ∀ Δ, Mono (((scalarNerveMap P).app n).app Δ) := by
      intro Δ
      have hn := nerveMap_mono_of_faithful (scalarFunctor P Δ) (hi Δ)
      exact inferInstanceAs (Mono ((nerveMap (scalarFunctor P Δ)).app n))
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

end SSet
