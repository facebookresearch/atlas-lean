/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory
import MathlibExt.AlgebraicTopology.CategoricalSource.NerveBasic

/-!
# The coherent simplices and their nerve

The construction reuses Mathlib's simplicial thickening: its Hom
Objects are nerves of endpoint-containing interval-subset posets and
Composition is union. All simplex operators are the enriched
direct-image functors. This packages their cosimplicial diagram
and its nerve on the enriched category carrier.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment

/-- The coherent simplex, with individual vertices and interval-subset Hom nerves. -/
abbrev coherentSimplex (n : SimplexCategory) : Carrier.{u} :=
  of (SimplicialThickening (ULift.{u} (Fin (n.len + 1))))

/-- The enriched functor induced by direct image of interval subsets under a simplex operator. -/
abbrev coherentSimplexMap {n m : SimplexCategory} (f : n ⟶ m) :
    coherentSimplex.{u} n ⟶ coherentSimplex.{u} m :=
  SimplicialThickening.functor f.toOrderHom.uliftMap

/-- The cosimplicial enriched-category diagram, including all faces and degeneracies. -/
def coherentSimplices : SimplexCategory ⥤ Carrier.{u} where
  obj := coherentSimplex
  map f := coherentSimplexMap f
  map_id n := SimplicialThickening.functor_id (ULift (Fin (n.len + 1)))
  map_comp f g := SimplicialThickening.functor_comp f.toOrderHom.uliftMap g.toOrderHom.uliftMap

/-- The coherent nerve functor of the coherent-simplex diagram. -/
abbrev coherentNerveFunctor : Carrier.{u} ⥤ SSet.{u} :=
  CategoryTheory.simplicialNerveFunctor.{u, u}

/-- This nerve is literally the pinned Mathlib coherent nerve on the same enrichment. -/
theorem coherentNerve_eq_mathlib (C : Carrier.{u}) :
    coherentNerveFunctor.obj C = SimplicialNerve (ForgetEnrichment SSet.{u} C) := rfl

/-- A coherent-nerve simplex is the enriched functor from the corresponding coherent
simplex. -/
abbrev CoherentSimplexIn (C : Carrier.{u}) (n : SimplexCategory) :=
  (coherentNerveFunctor.obj C).obj (op n)

/-- Coherent-nerve operators precompose the enriched simplex functor. -/
theorem coherentNerve_operator (C : Carrier.{u}) {n m : SimplexCategory} (f : n ⟶ m)
    (σ : CoherentSimplexIn C m) :
    (coherentNerveFunctor.obj C).map f.op σ = (coherentSimplexMap f).comp SSet.{u} σ := rfl

/-- A strict enriched map acts by postcomposition on every coherent simplex. -/
theorem coherentNerve_map (C D : Carrier.{u}) (F : C ⟶ D) (n : SimplexCategory)
    (σ : CoherentSimplexIn C n) :
    (coherentNerveFunctor.map F).app (op n) σ = σ.comp SSet.{u} F := rfl

end CategoryTheory.SimplicialEnrichment
