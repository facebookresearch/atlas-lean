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
# The original coherent simplices and their nerve

The construction reuses Mathlib's actual simplicial thickening: its Hom
objects are nerves of endpoint-containing interval-subset posets and
composition is union. All simplex operators are the existing enriched
direct-image functors. This packages their genuine cosimplicial diagram
and its nerve on the original enriched category carrier.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment

/-- The actual coherent simplex, with individual vertices and interval-subset Hom nerves. -/
abbrev coherentSimplex (n : SimplexCategory) : Carrier.{u} :=
  of (SimplicialThickening (ULift.{u} (Fin (n.len + 1))))

/-- A genuine simplex operator acts by the existing interval-subset direct-image enriched
functor. -/
abbrev coherentSimplexMap {n m : SimplexCategory} (f : n ⟶ m) :
    coherentSimplex.{u} n ⟶ coherentSimplex.{u} m :=
  SimplicialThickening.functor f.toOrderHom.uliftMap

/-- The actual cosimplicial enriched-category diagram, including all faces and degeneracies. -/
def coherentSimplices : SimplexCategory ⥤ Carrier.{u} where
  obj := coherentSimplex
  map f := coherentSimplexMap f
  map_id n := SimplicialThickening.functor_id (ULift (Fin (n.len + 1)))
  map_comp f g := SimplicialThickening.functor_comp f.toOrderHom.uliftMap g.toOrderHom.uliftMap

/-- The genuine coherent nerve functor of the actual coherent-simplex diagram. -/
abbrev coherentNerveFunctor : Carrier.{u} ⥤ SSet.{u} :=
  CategoryTheory.simplicialNerveFunctor.{u, u}

/-- This nerve is literally the pinned Mathlib coherent nerve on the same original enrichment. -/
theorem coherentNerve_eq_mathlib (C : Carrier.{u}) :
    coherentNerveFunctor.obj C = SimplicialNerve (ForgetEnrichment SSet.{u} C) := rfl

/-- A coherent-nerve simplex is the actual enriched functor from the corresponding coherent
simplex. -/
abbrev CoherentSimplexIn (C : Carrier.{u}) (n : SimplexCategory) :=
  (coherentNerveFunctor.obj C).obj (op n)

/-- Coherent-nerve operators precompose the actual original enriched simplex functor. -/
theorem coherentNerve_operator (C : Carrier.{u}) {n m : SimplexCategory} (f : n ⟶ m)
    (σ : CoherentSimplexIn C m) :
    (coherentNerveFunctor.obj C).map f.op σ = (coherentSimplexMap f).comp SSet.{u} σ := rfl

/-- A strict original enriched map acts by postcomposition on every coherent simplex. -/
theorem coherentNerve_map (C D : Carrier.{u}) (F : C ⟶ D) (n : SimplexCategory)
    (σ : CoherentSimplexIn C n) :
    (coherentNerveFunctor.map F).app (op n) σ = σ.comp SSet.{u} F := rfl

end CategoryTheory.SimplicialEnrichment
