/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeOperators
import MathlibExt.CategoryTheory.Enriched.FunctorCompositionLaws

/-!
# Actual coherent unstraightening simplices and their original operators

A simplex retains an original coherent base simplex and a whole marked
natural map from its maximum-marked cone weight to the original
coefficient diagram. Every ordinal operator restricts the same base
simplex and applies the original direct-image cone map. The identity
and composition laws are proved on all base Homs and all marked
components, not supplied as an unstraightening outcome.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

variable {C : Type u} [EnrichedCategory SSet.{u} C]

/-- The original coefficient diagram restricted to the actual coherent base simplex. -/
abbrev simplexCoefficient (F : EnrichedDiagram Cᵒᵖ) {n : ℕ}
    (σ : EnrichedFunctor SSet.{u} (Index.{u} n) C) : EnrichedDiagram (Index.{u} n)ᵒᵖ :=
  σ.opposite.comp SSet.{u} F

/-- A genuine unstraightening simplex retains the entire original base and cone-section data. -/
structure UnstraighteningSimplex (F : EnrichedDiagram Cᵒᵖ) (n : ℕ) where
  /-- The whole original coherent base simplex, including all Hom operators. -/
  base : EnrichedFunctor SSet.{u} (Index.{u} n) C
  /-- Its actual marked natural cone section. -/
  sectionMap : EnrichedDiagramMap (coneDiagram n) (simplexCoefficient F base)

/-- Base and whole marked section data determine the actual unstraightening simplex. -/
theorem UnstraighteningSimplex.ext {F : EnrichedDiagram Cᵒᵖ} {n : ℕ}
    {a b : UnstraighteningSimplex F n} (h : a.base = b.base)
    (ha : HEq a.sectionMap b.sectionMap) : a = b := by
  cases a
  cases b
  cases h
  cases eq_of_heq ha
  rfl

/-- Every original ordinal operator restricts the whole base and the actual maximum-marked section. -/
def UnstraighteningSimplex.pull {F : EnrichedDiagram Cᵒᵖ} {n m : ℕ}
    (f : Vertex.{u} m →o Vertex.{u} n) (a : UnstraighteningSimplex F n) :
    UnstraighteningSimplex F m := by
  let r := enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f))
  let t := EnrichedDiagramMap.comp (coneOperator f) (r.map a.sectionMap)
  refine ⟨(indexMap f).comp SSet.{u} a.base, ⟨t.app, ?_⟩⟩
  intro i j
  have h := t.naturality i j
  dsimp only [t, r, enrichedDiagramRestrict, EnrichedDiagramMap.comp,
    simplexCoefficient, EnrichedFunctor.comp, EnrichedFunctor.opposite] at h ⊢
  simpa only [Category.assoc] using h

/-- The original base of a restricted simplex is precisely the whole enriched precomposition. -/
theorem UnstraighteningSimplex.pull_base {F : EnrichedDiagram Cᵒᵖ} {n m : ℕ}
    (f : Vertex.{u} m →o Vertex.{u} n) (a : UnstraighteningSimplex F n) :
    (a.pull f).base = (indexMap f).comp SSet.{u} a.base := rfl

/-- Each restricted marked section retains exactly the original cone-image map and component. -/
theorem UnstraighteningSimplex.pull_section {F : EnrichedDiagram Cᵒᵖ} {n m : ℕ}
    (f : Vertex.{u} m →o Vertex.{u} n) (a : UnstraighteningSimplex F n) (i : (Index.{u} m)ᵒᵖ) :
    (a.pull f).sectionMap.app i =
      coneImage f i.unop.as ≫ a.sectionMap.app (op ((indexMap f).obj i.unop)) := rfl

/-- The identity ordinal operator keeps the entire original unstraightening simplex. -/
theorem UnstraighteningSimplex.pull_id {F : EnrichedDiagram Cᵒᵖ} {n : ℕ}
    (a : UnstraighteningSimplex F n) : a.pull (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) = a := by
  have hb : (a.pull (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).base = a.base :=
    (congrArg (fun j => j.comp SSet.{u} a.base) (SimplicialThickening.functor_id (Vertex.{u} n))).trans
      (EnrichedFunctor.id_comp_eq a.base)
  apply UnstraighteningSimplex.ext hb
  apply EnrichedDiagramMap.hext (congrArg (simplexCoefficient F) hb)
  apply heq_of_eq
  funext i
  change coneImage (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) i.unop.as ≫ a.sectionMap.app i =
    a.sectionMap.app i
  exact (congrArg (fun t => t ≫ a.sectionMap.app i) (coneImage_id i.unop.as)).trans
    (Category.id_comp _)

/-- All consecutive original ordinal operators retain the same whole composed simplex and marked section. -/
theorem UnstraighteningSimplex.pull_comp {F : EnrichedDiagram Cᵒᵖ} {n m k : ℕ}
    (f : Vertex.{u} m →o Vertex.{u} n) (g : Vertex.{u} k →o Vertex.{u} m)
    (a : UnstraighteningSimplex F n) : (a.pull f).pull g = a.pull (f.comp g) := by
  have hb : ((a.pull f).pull g).base = (a.pull (f.comp g)).base :=
    (EnrichedFunctor.comp_assoc_eq (indexMap g) (indexMap f) a.base).symm.trans
      (congrArg (fun j => j.comp SSet.{u} a.base) (SimplicialThickening.functor_comp g f).symm)
  apply UnstraighteningSimplex.ext hb
  apply EnrichedDiagramMap.hext (congrArg (simplexCoefficient F) hb)
  apply heq_of_eq
  funext i
  change coneImage g i.unop.as ≫
      (coneImage f (g i.unop.as) ≫ a.sectionMap.app (op ((indexMap (f.comp g)).obj i.unop))) =
    coneImage (f.comp g) i.unop.as ≫ a.sectionMap.app (op ((indexMap (f.comp g)).obj i.unop))
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ a.sectionMap.app (op ((indexMap (f.comp g)).obj i.unop)))
      (coneImage_comp g f i.unop.as))

end SSet.Marked.CoherentWeight
