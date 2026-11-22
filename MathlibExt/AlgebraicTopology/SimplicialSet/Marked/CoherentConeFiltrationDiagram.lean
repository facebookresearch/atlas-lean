/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFiltrationOrder
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDiagram

/-!
# Whole enriched stages of the original cone maximum filtration

Original coherent paths act by their entire vertex union. The exact
maximum equality shows that this action restricts to each bounded and
strictly preceding stage, preserving every original scalar Hom prism.
The stage inclusions are whole enriched natural marked maps. Strict
stages are not asserted to commute with arbitrary vertex collapses.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The whole original path union restricts to a selected maximum-bounded stage. -/
def coneAtMostPrependFunctor {n : ℕ} (i j k : Vertex.{u} n) :
    SimplicialThickening.Path i j × ConeAtMost j k ⥤ ConeAtMost i k where
  obj a := ⟨a.2.val.prepend a.1, (a.2.val.prepend_maximum a.1).le.trans a.2.property⟩
  map {a b} f := homOfLE (by
    change a.1.I.toFinite.toFinset ∪ a.2.val.vertices ⊆ b.1.I.toFinite.toFinset ∪ b.2.val.vertices
    apply Finset.union_subset_union
    · intro l hl
      exact b.1.I.toFinite.mem_toFinset.mpr (f.1.1.1.1 (a.1.I.toFinite.mem_toFinset.mp hl))
    · exact leOfHom f.2)

/-- The exact same original path union restricts to the strictly preceding maximum stage. -/
def coneBeforePrependFunctor {n : ℕ} (i j k : Vertex.{u} n) :
    SimplicialThickening.Path i j × ConeBefore j k ⥤ ConeBefore i k where
  obj a := ⟨a.2.val.prepend a.1, (a.2.val.prepend_maximum a.1).le.trans_lt a.2.property⟩
  map {a b} f := homOfLE (by
    change a.1.I.toFinite.toFinset ∪ a.2.val.vertices ⊆ b.1.I.toFinite.toFinset ∪ b.2.val.vertices
    apply Finset.union_subset_union
    · intro l hl
      exact b.1.I.toFinite.mem_toFinset.mpr (f.1.1.1.1 (a.1.I.toFinite.mem_toFinset.mp hl))
    · exact leOfHom f.2)

/-- Every whole original coherent Hom prism acts on the bounded stage with its original maximum marking. -/
def coneAtMostAction {n : ℕ} (i j k : Vertex.{u} n) :
    prod (max (nerve (SimplicialThickening.Path i j))) (coneAtMostWeight j k) ⟶ coneAtMostWeight i k where
  hom :=
    { app q := ↾fun a => a.1.prod' a.2 ⋙ coneAtMostPrependFunctor i j k
      naturality q r f := by ext a; rfl }
  preserve he :=
    (ConeSubset.prepend_maximum _ _).trans (he.2.trans (ConeSubset.prepend_maximum _ _).symm)

/-- The preceding stage carries the same whole original path action and exact selected marking. -/
def coneBeforeAction {n : ℕ} (i j k : Vertex.{u} n) :
    prod (max (nerve (SimplicialThickening.Path i j))) (coneBeforeWeight j k) ⟶ coneBeforeWeight i k where
  hom :=
    { app q := ↾fun a => a.1.prod' a.2 ⋙ coneBeforePrependFunctor i j k
      naturality q r f := by ext a; rfl }
  preserve he :=
    (ConeSubset.prepend_maximum _ _).trans (he.2.trans (ConeSubset.prepend_maximum _ _).symm)

/-- The entire selected maximum-bounded stage is an actual marked enriched diagram on the original opposite
  coherent simplex. -/
def coneAtMostDiagram {n : ℕ} (k : Vertex.{u} n) : EnrichedDiagram (Index.{u} n)ᵒᵖ where
  obj i := coneAtMostWeight i.unop.as k
  map i j := maxCurry (coneAtMostAction j.unop.as i.unop.as k)
  map_id i := by
    ext q z
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => Subtype.ext (ConeSubset.prepend_id _))
      (fun _ _ _ => Subsingleton.elim _ _)
  map_comp i j l := by
    ext q fg
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => Subtype.ext (ConeSubset.prepend_comp _ _ _).symm)
      (fun _ _ _ => Subsingleton.elim _ _)

/-- The whole strictly preceding stage is a genuine enriched diagram, including empty values at vertices
  outside the stage. -/
def coneBeforeDiagram {n : ℕ} (k : Vertex.{u} n) : EnrichedDiagram (Index.{u} n)ᵒᵖ where
  obj i := coneBeforeWeight i.unop.as k
  map i j := maxCurry (coneBeforeAction j.unop.as i.unop.as k)
  map_id i := by
    ext q z
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => Subtype.ext (ConeSubset.prepend_id _))
      (fun _ _ _ => Subsingleton.elim _ _)
  map_comp i j l := by
    ext q fg
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => Subtype.ext (ConeSubset.prepend_comp _ _ _).symm)
      (fun _ _ _ => Subsingleton.elim _ _)

/-- The native strict-stage inclusion changes only the proved maximum bound, not a vertex, inclusion or mark. -/
def coneBeforeInclusion {n : ℕ} (i k : Vertex.{u} n) :
    coneBeforeWeight i k ⟶ coneAtMostWeight i k where
  hom := nerveMap
    { obj a := ⟨a.val, a.property.le⟩
      map f := homOfLE (leOfHom f) }
  preserve he := he

/-- The actual preceding stage includes as a whole enriched natural marked map. -/
def coneBeforeDiagramInclusion {n : ℕ} (k : Vertex.{u} n) :
    coneBeforeDiagram k ⟶ coneAtMostDiagram k where
  app i := coneBeforeInclusion i.unop.as k
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r z
    refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- Forgetting only the stage bound embeds the whole original bounded subsets and their exact selected marks. -/
def coneAtMostInclusion {n : ℕ} (i k : Vertex.{u} n) : coneAtMostWeight i k ⟶ coneWeight i where
  hom := nerveMap
    { obj a := a.val
      map f := homOfLE (leOfHom f) }
  preserve he := he

/-- Every selected bounded stage retains the same complete original cone action as an enriched subdiagram. -/
def coneAtMostDiagramInclusion {n : ℕ} (k : Vertex.{u} n) :
    coneAtMostDiagram k ⟶ coneDiagram n where
  app i := coneAtMostInclusion i.unop.as k
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r z
    refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

end SSet.Marked.CoherentWeight
