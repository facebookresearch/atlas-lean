/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentSimplex
import MathlibExt.AlgebraicTopology.SimplicialCategory.Presentation

/-!
# The actual generators for coherent realization

Objects are the original vertices of the input simplicial set. A
generating Hom simplex retains an input simplex, its two specified
vertices, and an actual Hom simplex of the corresponding coherent
simplex. The inner simplicial operators act on that Hom simplex.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment

/-- Read the supplied individual vertex of an actual input simplex. -/
def vertex (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n))
    (i : coherentSimplex.{u} n) : K _⦋0⦌ :=
  K.map (SimplexCategory.const ⦋0⦌ n i.as.down).op σ

/-- The actual vertex map commutes with each original outer simplex operator. -/
theorem vertex_operator (K : SSet.{u}) {n m : SimplexCategory} (f : n ⟶ m)
    (σ : K.obj (op m)) (i : coherentSimplex.{u} n) :
    vertex K (K.map f.op σ) i = vertex K σ ((coherentSimplexMap f).obj i) := by
  change K.map (SimplexCategory.const ⦋0⦌ n i.as.down).op (K.map f.op σ) = _
  rw [← CategoryTheory.comp_apply, ← K.map_comp]
  rfl

/-- An original coherent Hom generator with both individual endpoint equations retained. -/
structure Arrow (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) where
  /-- The outer input simplex degree. -/
  degree : SimplexCategory
  /-- The original supplied input simplex. -/
  simplex : K.obj (op degree)
  /-- Its specified original source vertex. -/
  source : coherentSimplex.{u} degree
  /-- Its specified original target vertex. -/
  target : coherentSimplex.{u} degree
  /-- The source is the given individual input vertex. -/
  source_eq : vertex K simplex source = x
  /-- The target is the given individual input vertex. -/
  target_eq : vertex K simplex target = y
  /-- The actual coherent-simplex Hom simplex, at the given inner scalar degree. -/
  hom : (source ⟶[SSet.{u}] target).obj q

/-- Every inner scalar operator acts on the actual coherent Hom, retaining all outer
endpoint data. -/
def Arrow.map {K : SSet.{u}} {x y : K _⦋0⦌} {q r : SimplexCategoryᵒᵖ}
    (f : q ⟶ r) (a : Arrow K x y q) : Arrow K x y r :=
  ⟨a.degree, a.simplex, a.source, a.target, a.source_eq, a.target_eq,
    (a.source ⟶[SSet.{u}] a.target).map f a.hom⟩

/-- The vertex-indexed simplicial quiver of actual coherent generators. -/
def generatingQuiver (K : SSet.{u}) : SimplicialQuiver.Data (K _⦋0⦌) where
  Hom x y := {
    obj := Arrow K x y
    map := fun f => ↾Arrow.map f
    map_id := fun q => by
      ext a
      cases a with
      | mk n σ i j hx hy a =>
          change Arrow.mk n σ i j hx hy ((i ⟶[SSet.{u}] j).map (𝟙 q) a) = Arrow.mk n σ i j hx hy a
          rw [(i ⟶[SSet.{u}] j).map_id]
          rfl
    map_comp := fun f g => by
      ext a
      cases a with
      | mk n σ i j hx hy a =>
          change Arrow.mk n σ i j hx hy ((i ⟶[SSet.{u}] j).map (f ≫ g) a) =
            Arrow.mk n σ i j hx hy ((i ⟶[SSet.{u}] j).map g ((i ⟶[SSet.{u}] j).map f a))
          rw [(i ⟶[SSet.{u}] j).map_comp]
          rfl }

/-- The specified actual Hom simplex becomes a generator with exactly its original endpoint
equations. -/
def arrow (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n))
    (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y) {q : SimplexCategoryᵒᵖ}
    (a : (i ⟶[SSet.{u}] j).obj q) : ((generatingQuiver K).Hom x y).obj q :=
  ⟨n, σ, i, j, hx, hy, a⟩

/-- Its corresponding original whole free path has one actual coherent generator. -/
def arrowPath (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n))
    (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y) {q : SimplexCategoryᵒᵖ}
    (a : (i ⟶[SSet.{u}] j).obj q) : SimplicialQuiver.Path (generatingQuiver K) q x y :=
  @Quiver.Hom.toPath (K _⦋0⦌) (SimplicialQuiver.quiverAt (generatingQuiver K) q) x y
    (arrow K σ i j hx hy a)

/-- Inner scalar operators preserve the original coherent generating path and its full
endpoint data. -/
theorem arrowPath_operator (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n))
    (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y) {q r : SimplexCategoryᵒᵖ}
    (f : q ⟶ r) (a : (i ⟶[SSet.{u}] j).obj q) :
    SimplicialQuiver.mapPath (generatingQuiver K) f (arrowPath K σ i j hx hy a) =
      arrowPath K σ i j hx hy ((i ⟶[SSet.{u}] j).map f a) := rfl

end CategoryTheory.CoherentRealization
