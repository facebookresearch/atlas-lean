/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentGenerators

/-!
# The genuine coherent realization presentation

Its original object type is the set of input vertices. The actual
generating relations impose coherent-simplex identities, composition,
and every outer simplex operator. Their simplicial congruence produces
actual Hom simplicial sets and a genuine enriched category.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment SimplicialQuiver

/-- The actual generating equations for coherent realization, at the same original endpoints. -/
inductive Equations (K : SSet.{u}) :
    ∀ {q : SimplexCategoryᵒᵖ} {x y : K _⦋0⦌},
      Path (generatingQuiver K) q x y → Path (generatingQuiver K) q x y → Prop
  | identity (q : SimplexCategoryᵒᵖ) {n : SimplexCategory} (σ : K.obj (op n))
      (i : coherentSimplex.{u} n) {x : K _⦋0⦌} (hx : vertex K σ i = x) :
      Equations K (arrowPath K σ i i hx hx ((eId SSet.{u} i).app q PUnit.unit))
        (@Quiver.Path.nil (K _⦋0⦌) (quiverAt (generatingQuiver K) q) x)
  | composition (q : SimplexCategoryᵒᵖ) {n : SimplexCategory} (σ : K.obj (op n))
      (i j k : coherentSimplex.{u} n) {x y z : K _⦋0⦌}
      (hx : vertex K σ i = x) (hy : vertex K σ j = y) (hz : vertex K σ k = z)
      (a : (i ⟶[SSet.{u}] j).obj q) (b : (j ⟶[SSet.{u}] k).obj q) :
      Equations K (arrowPath K σ i k hx hz ((eComp SSet.{u} i j k).app q (a, b)))
        (@Quiver.Path.comp (K _⦋0⦌) (quiverAt (generatingQuiver K) q) x y z
          (arrowPath K σ i j hx hy a) (arrowPath K σ j k hy hz b))
  | operator (q : SimplexCategoryᵒᵖ) {n m : SimplexCategory} (f : n ⟶ m)
      (σ : K.obj (op m)) (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌}
      (hx : vertex K (K.map f.op σ) i = x) (hy : vertex K (K.map f.op σ) j = y)
      (a : (i ⟶[SSet.{u}] j).obj q) :
      Equations K (arrowPath K (K.map f.op σ) i j hx hy a)
        (arrowPath K σ ((coherentSimplexMap f).obj i) ((coherentSimplexMap f).obj j)
          ((vertex_operator K f σ i).symm.trans hx) ((vertex_operator K f σ j).symm.trans hy)
          (((coherentSimplexMap f).map i j).app q a))

/-- These equations are actual relations on the original free coherent generating paths. -/
def relations (K : SSet.{u}) : Relations (generatingQuiver K) :=
  fun _ _ _ p q => Equations K p q

/-- The actual coherent realization, with the individual original input vertices as its objects. -/
def realization (K : SSet.{u}) : Carrier.{u} := by
  letI := presentedEnrichment (relations K)
  exact SimplicialEnrichment.of (K _⦋0⦌)

/-- The actual Hom simplicial set of coherent realization at the two supplied original vertices. -/
abbrev hom (K : SSet.{u}) (x y : K _⦋0⦌) : SSet.{u} :=
  presentedHom (relations K) x y

/-- A whole coherent Hom is inserted into realization with exactly its supplied endpoint
equations. -/
def simplexHom (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n))
    (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y) :
    (i ⟶[SSet.{u}] j) ⟶ hom K x y where
  app q := ↾fun a => _root_.Quotient.mk _ (arrowPath K σ i j hx hy a)
  naturality q r f := by ext a; rfl

/-- Every original input simplex determines a genuine enriched functor into its coherent
realization. -/
def simplexInto (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n)) :
    coherentSimplex.{u} n ⟶ realization K where
  obj i := vertex K σ i
  map i j := simplexHom K σ i j rfl rfl
  map_id i := by
    ext q a
    exact _root_.Quotient.sound (Closure.relation (Equations.identity q σ i rfl))
  map_comp i j k := by
    ext q a
    exact _root_.Quotient.sound
      (Closure.relation (Equations.composition q σ i j k rfl rfl rfl a.1 a.2))

/-- The inserted coherent Hom keeps precisely its original source and target, not their
component classes. -/
theorem simplexInto_obj (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n))
    (i : coherentSimplex.{u} n) : (simplexInto K σ).obj i = vertex K σ i := rfl

/-- The inserted actual Hom simplex is represented by the original coherent generating path. -/
theorem simplexInto_map (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n))
    (i j : coherentSimplex.{u} n) (q : SimplexCategoryᵒᵖ) (a : (i ⟶[SSet.{u}] j).obj q) :
    ((simplexInto K σ).map i j).app q a =
      _root_.Quotient.mk (congruence (relations K) q (vertex K σ i) (vertex K σ j))
        (arrowPath K σ i j rfl rfl a) := rfl

end CategoryTheory.CoherentRealization
