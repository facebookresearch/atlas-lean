/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentExt

/-!
# Actual maps of coherent realizations

An original simplicial map sends a coherent generator to the same
coherent Hom simplex over the image input simplex. The two endpoint
equations are the actual vertex naturality equations. The defining
relations are preserved by construction and the resulting enriched map
acts on every whole original Hom path.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment SimplicialQuiver

/-- Original vertex evaluation is natural for an actual simplicial map. -/
theorem vertex_map {K L : SSet.{u}} (f : K ⟶ L) {n : SimplexCategory} (σ : K.obj (op n))
    (i : coherentSimplex.{u} n) :
    vertex L (f.app (op n) σ) i = f.app (op ⦋0⦌) (vertex K σ i) :=
  congr($(f.naturality (SimplexCategory.const ⦋0⦌ n i.as.down).op) σ).symm

/-- The same actual original endpoint equation at the image supplied vertex. -/
theorem vertex_image {K L : SSet.{u}} (f : K ⟶ L) {n : SimplexCategory} (σ : K.obj (op n))
    (i : coherentSimplex.{u} n) {x : K _⦋0⦌} (hx : vertex K σ i = x) :
    vertex L (f.app (op n) σ) i = f.app (op ⦋0⦌) x :=
  (vertex_map f σ i).trans (congrArg (fun x => f.app (op ⦋0⦌) x) hx)

/-- The actual original image interpretation of the coherent generating quiver. -/
def mapInterpretation {K L : SSet.{u}} (f : K ⟶ L) :
    Interpretation (generatingQuiver K) (realization L) where
  obj x := f.app (op ⦋0⦌) x
  map x y := {
    app q := ↾fun a => _root_.Quotient.mk _
      (arrowPath L (f.app (op a.degree) a.simplex) a.source a.target
        (vertex_image f a.simplex a.source a.source_eq)
        (vertex_image f a.simplex a.target a.target_eq) a.hom)
    naturality q r g := by ext a; rfl }

/-- A coherent generating path maps to the same actual Hom simplex over its image original
simplex. -/
theorem map_eval_arrow {K L : SSet.{u}} (f : K ⟶ L) {n : SimplexCategory} (σ : K.obj (op n))
    (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y)
    {q : SimplexCategoryᵒᵖ} (a : (i ⟶[SSet.{u}] j).obj q) :
    (mapInterpretation f).evalPath q (arrowPath K σ i j hx hy a) =
      _root_.Quotient.mk (congruence (relations L) q (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
        (arrowPath L (f.app (op n) σ) i j (vertex_image f σ i hx) (vertex_image f σ j hy) a) :=
  congr($((mapInterpretation f).generator_eval x y).app q (arrow K σ i j hx hy a))

/-- The actual image interpretation respects all original coherent presentation equations. -/
theorem map_relations {K L : SSet.{u}} (f : K ⟶ L) (q : SimplexCategoryᵒᵖ)
    (x y : K _⦋0⦌) (p r : Path (generatingQuiver K) q x y) (h : relations K q x y p r) :
    (mapInterpretation f).evalPath q p = (mapInterpretation f).evalPath q r := by
  cases h with
  | @identity n σ i x hx =>
      exact (map_eval_arrow f σ i i hx hx ((eId SSet.{u} i).app q PUnit.unit)).trans
        ((_root_.Quotient.sound (Closure.relation
          (Equations.identity q (f.app (op n) σ) i (vertex_image f σ i hx)))).trans
            ((mapInterpretation f).evalPath_nil q x).symm)
  | @composition n σ i j k x y z hx hy hz a b =>
      subst_vars
      let pi := arrowPath K σ i j rfl rfl a
      let pj := arrowPath K σ j k rfl rfl b
      let li := arrowPath L (f.app (op n) σ) i j (vertex_image f σ i rfl) (vertex_image f σ j rfl) a
      let lj := arrowPath L (f.app (op n) σ) j k (vertex_image f σ j rfl) (vertex_image f σ k rfl) b
      let c := (eComp SSet.{u} (C := realization L) (f.app (op ⦋0⦌) (vertex K σ i))
        (f.app (op ⦋0⦌) (vertex K σ j)) (f.app (op ⦋0⦌) (vertex K σ k))).app q
      have hi := map_eval_arrow f σ i j rfl rfl a
      have hj := map_eval_arrow f σ j k rfl rfl b
      have hcomp : _root_.Quotient.mk _ (arrowPath L (f.app (op n) σ) i k
          (vertex_image f σ i rfl) (vertex_image f σ k rfl) ((eComp SSet.{u} i j k).app q (a, b))) =
            c (_root_.Quotient.mk _ li, _root_.Quotient.mk _ lj) :=
        _root_.Quotient.sound (Closure.relation (Equations.composition q (f.app (op n) σ)
          i j k (vertex_image f σ i rfl) (vertex_image f σ j rfl) (vertex_image f σ k rfl) a b))
      have hpair : c (_root_.Quotient.mk _ li, _root_.Quotient.mk _ lj) =
          c ((mapInterpretation f).evalPath q pi, (mapInterpretation f).evalPath q pj) :=
        congrArg (fun t => c t) (Prod.ext hi.symm hj.symm)
      exact (map_eval_arrow f σ i k rfl rfl ((eComp SSet.{u} i j k).app q (a, b))).trans
        (hcomp.trans (hpair.trans ((mapInterpretation f).evalPath_comp q pi pj).symm))
  | @operator n m g σ i j x y hx hy a =>
      let τ := f.app (op m) σ
      have hσ : f.app (op n) (K.map g.op σ) = L.map g.op τ := congr($(f.naturality g.op) σ)
      let hx' : vertex L (L.map g.op τ) i = f.app (op ⦋0⦌) x :=
        (congrArg (fun σ => vertex L σ i) hσ).symm.trans (vertex_image f (K.map g.op σ) i hx)
      let hy' : vertex L (L.map g.op τ) j = f.app (op ⦋0⦌) y :=
        (congrArg (fun σ => vertex L σ j) hσ).symm.trans (vertex_image f (K.map g.op σ) j hy)
      have hpath := congrArg (fun p => _root_.Quotient.mk
        (congruence (relations L) q (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) p)
          (arrowPath_simplex_congr L hσ i j
            (vertex_image f (K.map g.op σ) i hx) (vertex_image f (K.map g.op σ) j hy) hx' hy' a)
      have hrel : _root_.Quotient.mk
          (congruence (relations L) q (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
          (arrowPath L (L.map g.op τ) i j hx' hy' a) =
          _root_.Quotient.mk
          (congruence (relations L) q (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
          (arrowPath L τ ((coherentSimplexMap g).obj i) ((coherentSimplexMap g).obj j)
            ((vertex_operator L g τ i).symm.trans hx') ((vertex_operator L g τ j).symm.trans hy')
              (((coherentSimplexMap g).map i j).app q a)) :=
        _root_.Quotient.sound (Closure.relation (Equations.operator q g τ i j hx' hy' a))
      exact (map_eval_arrow f (K.map g.op σ) i j hx hy a).trans (hpath.trans (hrel.trans
        (map_eval_arrow f σ ((coherentSimplexMap g).obj i) ((coherentSimplexMap g).obj j)
          ((vertex_operator K g σ i).symm.trans hx) ((vertex_operator K g σ j).symm.trans hy)
            (((coherentSimplexMap g).map i j).app q a)).symm))

/-- The genuine enriched realization map on all whole original coherent Hom paths. -/
def realizationMap {K L : SSet.{u}} (f : K ⟶ L) : realization K ⟶ realization L :=
  (mapInterpretation f).descend (relations K) (map_relations f)

/-- The actual realization map has exactly the original map on individual vertices. -/
theorem realizationMap_obj {K L : SSet.{u}} (f : K ⟶ L) (x : K _⦋0⦌) :
    (realizationMap f).obj x = f.app (op ⦋0⦌) x := rfl

/-- Whole inserted coherent Homs commute with the original realization map and its actual
endpoint equations. -/
theorem realizationMap_simplexHom {K L : SSet.{u}} (f : K ⟶ L) {n : SimplexCategory}
    (σ : K.obj (op n)) (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y) :
    simplexHom K σ i j hx hy ≫ (realizationMap f).map x y =
      simplexHom L (f.app (op n) σ) i j (vertex_image f σ i hx) (vertex_image f σ j hy) := by
  ext q a
  exact map_eval_arrow f σ i j hx hy a

end CategoryTheory.CoherentRealization
