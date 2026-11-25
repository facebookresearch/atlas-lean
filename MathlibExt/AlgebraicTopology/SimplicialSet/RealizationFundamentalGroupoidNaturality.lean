/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoid

/-!
# Naturality of the realization fundamental-groupoid functor

For a simplicial map `f : X ⟶ Y`, first mapping the combinatorial
fundamental groupoid and then directly realizing is naturally isomorphic to
first directly realizing and then applying the topological fundamental-
groupoid map induced by `|f|`.

At a represented vertex, the component is the equality isomorphism induced
by `realizedVertex_naturality`.  On an edge generator, naturality is exactly
`realizedEdgePath_naturality_hom`, with endpoint changes handled by equality
isomorphisms.  `SSet.FundamentalGroupoid.natIsoMk` extends this edge leaf to
all morphisms using `SSet.FundamentalGroupoid.hom_rec`.

This comparison does not identify the two functors definitionally, install a
global equivalence instance, or assert extra identity/composition coherence
between different comparison isomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory Simplicial
open scoped Simplicial

universe u

namespace SSet

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-- Equality between the two images of a represented vertex.  Its orientation
is realized mapped vertex to the image under the realized simplicial map. -/
theorem realizationFundamentalGroupoidNaturality_obj_mk_eq
    (x : X _⦋0⦌) :
    (SSet.mapFundamentalGroupoid f ⋙
      SSet.realizationFundamentalGroupoidFunctor Y).obj
        (SSet.FundamentalGroupoid.mk x) =
    (SSet.realizationFundamentalGroupoidFunctor X ⋙
      _root_.FundamentalGroupoid.map (SSet.toTop.map f).hom).obj
        (SSet.FundamentalGroupoid.mk x) := by
  exact congrArg _ (SSet.realizedVertex_naturality f x)

set_option backward.isDefEq.respectTransparency false in
/-- The two induced morphisms are heterogeneously equal on an edge
generator.  This is the path-level naturality leaf before endpoint casts. -/
private theorem realizationFundamentalGroupoidNaturality_map_homMk_heq
    {x y : X _⦋0⦌} (e : X.Edge x y) :
    (SSet.mapFundamentalGroupoid f ⋙
      SSet.realizationFundamentalGroupoidFunctor Y).map
        (SSet.FundamentalGroupoid.homMk e) ≍
    (SSet.realizationFundamentalGroupoidFunctor X ⋙
      _root_.FundamentalGroupoid.map (SSet.toTop.map f).hom).map
        (SSet.FundamentalGroupoid.homMk e) := by
  dsimp only [Functor.comp_map]
  rw [SSet.mapFundamentalGroupoid_map_homMk]
  change (SSet.realizationFundamentalGroupoidFunctor Y).map
      (SSet.FundamentalGroupoid.homMk (e.map f)) ≍
    (_root_.FundamentalGroupoid.map (SSet.toTop.map f).hom).map
      ((SSet.realizationFundamentalGroupoidFunctor X).map
        (SSet.FundamentalGroupoid.homMk e))
  rw [SSet.realizationFundamentalGroupoidFunctor_map_homMk,
    SSet.realizationFundamentalGroupoidFunctor_map_homMk]
  change Path.Homotopic.Quotient.mk
      (TopCat.pathEquiv (SSet.realizedEdgePath (e.map f))) ≍
    Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk
        (TopCat.pathEquiv (SSet.realizedEdgePath e)))
      (SSet.toTop.map f).hom
  rw [← Path.Homotopic.Quotient.mk_map]
  apply Path.Homotopic.hpath_hext
  intro t
  exact ConcreteCategory.congr_hom
    (SSet.realizedEdgePath_naturality_hom f e)
    (TopCat.I.homeomorph.symm t)

/-- Direct realization of fundamental groupoids is natural under a simplicial
map, with the vertex equality made explicit as an equality isomorphism. -/
noncomputable def realizationFundamentalGroupoidNaturality :
    SSet.mapFundamentalGroupoid f ⋙
        SSet.realizationFundamentalGroupoidFunctor Y ≅
      SSet.realizationFundamentalGroupoidFunctor X ⋙
        _root_.FundamentalGroupoid.map (SSet.toTop.map f).hom :=
  SSet.FundamentalGroupoid.natIsoMk
    (fun x ↦ eqToIso
      (realizationFundamentalGroupoidNaturality_obj_mk_eq f x))
    (fun {x y} e ↦ by
      let hx := realizationFundamentalGroupoidNaturality_obj_mk_eq f x
      let hy := realizationFundamentalGroupoidNaturality_obj_mk_eq f y
      apply (cancel_mono (eqToIso hy).inv).1
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      apply (conj_eqToHom_iff_heq _ _ hx hy).2
      exact realizationFundamentalGroupoidNaturality_map_homMk_heq f e)

/-- Component formula at a represented simplicial vertex. -/
@[simp]
theorem realizationFundamentalGroupoidNaturality_app_mk
    (x : X _⦋0⦌) :
    (realizationFundamentalGroupoidNaturality f).hom.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom (realizationFundamentalGroupoidNaturality_obj_mk_eq f x) :=
  rfl

/-- Naturality on an edge generator, with source and target equality
components displayed in their canonical order. -/
theorem realizationFundamentalGroupoidNaturality_hom_naturality_homMk
    {x y : X _⦋0⦌} (e : X.Edge x y) :
    (SSet.mapFundamentalGroupoid f ⋙
        SSet.realizationFundamentalGroupoidFunctor Y).map
          (SSet.FundamentalGroupoid.homMk e) ≫
      (realizationFundamentalGroupoidNaturality f).hom.app
        (SSet.FundamentalGroupoid.mk y) =
    (realizationFundamentalGroupoidNaturality f).hom.app
        (SSet.FundamentalGroupoid.mk x) ≫
      (SSet.realizationFundamentalGroupoidFunctor X ⋙
        _root_.FundamentalGroupoid.map
          (SSet.toTop.map f).hom).map
            (SSet.FundamentalGroupoid.homMk e) :=
  (realizationFundamentalGroupoidNaturality f).hom.naturality _

end SSet

end
