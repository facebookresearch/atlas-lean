/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid

/-!
# Fundamental groupoids and the realization--singular unit

The fundamental-groupoid map induced by the realization--singular unit,
followed by the singular comparison, is naturally isomorphic to direct
geometric realization.  Consequently, injectivity on a based endomorphism
monoid for realization is equivalent to injectivity for the unit map.

This file does not prove that the unit is faithful, a weak equivalence, or a
realization equivalence, and makes no Waldhausen, additivity, or K-theory
claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

/-- The singular vertex obtained from the realization unit represents the
original realized vertex. -/
theorem toSSetObj₀Equiv_unit_app
    (X : SSet.{u}) (x : X _⦋0⦌) :
    TopCat.toSSetObj₀Equiv
        ((sSetTopAdj.unit.app X).app (Opposite.op ⦋0⦌) x) =
      SSet.realizedVertex x := by
  calc
    TopCat.toSSetObj₀Equiv
        ((sSetTopAdj.unit.app X).app (Opposite.op ⦋0⦌) x) =
        sSetTopAdj.counit.app (SSet.toTop.obj X)
          (SSet.realizedVertex
            ((sSetTopAdj.unit.app X).app (Opposite.op ⦋0⦌) x)) :=
      (TopCat.counit_realizedVertex _).symm
    _ = sSetTopAdj.counit.app (SSet.toTop.obj X)
        (SSet.toTop.map (sSetTopAdj.unit.app X)
          (SSet.realizedVertex x)) := by
      rw [SSet.realizedVertex_naturality]
    _ = SSet.realizedVertex x := by
      have h := ConcreteCategory.congr_hom
        (sSetTopAdj.left_triangle_components X)
        (SSet.realizedVertex x)
      simpa only [Functor.comp_obj, Functor.comp_map,
        ConcreteCategory.comp_apply, CategoryTheory.id_apply] using h

/-- Pointwise edge compatibility for the realization--singular unit and
counit.  This is the edge part of the adjunction triangle. -/
theorem realizationUnit_realizedEdgePath_apply
    (X : SSet.{u}) {x y : X _⦋0⦌} (e : X.Edge x y)
    (t : TopCat.I.{u}) :
    sSetTopAdj.counit.app (SSet.toTop.obj X)
        ((SSet.realizedEdgePath
          (e.map (sSetTopAdj.unit.app X))).hom t) =
      (SSet.realizedEdgePath e).hom t := by
  have hnat := ConcreteCategory.congr_hom
    (SSet.realizedEdgePath_naturality_hom
      (sSetTopAdj.unit.app X) e) t
  rw [hnat]
  have htriangle := ConcreteCategory.congr_hom
    (sSetTopAdj.left_triangle_components X)
    ((SSet.realizedEdgePath e).hom t)
  simpa only [TopCat.hom_comp, ContinuousMap.comp_apply,
    Functor.comp_obj, Functor.comp_map, CategoryTheory.id_apply] using htriangle

abbrev realizationFundamentalGroupoidUnitComposite (X : SSet.{u}) :=
  SSet.mapFundamentalGroupoid (sSetTopAdj.unit.app X) ⋙
    TopCat.singularFundamentalGroupoidFunctor (SSet.toTop.obj X)

theorem realizationFundamentalGroupoidUnitComposite_obj_mk_eq
    (X : SSet.{u}) (x : X _⦋0⦌) :
    (realizationFundamentalGroupoidUnitComposite X).obj
        (SSet.FundamentalGroupoid.mk x) =
      (SSet.realizationFundamentalGroupoidFunctor X).obj
        (SSet.FundamentalGroupoid.mk x) := by
  apply _root_.FundamentalGroupoid.ext
  change sSetTopAdj.counit.app (SSet.toTop.obj X)
      (SSet.realizedVertex
        ((sSetTopAdj.unit.app X).app (Opposite.op ⦋0⦌) x)) =
    SSet.realizedVertex x
  exact (TopCat.counit_realizedVertex _).trans
    (SSet.toSSetObj₀Equiv_unit_app X x)

/-- On an edge generator, the unit--singular composite and direct
realization give heterogeneously equal fundamental-groupoid morphisms. -/
theorem realizationUnitComposite_map_homMk_heq
    (X : SSet.{u}) {x y : X _⦋0⦌} (e : X.Edge x y) :
    (realizationFundamentalGroupoidUnitComposite X).map
        (SSet.FundamentalGroupoid.homMk e) ≍
      (SSet.realizationFundamentalGroupoidFunctor X).map
        (SSet.FundamentalGroupoid.homMk e) := by
  dsimp [realizationFundamentalGroupoidUnitComposite,
    TopCat.singularFundamentalGroupoidFunctor]
  rw [SSet.mapFundamentalGroupoid_map_homMk]
  change (_root_.FundamentalGroupoid.map
      (sSetTopAdj.counit.app (SSet.toTop.obj X)).hom).map
        ((SSet.realizationFundamentalGroupoidFunctor
          (TopCat.toSSet.obj (SSet.toTop.obj X))).map
            (SSet.FundamentalGroupoid.homMk
              (e.map (sSetTopAdj.unit.app X)))) ≍ _
  rw [SSet.realizationFundamentalGroupoidFunctor_map_homMk,
    SSet.realizationFundamentalGroupoidFunctor_map_homMk]
  apply Path.Homotopic.hpath_hext
  intro t
  exact SSet.realizationUnit_realizedEdgePath_apply X e
    (TopCat.I.homeomorph.symm t)

/-- Factoring direct realization through the realization--singular unit and
the singular fundamental-groupoid comparison. -/
noncomputable def realizationFundamentalGroupoidUnitComparison
    (X : SSet.{u}) :
    SSet.mapFundamentalGroupoid (sSetTopAdj.unit.app X) ⋙
        TopCat.singularFundamentalGroupoidFunctor (SSet.toTop.obj X) ≅
      SSet.realizationFundamentalGroupoidFunctor X :=
  SSet.FundamentalGroupoid.natIsoMk
    (fun x ↦ eqToIso
      (realizationFundamentalGroupoidUnitComposite_obj_mk_eq X x))
    (fun {x y} e ↦ by
      let hx := realizationFundamentalGroupoidUnitComposite_obj_mk_eq X x
      let hy := realizationFundamentalGroupoidUnitComposite_obj_mk_eq X y
      apply (cancel_mono (eqToIso hy).inv).1
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      apply (conj_eqToHom_iff_heq _ _ hx hy).2
      exact SSet.realizationUnitComposite_map_homMk_heq X e)

/-- Formula for the comparison component at a represented vertex. -/
@[simp]
theorem realizationFundamentalGroupoidUnitComparison_hom_app_mk
    (X : SSet.{u}) (x : X _⦋0⦌) :
    (realizationFundamentalGroupoidUnitComparison X).hom.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom
        (realizationFundamentalGroupoidUnitComposite_obj_mk_eq X x) :=
  rfl

/-- Formula for the inverse comparison component at a represented vertex. -/
@[simp]
theorem realizationFundamentalGroupoidUnitComparison_inv_app_mk
    (X : SSet.{u}) (x : X _⦋0⦌) :
    (realizationFundamentalGroupoidUnitComparison X).inv.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom
        (realizationFundamentalGroupoidUnitComposite_obj_mk_eq X x).symm :=
  rfl

/-- Naturality of the comparison on an edge generator, with the source and
target components displayed in their canonical order. -/
theorem realizationFundamentalGroupoidUnitComparison_hom_naturality_homMk
    (X : SSet.{u}) {x y : X _⦋0⦌} (e : X.Edge x y) :
    (realizationFundamentalGroupoidUnitComposite X).map
          (SSet.FundamentalGroupoid.homMk e) ≫
        (realizationFundamentalGroupoidUnitComparison X).hom.app
          (SSet.FundamentalGroupoid.mk y) =
      (realizationFundamentalGroupoidUnitComparison X).hom.app
          (SSet.FundamentalGroupoid.mk x) ≫
        (SSet.realizationFundamentalGroupoidFunctor X).map
          (SSet.FundamentalGroupoid.homMk e) :=
  (realizationFundamentalGroupoidUnitComparison X).hom.naturality _

/-- Based injectivity for direct realization is equivalent to based
injectivity for the realization--singular unit.  The singular comparison is
fully faithful, and the remaining difference is conjugation by the comparison
component. -/
theorem realizationFundamentalGroupoid_mapEnd_injective_iff_unit
    (X : SSet.{u}) (z : X _⦋0⦌) :
    Function.Injective
        ((SSet.realizationFundamentalGroupoidFunctor X).mapEnd
          (SSet.FundamentalGroupoid.mk z)) ↔
      Function.Injective
        ((SSet.mapFundamentalGroupoid (sSetTopAdj.unit.app X)).mapEnd
          (SSet.FundamentalGroupoid.mk z)) := by
  let U := SSet.mapFundamentalGroupoid (sSetTopAdj.unit.app X)
  let S := TopCat.singularFundamentalGroupoidFunctor (SSet.toTop.obj X)
  let R := SSet.realizationFundamentalGroupoidFunctor X
  let η := SSet.realizationFundamentalGroupoidUnitComparison X
  let hS := TopCat.singularFundamentalGroupoidFunctor_fullyFaithful
    (SSet.toTop.obj X)
  constructor
  · intro hR f g hfg
    apply hR
    apply End.ext
    apply (cancel_epi (η.hom.app (SSet.FundamentalGroupoid.mk z))).1
    change η.hom.app (SSet.FundamentalGroupoid.mk z) ≫ R.map f.asHom =
      η.hom.app (SSet.FundamentalGroupoid.mk z) ≫ R.map g.asHom
    rw [← η.hom.naturality f.asHom, ← η.hom.naturality g.asHom]
    change S.map (U.map f.asHom) ≫ _ = S.map (U.map g.asHom) ≫ _
    exact congrArg (fun k ↦ S.map k ≫ η.hom.app _) (congrArg End.asHom hfg)
  · intro hU f g hfg
    apply hU
    apply End.ext
    apply hS.map_injective
    apply (cancel_mono (η.hom.app (SSet.FundamentalGroupoid.mk z))).1
    change (U ⋙ S).map f.asHom ≫
        η.hom.app (SSet.FundamentalGroupoid.mk z) =
      (U ⋙ S).map g.asHom ≫
        η.hom.app (SSet.FundamentalGroupoid.mk z)
    rw [η.hom.naturality f.asHom, η.hom.naturality g.asHom]
    exact congrArg (fun k ↦ η.hom.app _ ≫ k) (congrArg End.asHom hfg)

end SSet

end
