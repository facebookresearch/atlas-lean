/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidUnit

/-!
# Realization fundamental-groupoid unit tests

These tests pin the vertex and edge triangle formulas, the comparison
components, and the based injectivity equivalence.  They make no claim that
the unit map is faithful or a weak equivalence.
-/

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet

example (X : SSet.{u}) (x : X _⦋0⦌) :
    TopCat.toSSetObj₀Equiv
        ((sSetTopAdj.unit.app X).app (Opposite.op ⦋0⦌) x) =
      SSet.realizedVertex x :=
  SSet.toSSetObj₀Equiv_unit_app X x

example (X : SSet.{u}) {x y : X _⦋0⦌} (e : X.Edge x y)
    (t : TopCat.I.{u}) :
    sSetTopAdj.counit.app (SSet.toTop.obj X)
        ((SSet.realizedEdgePath
          (e.map (sSetTopAdj.unit.app X))).hom t) =
      (SSet.realizedEdgePath e).hom t :=
  SSet.realizationUnit_realizedEdgePath_apply X e t

example (X : SSet.{u}) :
    SSet.mapFundamentalGroupoid (sSetTopAdj.unit.app X) ⋙
        TopCat.singularFundamentalGroupoidFunctor (SSet.toTop.obj X) ≅
      SSet.realizationFundamentalGroupoidFunctor X :=
  SSet.realizationFundamentalGroupoidUnitComparison X

example (X : SSet.{u}) (x : X _⦋0⦌) :
    (SSet.realizationFundamentalGroupoidUnitComparison X).hom.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom
        (SSet.realizationFundamentalGroupoidUnitComposite_obj_mk_eq X x) := by
  simp

example (X : SSet.{u}) (x : X _⦋0⦌) :
    (SSet.realizationFundamentalGroupoidUnitComparison X).inv.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom
        (SSet.realizationFundamentalGroupoidUnitComposite_obj_mk_eq X x).symm := by
  simp

example (X : SSet.{u}) {x y : X _⦋0⦌} (e : X.Edge x y) :
    (SSet.realizationFundamentalGroupoidUnitComposite X).map
          (SSet.FundamentalGroupoid.homMk e) ≫
        (SSet.realizationFundamentalGroupoidUnitComparison X).hom.app
          (SSet.FundamentalGroupoid.mk y) =
      (SSet.realizationFundamentalGroupoidUnitComparison X).hom.app
          (SSet.FundamentalGroupoid.mk x) ≫
        (SSet.realizationFundamentalGroupoidFunctor X).map
          (SSet.FundamentalGroupoid.homMk e) :=
  SSet.realizationFundamentalGroupoidUnitComparison_hom_naturality_homMk X e

example (X : SSet.{u}) (z : X _⦋0⦌) :
    Function.Injective
        ((SSet.realizationFundamentalGroupoidFunctor X).mapEnd
          (SSet.FundamentalGroupoid.mk z)) ↔
      Function.Injective
        ((SSet.mapFundamentalGroupoid (sSetTopAdj.unit.app X)).mapEnd
          (SSet.FundamentalGroupoid.mk z)) :=
  SSet.realizationFundamentalGroupoid_mapEnd_injective_iff_unit X z

end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
