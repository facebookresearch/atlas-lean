/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUniverseLift

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u v

variable (X : SSet.{u}) (x : X _⦋0⦌)

example : SSet.toTop.obj (SSet.uliftFunctor.{v, u}.obj X) ≅
    TopCat.uliftFunctor.{v, u}.obj (SSet.toTop.obj X) :=
  SSet.toTopULiftIso.{u, v}.app X

example :
    (SSet.toTopULiftIso.{u, v}.hom.app X) (SSet.realizedVertex (ULift.up x)) =
      (ULift.up (SSet.realizedVertex x) : TopCat.uliftFunctor.{v, u}.obj (SSet.toTop.obj X)) :=
  SSet.toTopULiftIso_hom_realizedVertex.{u, v} X x

example :
    (SSet.toTopULiftIso.{u, v}.inv.app X)
        (ULift.up (SSet.realizedVertex x) : TopCat.uliftFunctor.{v, u}.obj (SSet.toTop.obj X)) =
      SSet.realizedVertex (ULift.up x : (SSet.uliftFunctor.{v, u}.obj X) _⦋0⦌) :=
  SSet.toTopULiftIso_inv_realizedVertex.{u, v} X x

end
