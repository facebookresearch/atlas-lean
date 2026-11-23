/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedByCounit

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Topology

namespace CompactlyGenerated.GeneratedByCounitTests

#check CompactlyGenerated.adj_counit_app_eq_generatedBy
#check CompactlyGenerated.adjCounit_apply

#check @CompactlyGenerated.adj_counit_app_eq_generatedBy.{0, 0}
#check @CompactlyGenerated.adj_counit_app_eq_generatedBy.{1, 1}
#check @CompactlyGenerated.adj_counit_app_eq_generatedBy.{0, 1}
#check @CompactlyGenerated.adjCounit_apply.{0, 0}
#check @CompactlyGenerated.adjCounit_apply.{1, 1}
#check @CompactlyGenerated.adjCounit_apply.{0, 1}

section Factors

variable (Y : TopCat.{v})

example :
    let P := CompactlyGenerated.compactHausProbes.{u}
    let e := CompactlyGenerated.equivalenceGeneratedByTopCat.{u, v}
    let T := TopCat.toGeneratedByTopCat (X := P)
    let U := GeneratedByTopCat.toTopCat (X := P)
    let eToTop : e.functor ⋙ U ≅
      CompactlyGenerated.compactlyGeneratedToTop := Iso.refl _
    CompactlyGenerated.adj.counit.app Y =
      eToTop.inv.app ((T ⋙ e.inverse).obj Y) ≫
        U.map (e.counitIso.hom.app (T.obj Y)) ≫
          (GeneratedByTopCat.adjCounit (X := P)).app Y :=
  CompactlyGenerated.adj_counit_app_eq_generatedBy Y

example :
    let P := CompactlyGenerated.compactHausProbes.{u}
    let e := CompactlyGenerated.equivalenceGeneratedByTopCat.{u, v}
    let T := TopCat.toGeneratedByTopCat (X := P)
    let U := GeneratedByTopCat.toTopCat (X := P)
    compactlyGeneratedToTop.obj ((T ⋙ e.inverse).obj Y) ⟶
      (e.functor ⋙ U).obj ((T ⋙ e.inverse).obj Y) :=
  by
    dsimp only
    let P := CompactlyGenerated.compactHausProbes.{u}
    let e := CompactlyGenerated.equivalenceGeneratedByTopCat.{u, v}
    let U := GeneratedByTopCat.toTopCat (X := P)
    let eToTop : e.functor ⋙ U ≅
        CompactlyGenerated.compactlyGeneratedToTop := Iso.refl _
    exact eToTop.inv.app _

example :
    let P := CompactlyGenerated.compactHausProbes.{u}
    let e := CompactlyGenerated.equivalenceGeneratedByTopCat.{u, v}
    let T := TopCat.toGeneratedByTopCat (X := P)
    let U := GeneratedByTopCat.toTopCat (X := P)
    (e.functor ⋙ U).obj (e.inverse.obj (T.obj Y)) ⟶ U.obj (T.obj Y) :=
  by
    dsimp only
    exact GeneratedByTopCat.toTopCat.map
      (CompactlyGenerated.equivalenceGeneratedByTopCat.counitIso.hom.app _)

example :
    let P := CompactlyGenerated.compactHausProbes.{u}
    let T := TopCat.toGeneratedByTopCat (X := P)
    let U := GeneratedByTopCat.toTopCat (X := P)
    U.obj (T.obj Y) ⟶ Y :=
  by
    dsimp only
    exact (GeneratedByTopCat.adjCounit
      (X := CompactlyGenerated.compactHausProbes.{u})).app Y

example :
    let P := CompactlyGenerated.compactHausProbes.{u}
    let e := CompactlyGenerated.equivalenceGeneratedByTopCat.{u, v}
    let T := TopCat.toGeneratedByTopCat (X := P)
    let U := GeneratedByTopCat.toTopCat (X := P)
    let eToTop : e.functor ⋙ U ≅
      CompactlyGenerated.compactlyGeneratedToTop := Iso.refl _
    IsIso (eToTop.inv.app ((T ⋙ e.inverse).obj Y)) := by
  dsimp only
  let P := CompactlyGenerated.compactHausProbes.{u}
  let e := CompactlyGenerated.equivalenceGeneratedByTopCat.{u, v}
  let U := GeneratedByTopCat.toTopCat (X := P)
  let eToTop : e.functor ⋙ U ≅
      CompactlyGenerated.compactlyGeneratedToTop := Iso.refl _
  change IsIso (eToTop.inv.app _)
  infer_instance

example :
    let P := CompactlyGenerated.compactHausProbes.{u}
    let e := CompactlyGenerated.equivalenceGeneratedByTopCat.{u, v}
    let T := TopCat.toGeneratedByTopCat (X := P)
    let U := GeneratedByTopCat.toTopCat (X := P)
    IsIso (U.map (e.counitIso.hom.app (T.obj Y))) := by
  dsimp only
  infer_instance

end Factors

example (Y : TopCat.{v}) (y : Y) :
    CompactlyGenerated.adj.counit.app Y y = y :=
  @CompactlyGenerated.adjCounit_apply.{v, u} Y y

#print axioms CompactlyGenerated.adj_counit_app_eq_generatedBy
#print axioms CompactlyGenerated.adjCounit_apply

end CompactlyGenerated.GeneratedByCounitTests
