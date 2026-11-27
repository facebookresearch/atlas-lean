/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMap
public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Continuous realization of a simplicial homotopy

A simplicial cylinder homotopy from `f : X → Y` to `g : X → Y` realizes to a
continuous-map homotopy from `|f|` to `|g|`. Its cylinder has interval parameter
first, with endpoint zero the realized source map and endpoint one the realized
target map, in every realization universe.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

/--
A simplicial homotopy from `f` to `g` gives a continuous-map homotopy from
`|f|` to `|g|`, with the same ordered endpoints.
-/
noncomputable def realizeHomotopy (X Y : SSet.{u}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    ContinuousMap.Homotopy (SSet.toTop.map f).hom (SSet.toTop.map g).hom where
  toFun p :=
    SSet.realizeHomotopyMap X Y f g H
      ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv
        (TopCat.I.homeomorph.symm p.1, p.2))
  continuous_toFun :=
    (SSet.realizeHomotopyMap X Y f g H).hom.continuous.comp
      ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv.hom.continuous.comp
        ((TopCat.I.homeomorph.symm.continuous.comp continuous_fst).prodMk
          continuous_snd))
  map_zero_left x := by
    have h0 := SSet.realizeHomotopyMap_zero X Y f g H
    have hx := ConcreteCategory.congr_hom h0 x
    have hs0 : TopCat.I.homeomorph.symm (0 : unitInterval) = (0 : TopCat.I) := rfl
    have hpt : (TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv
        (TopCat.I.homeomorph.symm (0 : unitInterval), x) =
        (Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj X))) x := by
      apply Limits.Concrete.limit_ext
      rintro ⟨⟨⟩⟩
      · change (Limits.prod.fst : TopCat.I ⨯ SSet.toTop.obj X ⟶ TopCat.I) _ =
          (Limits.prod.fst : TopCat.I ⨯ SSet.toTop.obj X ⟶ TopCat.I) _
        change ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv ≫
          Limits.prod.fst) _ = ((Limits.prod.lift
          (TopCat.const (0 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj X))) ≫ Limits.prod.fst) _
        rw [TopCat.prodIsoProd_inv_fst, Limits.prod.lift_fst]
        exact hs0
      · change (Limits.prod.snd : TopCat.I ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj X) _ =
          (Limits.prod.snd : TopCat.I ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj X) _
        change ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv ≫
          Limits.prod.snd) _ = ((Limits.prod.lift
          (TopCat.const (0 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj X))) ≫ Limits.prod.snd) _
        rw [TopCat.prodIsoProd_inv_snd, Limits.prod.lift_snd]
        exact rfl
    change SSet.realizeHomotopyMap X Y f g H
      ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv
        (TopCat.I.homeomorph.symm (0 : unitInterval), x)) = _
    rw [hpt]
    exact hx
  map_one_left x := by
    have h1 := SSet.realizeHomotopyMap_one X Y f g H
    have hx := ConcreteCategory.congr_hom h1 x
    have hs1 : TopCat.I.homeomorph.symm (1 : unitInterval) = (1 : TopCat.I) := rfl
    have hpt : (TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv
        (TopCat.I.homeomorph.symm (1 : unitInterval), x) =
        (Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj X))) x := by
      apply Limits.Concrete.limit_ext
      rintro ⟨⟨⟩⟩
      · change (Limits.prod.fst : TopCat.I ⨯ SSet.toTop.obj X ⟶ TopCat.I) _ =
          (Limits.prod.fst : TopCat.I ⨯ SSet.toTop.obj X ⟶ TopCat.I) _
        change ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv ≫
          Limits.prod.fst) _ = ((Limits.prod.lift
          (TopCat.const (1 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj X))) ≫ Limits.prod.fst) _
        rw [TopCat.prodIsoProd_inv_fst, Limits.prod.lift_fst]
        exact hs1
      · change (Limits.prod.snd : TopCat.I ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj X) _ =
          (Limits.prod.snd : TopCat.I ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj X) _
        change ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv ≫
          Limits.prod.snd) _ = ((Limits.prod.lift
          (TopCat.const (1 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj X))) ≫ Limits.prod.snd) _
        rw [TopCat.prodIsoProd_inv_snd, Limits.prod.lift_snd]
        exact rfl
    change SSet.realizeHomotopyMap X Y f g H
      ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv
        (TopCat.I.homeomorph.symm (1 : unitInterval), x)) = _
    rw [hpt]
    exact hx

end SSet
