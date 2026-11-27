/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationFiniteProductComparisonArbitrary
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationProductComparisonBraid

/-!
# Realized cylinder map and its interval endpoints

For a simplicial homotopy from `f` to `g`, realization gives a continuous map
`I × |X| → |Y|`, using the interval realization and the interval-times-space
product comparison. At time zero it is `|f|`; at time one it is `|g|`.

The interval endpoints correspond to simplicial inclusions `ι₀` and `ι₁`,
respectively: face `d₁` gives the zero vertex and face `d₀` gives the one vertex.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial MonoidalCategory

open scoped Simplicial

namespace SSet

/--
The continuous map `I × |X| → |Y|` associated to a simplicial homotopy from
`f` to `g`, with the interval as its first factor.
-/
noncomputable def realizeHomotopyMap (X Y : SSet.{u}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj Y := by
  haveI : IsIso (Limits.prodComparison SSet.toTop (Δ[1] : SSet.{u}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  have hIsoP : IsIso (Limits.prodComparison SSet.toTop X (Δ[1] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap _ _
  let hBridgeIso : ((Limits.prod.functor.obj X).obj (Δ[1] : SSet.{u})) ≅ (X ⨯ (Δ[1] : SSet.{u})) :=
    Iso.refl (X ⨯ (Δ[1] : SSet.{u}))
  exact (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
    Limits.prod.map (𝟙 (SSet.toTop.obj X))
      SSet.stdSimplex.toTopObjIsoI.inv ≫
    (@asIso _ _ _ _ (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{u})) hIsoP).inv ≫
    SSet.toTop.map hBridgeIso.inv ≫
    SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
    SSet.toTop.map H.h

/--
Restricting the realized cylinder map to time zero gives the realized map `|f|`.
-/
theorem realizeHomotopyMap_zero (X Y : SSet.{u}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
      (𝟙 (SSet.toTop.obj X)) ≫
      realizeHomotopyMap X Y f g H =
      SSet.toTop.map f := by
  let _ : IsIso (Limits.prodComparison SSet.toTop (Δ[1] : SSet.{u}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  have hIsoP : IsIso (Limits.prodComparison SSet.toTop X (Δ[1] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap _ _
  have hPinvHom : Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{u}) ≫
        (@asIso _ _ _ _ (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u})) hIsoP).inv =
    𝟙 (SSet.toTop.obj (X ⨯ (Δ[1] : SSet.{u}))) :=
    @IsIso.hom_inv_id _ _ _ _ _ hIsoP
  have hTC :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u}) =
    𝟙 (X ⊗ (Δ[1] : SSet.{u})) :=
    Iso.hom_inv_id_app (CartesianMonoidalCategory.tensorLeftIsoProd X) (Δ[1] : SSet.{u})
  have hIota : SSet.ι₀ (X := X) =
    (SSet.ι₀ ≫ (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u})) ≫
      (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u}) := by
    rw [Category.assoc, hTC, Category.comp_id]
  let hBridgeIso : ((Limits.prod.functor.obj X).obj (Δ[1] : SSet.{u})) ≅ (X ⨯ (Δ[1] : SSet.{u})) :=
    Iso.refl (X ⨯ (Δ[1] : SSet.{u}))
  have hHomFst :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
        (hBridgeIso.hom ≫ Limits.prod.fst) =
      CartesianMonoidalCategory.fst X (Δ[1] : SSet.{u}) := by
    have hBridge : hBridgeIso.hom ≫ Limits.prod.fst = Limits.prod.fst :=
      Category.id_comp Limits.prod.fst
    calc (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
      (hBridgeIso.hom ≫ Limits.prod.fst)
        = (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
          Limits.prod.fst := by
          rw [hBridge]
      _ = CartesianMonoidalCategory.fst X (Δ[1] : SSet.{u}) :=
          IsLimit.conePointUniqueUpToIso_hom_comp
            (CartesianMonoidalCategory.tensorProductIsBinaryProduct X (Δ[1] : SSet.{u}))
            (Limits.limit.isLimit _) ⟨.left⟩
  have hHomSnd :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
        (hBridgeIso.hom ≫ Limits.prod.snd) =
      CartesianMonoidalCategory.snd X (Δ[1] : SSet.{u}) := by
    have hBridge : hBridgeIso.hom ≫ Limits.prod.snd = Limits.prod.snd :=
      Category.id_comp Limits.prod.snd
    calc (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
      (hBridgeIso.hom ≫ Limits.prod.snd)
        = (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
          Limits.prod.snd := by
          rw [hBridge]
      _ = CartesianMonoidalCategory.snd X (Δ[1] : SSet.{u}) :=
          IsLimit.conePointUniqueUpToIso_hom_comp
            (CartesianMonoidalCategory.tensorProductIsBinaryProduct X (Δ[1] : SSet.{u}))
            (Limits.limit.isLimit _) ⟨.right⟩
  have hProd : (Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
      (𝟙 (SSet.toTop.obj X)) ≫
      (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
      Limits.prod.map (𝟙 (SSet.toTop.obj X))
        SSet.stdSimplex.toTopObjIsoI.inv) =
      SSet.toTop.map
        (SSet.ι₀ ≫ (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map hBridgeIso.hom ≫
        Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u}) := by
    apply Limits.prod.hom_ext
    · simp only [Category.assoc, Limits.prod.map_fst, Limits.prod.lift_fst,
        Limits.prod.braiding_hom, Limits.prod.lift_fst, Limits.prod.lift_snd,
        Category.comp_id, Limits.prodComparison_fst,
        Limits.prod.lift_fst, SSet.ι₀_fst, ← Functor.map_comp,
        hHomFst, hBridgeIso]
      exact (SSet.toTop.map_id _).symm
    · have hRedZero : ((Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj X)) ≫
          (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
          Limits.prod.map (𝟙 (SSet.toTop.obj X))
            SSet.stdSimplex.toTopObjIsoI.inv) ≫ Limits.prod.snd) =
          TopCat.const (0 : TopCat.I.{u}) ≫ SSet.stdSimplex.toTopObjIsoI.inv := by
        calc ((Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫
              (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
              Limits.prod.map (𝟙 (SSet.toTop.obj X))
                SSet.stdSimplex.toTopObjIsoI.inv) ≫ Limits.prod.snd)
            _ = Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫
              (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
              (Limits.prod.map (𝟙 (SSet.toTop.obj X))
                SSet.stdSimplex.toTopObjIsoI.inv ≫ Limits.prod.snd) := by
              rw [Category.assoc, Category.assoc]
            _ = Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫
              (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
              (Limits.prod.snd ≫ SSet.stdSimplex.toTopObjIsoI.inv) := by
              rw [Limits.prod.map_snd]
            _ = Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫
              (((Limits.prod.braiding TopCat.I.{u}
                (SSet.toTop.obj X)).hom ≫ Limits.prod.snd) ≫
                SSet.stdSimplex.toTopObjIsoI.inv) := by
              rw [← Category.assoc
                (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom
                Limits.prod.snd SSet.stdSimplex.toTopObjIsoI.inv]
            _ = Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫
              (Limits.prod.fst ≫ SSet.stdSimplex.toTopObjIsoI.inv) := by
              rw [Limits.prod.braiding_hom, Limits.prod.lift_snd]
            _ = (Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫ Limits.prod.fst) ≫
              SSet.stdSimplex.toTopObjIsoI.inv := by
              rw [← Category.assoc
                (Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
                  (𝟙 (SSet.toTop.obj X)))
                Limits.prod.fst SSet.stdSimplex.toTopObjIsoI.inv]
            _ = TopCat.const (0 : TopCat.I.{u}) ≫ SSet.stdSimplex.toTopObjIsoI.inv := by
              rw [Limits.prod.lift_fst]
      rw [hRedZero]
      simp only [Category.assoc,
        Limits.prodComparison_snd,
        SSet.ι₀_snd, ← Functor.map_comp,
        hHomSnd, hBridgeIso]
      ext x
      simp only [TopCat.const_apply, ConcreteCategory.comp_apply]
      rw [SSet.toTopObjIsoI_inv_zero]
      have hFac : SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2) :
          (Δ[1] : SSet.{u}) _⦋0⦌) =
          IsTerminal.from SSet.stdSimplex.isTerminalObj₀ X ≫
            SSet.stdSimplex.δ 1 := by
        rw [SSet.stdSimplex.δ_one_eq_const]
        simp
      rw [hFac, Functor.map_comp]
      exact congrArg (SSet.toTop.map (SSet.stdSimplex.δ 1)) (Subsingleton.elim _ _)
  calc Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
        (𝟙 (SSet.toTop.obj X)) ≫ realizeHomotopyMap X Y f g H
      = (Limits.prod.lift (TopCat.const (0 : TopCat.I.{u}))
        (𝟙 (SSet.toTop.obj X)) ≫
        (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
        Limits.prod.map (𝟙 (SSet.toTop.obj X))
          SSet.stdSimplex.toTopObjIsoI.inv ≫
        (@asIso _ _ _ _ (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u})) hIsoP).inv ≫
        SSet.toTop.map hBridgeIso.inv ≫
        SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map H.h) := by
          unfold realizeHomotopyMap
          simp only [hBridgeIso]
      _ = SSet.toTop.map
        (SSet.ι₀ ≫ (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map hBridgeIso.hom ≫
        Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u}) ≫
        (@asIso _ _ _ _ (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u})) hIsoP).inv ≫
        SSet.toTop.map hBridgeIso.inv ≫
        SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map H.h := by
          exact congrArg (· ≫ (@asIso _ _ _ _ (Limits.prodComparison SSet.toTop
            X (Δ[1] : SSet.{u})) hIsoP).inv ≫
            SSet.toTop.map hBridgeIso.inv ≫
            SSet.toTop.map
              ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
            SSet.toTop.map H.h) hProd
      _ = SSet.toTop.map
        (SSet.ι₀ ≫ (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map H.h := by
          simp only [← Category.assoc, hPinvHom, Category.id_comp,
            ← Functor.map_comp, Iso.hom_inv_id]
      _ =
        SSet.toTop.map
          ((SSet.ι₀ ≫ (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u})) ≫
            (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map H.h := by
          simp only [← Functor.map_comp, Category.assoc]
      _ = SSet.toTop.map (SSet.ι₀ (X := X)) ≫ SSet.toTop.map H.h := by rw [← hIota]
      _ = SSet.toTop.map (SSet.ι₀ (X := X) ≫ H.h) := by
          rw [← Functor.map_comp]
      _ = SSet.toTop.map f := by rw [H.h₀]

/--
Restricting the realized cylinder map to time one gives the realized map `|g|`.
-/
theorem realizeHomotopyMap_one (X Y : SSet.{u}) (f g : X ⟶ Y)
    (H : SSet.Homotopy f g) :
    Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
      (𝟙 (SSet.toTop.obj X)) ≫
      realizeHomotopyMap X Y f g H =
      SSet.toTop.map g := by
  let _ : IsIso (Limits.prodComparison SSet.toTop (Δ[1] : SSet.{u}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  have hIsoP : IsIso (Limits.prodComparison SSet.toTop X (Δ[1] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap _ _
  have hPinvHom : Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{u}) ≫
        (@asIso _ _ _ _ (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u})) hIsoP).inv =
    𝟙 (SSet.toTop.obj (X ⨯ (Δ[1] : SSet.{u}))) :=
    @IsIso.hom_inv_id _ _ _ _ _ hIsoP
  have hTC :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u}) =
    𝟙 (X ⊗ (Δ[1] : SSet.{u})) :=
    Iso.hom_inv_id_app (CartesianMonoidalCategory.tensorLeftIsoProd X) (Δ[1] : SSet.{u})
  have hIota : SSet.ι₁ (X := X) =
    (SSet.ι₁ ≫ (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u})) ≫
      (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u}) := by
    rw [Category.assoc, hTC, Category.comp_id]
  let hBridgeIso : ((Limits.prod.functor.obj X).obj (Δ[1] : SSet.{u})) ≅ (X ⨯ (Δ[1] : SSet.{u})) :=
    Iso.refl (X ⨯ (Δ[1] : SSet.{u}))
  have hHomFst :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
        (hBridgeIso.hom ≫ Limits.prod.fst) =
      CartesianMonoidalCategory.fst X (Δ[1] : SSet.{u}) := by
    have hBridge : hBridgeIso.hom ≫ Limits.prod.fst = Limits.prod.fst :=
      Category.id_comp Limits.prod.fst
    calc (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
      (hBridgeIso.hom ≫ Limits.prod.fst)
        = (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
          Limits.prod.fst := by
          rw [hBridge]
      _ = CartesianMonoidalCategory.fst X (Δ[1] : SSet.{u}) :=
          IsLimit.conePointUniqueUpToIso_hom_comp
            (CartesianMonoidalCategory.tensorProductIsBinaryProduct X (Δ[1] : SSet.{u}))
            (Limits.limit.isLimit _) ⟨.left⟩
  have hHomSnd :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
        (hBridgeIso.hom ≫ Limits.prod.snd) =
      CartesianMonoidalCategory.snd X (Δ[1] : SSet.{u}) := by
    have hBridge : hBridgeIso.hom ≫ Limits.prod.snd = Limits.prod.snd :=
      Category.id_comp Limits.prod.snd
    calc (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
      (hBridgeIso.hom ≫ Limits.prod.snd)
        = (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u}) ≫
          Limits.prod.snd := by
          rw [hBridge]
      _ = CartesianMonoidalCategory.snd X (Δ[1] : SSet.{u}) :=
          IsLimit.conePointUniqueUpToIso_hom_comp
            (CartesianMonoidalCategory.tensorProductIsBinaryProduct X (Δ[1] : SSet.{u}))
            (Limits.limit.isLimit _) ⟨.right⟩
  have hProd : (Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
      (𝟙 (SSet.toTop.obj X)) ≫
      (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
      Limits.prod.map (𝟙 (SSet.toTop.obj X))
        SSet.stdSimplex.toTopObjIsoI.inv) =
      SSet.toTop.map
        (SSet.ι₁ ≫ (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map hBridgeIso.hom ≫
        Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u}) := by
    apply Limits.prod.hom_ext
    · simp only [Category.assoc, Limits.prod.map_fst, Limits.prod.lift_fst,
        Limits.prod.braiding_hom, Limits.prod.lift_fst, Limits.prod.lift_snd,
        Category.comp_id, Limits.prodComparison_fst,
        Limits.prod.lift_fst, SSet.ι₁_fst, ← Functor.map_comp,
        hHomFst, hBridgeIso]
      exact (SSet.toTop.map_id _).symm
    · have hRedOne : ((Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
          (𝟙 (SSet.toTop.obj X)) ≫
          (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
          Limits.prod.map (𝟙 (SSet.toTop.obj X))
            SSet.stdSimplex.toTopObjIsoI.inv) ≫ Limits.prod.snd) =
          TopCat.const (1 : TopCat.I.{u}) ≫ SSet.stdSimplex.toTopObjIsoI.inv := by
        calc ((Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫
              (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
              Limits.prod.map (𝟙 (SSet.toTop.obj X))
                SSet.stdSimplex.toTopObjIsoI.inv) ≫ Limits.prod.snd)
            _ = Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫
              (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
              (Limits.prod.map (𝟙 (SSet.toTop.obj X))
                SSet.stdSimplex.toTopObjIsoI.inv ≫ Limits.prod.snd) := by
              rw [Category.assoc, Category.assoc]
            _ = Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫
              (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
              (Limits.prod.snd ≫ SSet.stdSimplex.toTopObjIsoI.inv) := by
              rw [Limits.prod.map_snd]
            _ = Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫
              (((Limits.prod.braiding TopCat.I.{u}
                (SSet.toTop.obj X)).hom ≫ Limits.prod.snd) ≫
                SSet.stdSimplex.toTopObjIsoI.inv) := by
              rw [← Category.assoc
                (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom
                Limits.prod.snd SSet.stdSimplex.toTopObjIsoI.inv]
            _ = Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫
              (Limits.prod.fst ≫ SSet.stdSimplex.toTopObjIsoI.inv) := by
              rw [Limits.prod.braiding_hom, Limits.prod.lift_snd]
            _ = (Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
              (𝟙 (SSet.toTop.obj X)) ≫ Limits.prod.fst) ≫
              SSet.stdSimplex.toTopObjIsoI.inv := by
              rw [← Category.assoc
                (Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
                  (𝟙 (SSet.toTop.obj X)))
                Limits.prod.fst SSet.stdSimplex.toTopObjIsoI.inv]
            _ = TopCat.const (1 : TopCat.I.{u}) ≫ SSet.stdSimplex.toTopObjIsoI.inv := by
              rw [Limits.prod.lift_fst]
      rw [hRedOne]
      simp only [Category.assoc,
        Limits.prodComparison_snd,
        SSet.ι₁_snd, ← Functor.map_comp,
        hHomSnd, hBridgeIso]
      ext x
      simp only [TopCat.const_apply, ConcreteCategory.comp_apply]
      rw [SSet.toTopObjIsoI_inv_one]
      have hFac : SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2) :
          (Δ[1] : SSet.{u}) _⦋0⦌) =
          IsTerminal.from SSet.stdSimplex.isTerminalObj₀ X ≫
            SSet.stdSimplex.δ 0 := by
        rw [SSet.stdSimplex.δ_zero_eq_const]
        simp
      rw [hFac, Functor.map_comp]
      exact congrArg (SSet.toTop.map (SSet.stdSimplex.δ 0)) (Subsingleton.elim _ _)
  calc Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
        (𝟙 (SSet.toTop.obj X)) ≫ realizeHomotopyMap X Y f g H
      = (Limits.prod.lift (TopCat.const (1 : TopCat.I.{u}))
        (𝟙 (SSet.toTop.obj X)) ≫
        (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
        Limits.prod.map (𝟙 (SSet.toTop.obj X))
          SSet.stdSimplex.toTopObjIsoI.inv ≫
        (@asIso _ _ _ _ (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u})) hIsoP).inv ≫
        SSet.toTop.map hBridgeIso.inv ≫
        SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map H.h) := by
          unfold realizeHomotopyMap
          simp only [hBridgeIso]
      _ = SSet.toTop.map
        (SSet.ι₁ ≫ (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map hBridgeIso.hom ≫
        Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u}) ≫
        (@asIso _ _ _ _ (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u})) hIsoP).inv ≫
        SSet.toTop.map hBridgeIso.inv ≫
        SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map H.h := by
          exact congrArg (· ≫ (@asIso _ _ _ _ (Limits.prodComparison SSet.toTop
            X (Δ[1] : SSet.{u})) hIsoP).inv ≫
            SSet.toTop.map hBridgeIso.inv ≫
            SSet.toTop.map
              ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
            SSet.toTop.map H.h) hProd
      _ = SSet.toTop.map
        (SSet.ι₁ ≫ (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map H.h := by
          simp only [← Category.assoc, hPinvHom, Category.id_comp,
            ← Functor.map_comp, Iso.hom_inv_id]
      _ =
        SSet.toTop.map
          ((SSet.ι₁ ≫ (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[1] : SSet.{u})) ≫
            (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map H.h := by
          simp only [← Functor.map_comp, Category.assoc]
      _ = SSet.toTop.map (SSet.ι₁ (X := X)) ≫ SSet.toTop.map H.h := by rw [← hIota]
      _ = SSet.toTop.map (SSet.ι₁ (X := X) ≫ H.h) := by
          rw [← Functor.map_comp]
      _ = SSet.toTop.map g := by rw [H.h₁]

end SSet
