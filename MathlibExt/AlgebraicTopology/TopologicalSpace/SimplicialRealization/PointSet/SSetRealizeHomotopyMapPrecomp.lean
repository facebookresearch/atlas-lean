/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyComp
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMap

/-!
# Realized simplicial homotopies and source precomposition

An ordinary simplicial homotopy may be precomposed in its source.  Realizing
that precomposition agrees with precomposing the realized homotopy map by the
identity on the interval and the realized source map.

The second theorem identifies a realized cylinder which factors through the
first simplicial projection with the corresponding second topological
projection.  Its two endpoint parameters may differ: the supplied equality
of the cylinder map is the load-bearing hypothesis.

Only ordinary simplicial homotopies and map-level realization identities are
provided.  There is no stationarity, continuous relative homotopy,
Waldhausen, pointed, loop-space, additivity, weak-equivalence, spectrum, or
Q/S claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u

namespace SSet

variable {W X Y : SSet.{u}} {f g : X ⟶ Y}

set_option backward.isDefEq.respectTransparency false in
private theorem tensorLeftIsoProd_hom_natural_left
    (k : W ⟶ X) (T : SSet.{u}) :
    (k ▷ T) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T =
      (CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app T ≫
        Limits.prod.map k (𝟙 T) := by
  have hXfst :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T ≫
          Limits.prod.fst =
        CartesianMonoidalCategory.fst X T :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X T)
      (Limits.limit.isLimit _) ⟨WalkingPair.left⟩
  have hXsnd :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T ≫
          Limits.prod.snd =
        CartesianMonoidalCategory.snd X T :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X T)
      (Limits.limit.isLimit _) ⟨WalkingPair.right⟩
  have hWfst :
      (CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app T ≫
          Limits.prod.fst =
        CartesianMonoidalCategory.fst W T :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct W T)
      (Limits.limit.isLimit _) ⟨WalkingPair.left⟩
  have hWsnd :
      (CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app T ≫
          Limits.prod.snd =
        CartesianMonoidalCategory.snd W T :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct W T)
      (Limits.limit.isLimit _) ⟨WalkingPair.right⟩
  apply Limits.prod.hom_ext
  · rw [Category.assoc, hXfst, Category.assoc,
      Limits.prod.map_fst]
    rw [← Category.assoc, hWfst]
    exact CartesianMonoidalCategory.whiskerRight_fst k T
  · rw [Category.assoc, hXsnd, Category.assoc,
      Limits.prod.map_snd]
    rw [← Category.assoc, hWsnd, Category.comp_id]
    exact CartesianMonoidalCategory.whiskerRight_snd k T

set_option backward.isDefEq.respectTransparency false in
private theorem tensorLeftIsoProd_inv_natural_left
    (k : W ⟶ X) (T : SSet.{u}) :
    Limits.prod.map k (𝟙 T) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app T =
      (CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
        (k ▷ T) := by
  apply (cancel_mono
    ((CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T)).mp
  calc
    (Limits.prod.map k (𝟙 T) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app T) ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T =
      Limits.prod.map k (𝟙 T) := by
        rw [Category.assoc, Iso.inv_hom_id_app]
        exact Category.comp_id _
    _ = ((CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app T) ≫
        Limits.prod.map k (𝟙 T) := by simp
    _ = (CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
        ((CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app T ≫
          Limits.prod.map k (𝟙 T)) := by rw [Category.assoc]
    _ = (CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
        ((k ▷ T) ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T) := by
      rw [tensorLeftIsoProd_hom_natural_left]
    _ = ((CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
          (k ▷ T)) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T := by
      rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Realization commutes with precomposition in the simplicial source.  The
interval factor is unchanged and the realized source map is covariant. -/
theorem realizeHomotopyMap_precomp (H : SSet.Homotopy f g)
    (k : W ⟶ X) :
    Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map k) ≫
        SSet.realizeHomotopyMap X Y f g H =
      SSet.realizeHomotopyMap W Y (k ≫ f) (k ≫ g)
        (H.precomp k) := by
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u}) W) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      W (Δ[1] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap _ _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap _ _
  have hBraid :
      Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map k) ≫
          (Limits.prod.braiding TopCat.I.{u}
            (SSet.toTop.obj X)).hom =
        (Limits.prod.braiding TopCat.I.{u}
            (SSet.toTop.obj W)).hom ≫
          Limits.prod.map (SSet.toTop.map k)
            (𝟙 TopCat.I.{u}) := by
    exact Limits.braid_natural (𝟙 TopCat.I.{u}) (SSet.toTop.map k)
  have hMaps :
      Limits.prod.map (SSet.toTop.map k)
          (𝟙 TopCat.I.{u}) ≫
          Limits.prod.map (𝟙 (SSet.toTop.obj X))
            SSet.stdSimplex.toTopObjIsoI.inv =
        Limits.prod.map (𝟙 (SSet.toTop.obj W))
            SSet.stdSimplex.toTopObjIsoI.inv ≫
          Limits.prod.map (SSet.toTop.map k)
            (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u}))) := by
    rw [Limits.prod.map_map, Limits.prod.map_map]
    simp only [Category.comp_id, Category.id_comp]
  have hProd :
      Limits.prod.map (SSet.toTop.map k)
          (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u}))) ≫
          (asIso (Limits.prodComparison SSet.toTop
            X (Δ[1] : SSet.{u}))).inv =
        (asIso (Limits.prodComparison SSet.toTop
            W (Δ[1] : SSet.{u}))).inv ≫
          SSet.toTop.map
            (Limits.prod.map k (𝟙 (Δ[1] : SSet.{u}))) := by
    simpa using
      (Limits.prodComparison_inv_natural
        (F := SSet.toTop) k (𝟙 (Δ[1] : SSet.{u}))).symm
  have hTensor :
      SSet.toTop.map
          (Limits.prod.map k (𝟙 (Δ[1] : SSet.{u}))) ≫
          SSet.toTop.map
            ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
              (Δ[1] : SSet.{u})) =
        SSet.toTop.map
            ((CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app
              (Δ[1] : SSet.{u})) ≫
          SSet.toTop.map (k ▷ (Δ[1] : SSet.{u})) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      tensorLeftIsoProd_inv_natural_left]
  let bridgeW : ((Limits.prod.functor.obj W).obj
      (Δ[1] : SSet.{u})) ≅ (W ⨯ (Δ[1] : SSet.{u})) :=
    Iso.refl _
  let bridgeX : ((Limits.prod.functor.obj X).obj
      (Δ[1] : SSet.{u})) ≅ (X ⨯ (Δ[1] : SSet.{u})) :=
    Iso.refl _
  have hBridge :
      SSet.toTop.map
          (Limits.prod.map k (𝟙 (Δ[1] : SSet.{u}))) ≫
          SSet.toTop.map bridgeX.inv =
        SSet.toTop.map bridgeW.inv ≫
          SSet.toTop.map
            (Limits.prod.map k (𝟙 (Δ[1] : SSet.{u}))) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  change
    Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map k) ≫
      (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
      Limits.prod.map (𝟙 (SSet.toTop.obj X))
        SSet.stdSimplex.toTopObjIsoI.inv ≫
      (asIso (Limits.prodComparison SSet.toTop
        X (Δ[1] : SSet.{u}))).inv ≫
      SSet.toTop.map bridgeX.inv ≫
      SSet.toTop.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
          (Δ[1] : SSet.{u})) ≫
      SSet.toTop.map H.h =
    (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj W)).hom ≫
      Limits.prod.map (𝟙 (SSet.toTop.obj W))
        SSet.stdSimplex.toTopObjIsoI.inv ≫
      (asIso (Limits.prodComparison SSet.toTop
        W (Δ[1] : SSet.{u}))).inv ≫
      SSet.toTop.map bridgeW.inv ≫
      SSet.toTop.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app
          (Δ[1] : SSet.{u})) ≫
      SSet.toTop.map (H.precomp k).h
  rw [← Category.assoc, hBraid, Category.assoc]
  slice_lhs 2 3 => rw [hMaps]
  slice_lhs 3 4 => rw [hProd]
  slice_lhs 4 5 => rw [hBridge]
  slice_lhs 5 6 => rw [hTensor]
  simp only [← Functor.map_comp, Homotopy.precomp_h,
    Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A realized homotopy map whose simplicial cylinder factors through the
first projection is constant in the interval coordinate. -/
theorem realizeHomotopyMap_of_h_eq_fst
    {q₀ q₁ : W ⟶ Y} (H : SSet.Homotopy q₀ q₁)
    (hH : H.h = CartesianMonoidalCategory.fst W
      (Δ[1] : SSet.{u}) ≫ q₀) :
    SSet.realizeHomotopyMap W Y q₀ q₁ H =
      Limits.prod.snd ≫ SSet.toTop.map q₀ := by
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u}) W) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      W (Δ[1] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap _ _
  let bridgeW : ((Limits.prod.functor.obj W).obj
      (Δ[1] : SSet.{u})) ≅ (W ⨯ (Δ[1] : SSet.{u})) :=
    Iso.refl _
  have hTensorFst :
      (CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app
          (Δ[1] : SSet.{u}) ≫
          CartesianMonoidalCategory.fst W (Δ[1] : SSet.{u}) =
        Limits.prod.fst := by
    apply (cancel_epi
      ((CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app
        (Δ[1] : SSet.{u}))).mp
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    exact (IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct W
        (Δ[1] : SSet.{u}))
      (Limits.limit.isLimit _) ⟨WalkingPair.left⟩).symm
  have hTensorFstQ :
      (CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app
          (Δ[1] : SSet.{u}) ≫
          (CartesianMonoidalCategory.fst W (Δ[1] : SSet.{u}) ≫ q₀) =
        Limits.prod.fst ≫ q₀ := by
    rw [← Category.assoc, hTensorFst]
  have hSSetTail :
      bridgeW.inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app
            (Δ[1] : SSet.{u}) ≫
          (CartesianMonoidalCategory.fst W (Δ[1] : SSet.{u}) ≫ q₀) =
        Limits.prod.fst ≫ q₀ := by
    rw [hTensorFstQ]
    rfl
  change
    (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj W)).hom ≫
      Limits.prod.map (𝟙 (SSet.toTop.obj W))
        SSet.stdSimplex.toTopObjIsoI.inv ≫
      (asIso (Limits.prodComparison SSet.toTop
        W (Δ[1] : SSet.{u}))).inv ≫
      SSet.toTop.map bridgeW.inv ≫
      SSet.toTop.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app
          (Δ[1] : SSet.{u})) ≫
      SSet.toTop.map H.h =
      Limits.prod.snd ≫ SSet.toTop.map q₀
  rw [hH]
  simp only [← Functor.map_comp]
  rw [hSSetTail, Functor.map_comp, asIso_inv]
  slice_lhs 3 4 => rw [Limits.inv_prodComparison_map_fst]
  simp

end SSet
