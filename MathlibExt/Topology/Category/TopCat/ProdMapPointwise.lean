/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Category.TopCat.Limits.Products

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

/-!
# Pointwise transport for fixed-left product maps

The `prodIsoProd` inverse point `(k, x)` transported through
`Limits.prod.map (𝟙 K) f` is the inverse point `(k, f x)`.
Helper for the next fixed-left factorization packet.
-/

/-- Pointwise transport of a `prodIsoProd` inverse point through a fixed-left
product map. -/
theorem prodMap_prodIso_inv_apply {K X Y : TopCat.{u}} (f : X ⟶ Y)
    (k : ↑K) (x : ↑X) :
    (Limits.prod.map (𝟙 K) f) ((prodIsoProd K X).inv (k, x)) =
      (prodIsoProd K Y).inv (k, f x) := by
  have eFst : (Limits.prod.fst : K ⨯ X ⟶ K)
      ((prodIsoProd K X).inv (k, x)) = k :=
    CategoryTheory.ConcreteCategory.congr_hom
      (TopCat.prodIsoProd_inv_fst K X) (k, x)
  have eMapFst : (Limits.prod.fst : K ⨯ Y ⟶ K)
      ((Limits.prod.map (𝟙 K) f) ((prodIsoProd K X).inv (k, x))) =
      (𝟙 K : K ⟶ K)
        ((Limits.prod.fst : K ⨯ X ⟶ K)
          ((prodIsoProd K X).inv (k, x))) :=
    CategoryTheory.ConcreteCategory.congr_hom
      (Limits.prod.map_fst (𝟙 K) f) ((prodIsoProd K X).inv (k, x))
  have hfst : (Limits.prod.fst : K ⨯ Y ⟶ K)
      ((Limits.prod.map (𝟙 K) f) ((prodIsoProd K X).inv (k, x))) = k :=
    eMapFst.trans ((congr_arg ⇑(𝟙 K : K ⟶ K) eFst).trans rfl)
  have eSnd : (Limits.prod.snd : K ⨯ X ⟶ X)
      ((prodIsoProd K X).inv (k, x)) = x :=
    CategoryTheory.ConcreteCategory.congr_hom
      (TopCat.prodIsoProd_inv_snd K X) (k, x)
  have eMapSnd : (Limits.prod.snd : K ⨯ Y ⟶ Y)
      ((Limits.prod.map (𝟙 K) f) ((prodIsoProd K X).inv (k, x))) =
      f ((Limits.prod.snd : K ⨯ X ⟶ X)
        ((prodIsoProd K X).inv (k, x))) :=
    CategoryTheory.ConcreteCategory.congr_hom
      (Limits.prod.map_snd (𝟙 K) f) ((prodIsoProd K X).inv (k, x))
  have hsnd : (Limits.prod.snd : K ⨯ Y ⟶ Y)
      ((Limits.prod.map (𝟙 K) f) ((prodIsoProd K X).inv (k, x))) = f x :=
    eMapSnd.trans (congr_arg ⇑f eSnd)
  have hpair : ((Limits.prod.fst : K ⨯ Y ⟶ K)
      ((Limits.prod.map (𝟙 K) f) ((prodIsoProd K X).inv (k, x))),
      (Limits.prod.snd : K ⨯ Y ⟶ Y)
        ((Limits.prod.map (𝟙 K) f) ((prodIsoProd K X).inv (k, x)))) =
      (k, f x) :=
    Prod.ext hfst hsnd
  have hL : (prodIsoProd K Y).hom
      ((Limits.prod.map (𝟙 K) f) ((prodIsoProd K X).inv (k, x))) =
      (k, f x) :=
    (prodIsoProd_hom_apply
      ((Limits.prod.map (𝟙 K) f) ((prodIsoProd K X).inv (k, x)))).trans
      hpair
  have eFstR : (Limits.prod.fst : K ⨯ Y ⟶ K)
      ((prodIsoProd K Y).inv (k, f x)) = k :=
    CategoryTheory.ConcreteCategory.congr_hom
      (TopCat.prodIsoProd_inv_fst K Y) (k, f x)
  have eSndR : (Limits.prod.snd : K ⨯ Y ⟶ Y)
      ((prodIsoProd K Y).inv (k, f x)) = f x :=
    CategoryTheory.ConcreteCategory.congr_hom
      (TopCat.prodIsoProd_inv_snd K Y) (k, f x)
  have hR : (prodIsoProd K Y).hom ((prodIsoProd K Y).inv (k, f x)) =
      (k, f x) :=
    (prodIsoProd_hom_apply ((prodIsoProd K Y).inv (k, f x))).trans
      (Prod.ext eFstR eSndR)
  apply (homeoOfIso (prodIsoProd K Y)).injective
  change (prodIsoProd K Y).hom _ = (prodIsoProd K Y).hom _
  rw [hL, hR]

/-- Product points are determined by their two projections. -/
theorem prod_point_ext {X Y : TopCat.{u}} {p q : ↑(X ⨯ Y)}
    (hfst : (Limits.prod.fst : X ⨯ Y ⟶ X) p =
      (Limits.prod.fst : X ⨯ Y ⟶ X) q)
    (hsnd : (Limits.prod.snd : X ⨯ Y ⟶ Y) p =
      (Limits.prod.snd : X ⨯ Y ⟶ Y) q) :
    p = q := by
  apply (homeoOfIso (prodIsoProd X Y)).injective
  change (prodIsoProd X Y).hom _ = (prodIsoProd X Y).hom _
  rw [prodIsoProd_hom_apply, prodIsoProd_hom_apply]
  exact Prod.ext hfst hsnd

end TopCat
