/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryBar.Change

/-!
# Category bar functoriality public contract

Compile-level pins for category-bar functoriality through coefficient maps,
change of indexing category, and mixed naturality, including `Data` and
simplicial packaging with identity and composition laws.
-/

open CategoryTheory Opposite

universe u v uR uL

namespace MathlibExtTest.CategoryBar.FunctorialityTests

variable {C : Type u} [Category.{v} C]
variable {R R' R'' : Cᵒᵖ ⥤ Type uR} {L L' L'' : C ⥤ Type uL}
variable {D E : Type u} [Category.{v} D] [Category.{v} E]
variable {S S' : Dᵒᵖ ⥤ Type uR} {T T' : D ⥤ Type uL}
variable {U : Eᵒᵖ ⥤ Type uR} {V : E ⥤ Type uL}

example (αR : R ⟶ R') (αL : L ⟶ L') (βR : R' ⟶ R'') (βL : L' ⟶ L'')
    {n : ℕ} (x : CategoryBar.barObj C R L n) :
    CategoryBar.barCoeffMap βR βL (CategoryBar.barCoeffMap αR αL x) =
      CategoryBar.barCoeffMap (αR ≫ βR) (αL ≫ βL) x :=
  CategoryBar.barCoeffMap_comp αR αL βR βL x

example (αR : R ⟶ R') (αL : L ⟶ L') (n : ℕ) :
    (CategoryBar.categoryBarDataMap αR αL).app n =
      ↾(CategoryBar.barCoeffMap αR αL (n := n)) :=
  CategoryBar.categoryBarDataMap_app αR αL n

example (αR : R ⟶ R') (αL : L ⟶ L') {n : ℕ}
    (i : Fin (n + 2)) (x : CategoryBar.barObj C R L (n + 1)) :
    CategoryBar.barCoeffMap αR αL (CategoryBar.barδ i x) =
      CategoryBar.barδ i (CategoryBar.barCoeffMap αR αL x) :=
  CategoryBar.barCoeffMap_δ αR αL i x

example (αR : R ⟶ R') (αL : L ⟶ L') {n : ℕ}
    (i : Fin (n + 1)) (x : CategoryBar.barObj C R L n) :
    CategoryBar.barCoeffMap αR αL (CategoryBar.barσ i x) =
      CategoryBar.barσ i (CategoryBar.barCoeffMap αR αL x) :=
  CategoryBar.barCoeffMap_σ αR αL i x

example :
    CategoryBar.categoryBarDataMap (𝟙 R) (𝟙 L) = 𝟙 _ :=
  CategoryBar.categoryBarDataMap_id

example (αR : R ⟶ R') (αL : L ⟶ L') (βR : R' ⟶ R'') (βL : L' ⟶ L'') :
    CategoryBar.categoryBarDataMap αR αL ≫ CategoryBar.categoryBarDataMap βR βL =
      CategoryBar.categoryBarDataMap (αR ≫ βR) (αL ≫ βL) :=
  CategoryBar.categoryBarDataMap_comp αR αL βR βL

example (αR : R ⟶ R') (αL : L ⟶ L') (n : ℕ) :
    (CategoryBar.categoryBarMap αR αL).app (op (SimplexCategory.mk n)) =
      ↾(CategoryBar.barCoeffMap αR αL (n := n)) :=
  CategoryBar.categoryBarMap_app_mk αR αL n

example :
    CategoryBar.categoryBarMap (𝟙 R) (𝟙 L) = 𝟙 _ :=
  CategoryBar.categoryBarMap_id

example (αR : R ⟶ R') (αL : L ⟶ L') (βR : R' ⟶ R'') (βL : L' ⟶ L'') :
    CategoryBar.categoryBarMap αR αL ≫ CategoryBar.categoryBarMap βR βL =
      CategoryBar.categoryBarMap (αR ≫ βR) (αL ≫ βL) :=
  CategoryBar.categoryBarMap_comp αR αL βR βL

example (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T)
    {n : ℕ} (F : ComposableArrows C n) (l : L.obj F.left)
    (r : R.obj (op F.right)) :
    CategoryBar.barIdxMap Φ αR αL (⟨F, l, r⟩ : CategoryBar.barObj C R L n) =
      (⟨(Φ.mapComposableArrows n).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : CategoryBar.barObj D S T n) :=
  CategoryBar.barIdxMap_mk Φ αR αL F l r

example (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T)
    {n : ℕ} (i : Fin (n + 2)) (x : CategoryBar.barObj C R L (n + 1)) :
    CategoryBar.barIdxMap Φ αR αL (CategoryBar.barδ i x) =
      CategoryBar.barδ i (CategoryBar.barIdxMap Φ αR αL x) :=
  CategoryBar.barIdxMap_δ Φ αR αL i x

example (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T)
    {n : ℕ} (i : Fin (n + 1)) (x : CategoryBar.barObj C R L n) :
    CategoryBar.barIdxMap Φ αR αL (CategoryBar.barσ i x) =
      CategoryBar.barσ i (CategoryBar.barIdxMap Φ αR αL x) :=
  CategoryBar.barIdxMap_σ Φ αR αL i x

example (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T) (n : ℕ) :
    (CategoryBar.categoryBarIdxDataMap Φ αR αL).app n =
      ↾(CategoryBar.barIdxMap Φ αR αL (n := n)) :=
  CategoryBar.categoryBarIdxDataMap_app Φ αR αL n

example (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T) (n : ℕ) :
    (CategoryBar.categoryBarIdxMap Φ αR αL).app (op (SimplexCategory.mk n)) =
      ↾(CategoryBar.barIdxMap Φ αR αL (n := n)) :=
  CategoryBar.categoryBarIdxMap_app_mk Φ αR αL n

example :
    CategoryBar.categoryBarIdxDataMap (𝟭 C) (R := R) (L := L)
      CategoryBar.idxIdR CategoryBar.idxIdL = 𝟙 _ :=
  CategoryBar.categoryBarIdxDataMap_id

example :
    CategoryBar.categoryBarIdxMap (𝟭 C) (R := R) (L := L)
      CategoryBar.idxIdR CategoryBar.idxIdL = 𝟙 _ :=
  CategoryBar.categoryBarIdxMap_id

example (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T)
    (βR : S ⟶ Ψ.op ⋙ U) (βL : T ⟶ Ψ ⋙ V)
    {n : ℕ} (x : CategoryBar.barObj C R L n) :
    CategoryBar.barIdxMap Ψ βR βL (CategoryBar.barIdxMap Φ αR αL x) =
      CategoryBar.barIdxMap (Φ ⋙ Ψ) (CategoryBar.compIdxR Φ Ψ αR βR)
        (CategoryBar.compIdxL Φ Ψ αL βL) x :=
  CategoryBar.barIdxMap_comp Φ Ψ αR αL βR βL x

example (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T)
    (βR : S ⟶ Ψ.op ⋙ U) (βL : T ⟶ Ψ ⋙ V) :
    CategoryBar.categoryBarIdxDataMap Φ αR αL ≫
        CategoryBar.categoryBarIdxDataMap Ψ βR βL =
      CategoryBar.categoryBarIdxDataMap (Φ ⋙ Ψ)
        (CategoryBar.compIdxR Φ Ψ αR βR) (CategoryBar.compIdxL Φ Ψ αL βL) :=
  CategoryBar.categoryBarIdxDataMap_comp Φ Ψ αR αL βR βL

example (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T)
    (βR : S ⟶ Ψ.op ⋙ U) (βL : T ⟶ Ψ ⋙ V) :
    CategoryBar.categoryBarIdxMap Φ αR αL ≫ CategoryBar.categoryBarIdxMap Ψ βR βL =
      CategoryBar.categoryBarIdxMap (Φ ⋙ Ψ)
        (CategoryBar.compIdxR Φ Ψ αR βR) (CategoryBar.compIdxL Φ Ψ αL βL) :=
  CategoryBar.categoryBarIdxMap_comp Φ Ψ αR αL βR βL

example (Φ : C ⥤ D)
    (γR : R ⟶ R') (γL : L ⟶ L') (δR : S ⟶ S') (δL : T ⟶ T')
    (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T)
    (αR' : R' ⟶ Φ.op ⋙ S') (αL' : L' ⟶ Φ ⋙ T')
    (hR : γR ≫ αR' = αR ≫ (Functor.whiskerLeft Φ.op δR))
    (hL : γL ≫ αL' = αL ≫ (Functor.whiskerLeft Φ δL))
    {n : ℕ} (x : CategoryBar.barObj C R L n) :
    CategoryBar.barCoeffMap δR δL (CategoryBar.barIdxMap Φ αR αL x) =
      CategoryBar.barIdxMap Φ αR' αL' (CategoryBar.barCoeffMap γR γL x) :=
  CategoryBar.barCoeff_idx_mixed Φ γR γL δR δL αR αL αR' αL' hR hL x

example (Φ : C ⥤ D)
    (γR : R ⟶ R') (γL : L ⟶ L') (δR : S ⟶ S') (δL : T ⟶ T')
    (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T)
    (αR' : R' ⟶ Φ.op ⋙ S') (αL' : L' ⟶ Φ ⋙ T')
    (hR : γR ≫ αR' = αR ≫ (Functor.whiskerLeft Φ.op δR))
    (hL : γL ≫ αL' = αL ≫ (Functor.whiskerLeft Φ δL)) :
    CategoryBar.categoryBarIdxDataMap Φ αR αL ≫ CategoryBar.categoryBarDataMap δR δL =
      CategoryBar.categoryBarDataMap γR γL ≫ CategoryBar.categoryBarIdxDataMap Φ αR' αL' :=
  CategoryBar.categoryBarDataMap_idx_mixed Φ γR γL δR δL αR αL αR' αL' hR hL

example (Φ : C ⥤ D)
    (γR : R ⟶ R') (γL : L ⟶ L') (δR : S ⟶ S') (δL : T ⟶ T')
    (αR : R ⟶ Φ.op ⋙ S) (αL : L ⟶ Φ ⋙ T)
    (αR' : R' ⟶ Φ.op ⋙ S') (αL' : L' ⟶ Φ ⋙ T')
    (hR : γR ≫ αR' = αR ≫ (Functor.whiskerLeft Φ.op δR))
    (hL : γL ≫ αL' = αL ≫ (Functor.whiskerLeft Φ δL)) :
    CategoryBar.categoryBarIdxMap Φ αR αL ≫ CategoryBar.categoryBarMap δR δL =
      CategoryBar.categoryBarMap γR γL ≫ CategoryBar.categoryBarIdxMap Φ αR' αL' :=
  CategoryBar.categoryBarMap_idx_mixed Φ γR γL δR δL αR αL αR' αL' hR hL

end MathlibExtTest.CategoryBar.FunctorialityTests
