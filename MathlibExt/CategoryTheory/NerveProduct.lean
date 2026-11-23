/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Strict nerve product isomorphism

For categories `C` and `D` over the same universes, the nerve of the product
category is canonically isomorphic to the product of nerves as simplicial sets,
via product-category projections and pairing. This is the wrappable step
needed to transport the StageWeak source and quotient evaluation maps at the nerve level.

This is a strict nerve-level isomorphism only. No realization product
isomorphism, homeomorphism, weak equivalence, additivity, loop-space, or `K₀`
claim is made here.
-/

@[expose] public section

namespace CategoryTheory

universe v u

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Simplicial

/-- Canonical strict product isomorphism for the nerve, same-universe only. -/
noncomputable def nerveProdIso (C D : Type u) [Category.{v} C] [Category.{v} D] :
    nerve (C × D) ≅ nerve C ⨯ nerve D :=
  let toExplicit : nerve (C × D) ⟶
      FunctorToTypes.prod (nerve C) (nerve D) :=
    { app Δ := ↾fun X =>
        ((nerveMap (Prod.fst C D)).app Δ X, (nerveMap (Prod.snd C D)).app Δ X) }
  let fromExplicit : FunctorToTypes.prod (nerve C) (nerve D) ⟶ nerve (C × D) :=
    { app Δ := ↾fun p => p.1.prod' p.2 }
  let toFrom : toExplicit ≫ fromExplicit = 𝟙 (nerve (C × D)) := by
    ext Δ X
    rfl
  let fromTo : fromExplicit ≫ toExplicit = 𝟙 _ := by
    ext Δ p
    · rfl
    · rfl
  let explicitIso : nerve (C × D) ≅
      FunctorToTypes.prod (nerve C) (nerve D) :=
    { hom := toExplicit
      inv := fromExplicit
      hom_inv_id := toFrom
      inv_hom_id := fromTo }
  explicitIso.trans (FunctorToTypes.binaryProductIso _ _).symm

/-- The forward nerve product isomorphism followed by the first projection is
induced by the ordinary first projection. -/
@[reassoc (attr := simp)]
lemma nerveProdIso_hom_comp_fst (C D : Type u) [Category.{v} C] [Category.{v} D] :
    (nerveProdIso C D).hom ≫ prod.fst =
      nerveMap (Prod.fst C D) := by
  simp only [nerveProdIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, FunctorToTypes.binaryProductIso_inv_comp_fst]
  rfl

/-- The forward nerve product isomorphism followed by the second projection is
induced by the ordinary second projection. -/
@[reassoc (attr := simp)]
lemma nerveProdIso_hom_comp_snd (C D : Type u) [Category.{v} C] [Category.{v} D] :
    (nerveProdIso C D).hom ≫ prod.snd =
      nerveMap (Prod.snd C D) := by
  simp only [nerveProdIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, FunctorToTypes.binaryProductIso_inv_comp_snd]
  rfl

/-- Forward computation on `0`-simplices: the iso sends `mk₀ X` to the paired `mk₀`. -/
@[simp]
lemma nerveProdIso_hom_app_mk₀ (C D : Type u) [Category.{v} C] [Category.{v} D] (X : C × D) :
    (nerveProdIso C D).hom.app (op ⦋0⦌) (ComposableArrows.mk₀ X) =
      FunctorToTypes.prodMk (ComposableArrows.mk₀ X.1) (ComposableArrows.mk₀ X.2) := by
  refine FunctorToTypes.prod_ext' (nerve C) (nerve D) (op ⦋0⦌) _ _ ?_ ?_
  · have h : ((nerveProdIso C D).hom ≫ Limits.prod.fst).app (op ⦋0⦌)
        (ComposableArrows.mk₀ X) = ComposableArrows.mk₀ X.1 := by
      rw [nerveProdIso_hom_comp_fst]
      exact nerveMap_app_mk₀ _ _
    have hMk : (Limits.prod.fst (X := nerve C)).app (op ⦋0⦌)
        ((FunctorToTypes.prodMk (ComposableArrows.mk₀ X.1) (ComposableArrows.mk₀ X.2)) :
          (nerve C ⨯ nerve D).obj (op ⦋0⦌)) =
        ComposableArrows.mk₀ X.1 :=
      FunctorToTypes.prodMk_fst _ _
    exact h.trans hMk.symm
  · have h : ((nerveProdIso C D).hom ≫ Limits.prod.snd).app (op ⦋0⦌)
        (ComposableArrows.mk₀ X) = ComposableArrows.mk₀ X.2 := by
      rw [nerveProdIso_hom_comp_snd]
      exact nerveMap_app_mk₀ _ _
    have hMk : (Limits.prod.snd (X := nerve C)).app (op ⦋0⦌)
        ((FunctorToTypes.prodMk (ComposableArrows.mk₀ X.1) (ComposableArrows.mk₀ X.2)) :
          (nerve C ⨯ nerve D).obj (op ⦋0⦌)) =
        ComposableArrows.mk₀ X.2 :=
      FunctorToTypes.prodMk_snd _ _
    exact h.trans hMk.symm

/-- Forward computation on `1`-simplices: the iso sends `mk₁ f` to the paired `mk₁`. -/
@[simp]
lemma nerveProdIso_hom_app_mk₁ (C D : Type u) [Category.{v} C] [Category.{v} D]
    {X Y : C × D} (f : X ⟶ Y) :
    (nerveProdIso C D).hom.app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      FunctorToTypes.prodMk (ComposableArrows.mk₁ f.1) (ComposableArrows.mk₁ f.2) := by
  refine FunctorToTypes.prod_ext' (nerve C) (nerve D) (op ⦋1⦌) _ _ ?_ ?_
  · have h : ((nerveProdIso C D).hom ≫ Limits.prod.fst).app (op ⦋1⦌)
        (ComposableArrows.mk₁ f) = ComposableArrows.mk₁ f.1 := by
      rw [nerveProdIso_hom_comp_fst]
      exact nerveMap_app_mk₁ _ _
    have hMk : (Limits.prod.fst (X := nerve C)).app (op ⦋1⦌)
        ((FunctorToTypes.prodMk (ComposableArrows.mk₁ f.1) (ComposableArrows.mk₁ f.2)) :
          (nerve C ⨯ nerve D).obj (op ⦋1⦌)) =
        ComposableArrows.mk₁ f.1 :=
      FunctorToTypes.prodMk_fst _ _
    exact h.trans hMk.symm
  · have h : ((nerveProdIso C D).hom ≫ Limits.prod.snd).app (op ⦋1⦌)
        (ComposableArrows.mk₁ f) = ComposableArrows.mk₁ f.2 := by
      rw [nerveProdIso_hom_comp_snd]
      exact nerveMap_app_mk₁ _ _
    have hMk : (Limits.prod.snd (X := nerve C)).app (op ⦋1⦌)
        ((FunctorToTypes.prodMk (ComposableArrows.mk₁ f.1) (ComposableArrows.mk₁ f.2)) :
          (nerve C ⨯ nerve D).obj (op ⦋1⦌)) =
        ComposableArrows.mk₁ f.2 :=
      FunctorToTypes.prodMk_snd _ _
    exact h.trans hMk.symm

/-- Inverse computation on a paired `0`-simplex. -/
@[simp]
lemma nerveProdIso_inv_app_pair_mk₀ (C D : Type u) [Category.{v} C] [Category.{v} D]
    (x : C) (y : D) :
    (nerveProdIso C D).inv.app (op ⦋0⦌)
      (FunctorToTypes.prodMk (ComposableArrows.mk₀ x) (ComposableArrows.mk₀ y)) =
      ComposableArrows.mk₀ (x, y) := by
  have h_hom : (nerveProdIso C D).hom.app (op ⦋0⦌) (ComposableArrows.mk₀ (x, y)) =
      FunctorToTypes.prodMk (ComposableArrows.mk₀ x) (ComposableArrows.mk₀ y) :=
    nerveProdIso_hom_app_mk₀ C D (x, y)
  have h_iso : (nerveProdIso C D).inv.app (op ⦋0⦌)
      ((nerveProdIso C D).hom.app (op ⦋0⦌) (ComposableArrows.mk₀ (x, y))) =
      ComposableArrows.mk₀ (x, y) := by
    have h1 := Iso.hom_inv_id_app (nerveProdIso C D) (op ⦋0⦌)
    have h2 := ConcreteCategory.congr_hom h1 (ComposableArrows.mk₀ (x, y))
    exact h2
  rw [h_hom] at h_iso
  exact h_iso

/-- Inverse computation on a paired `1`-simplex. -/
@[simp]
lemma nerveProdIso_inv_app_pair_mk₁ (C D : Type u) [Category.{v} C] [Category.{v} D]
    {x₁ y₁ : C} {x₂ y₂ : D} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    (nerveProdIso C D).inv.app (op ⦋1⦌)
      (FunctorToTypes.prodMk (ComposableArrows.mk₁ f) (ComposableArrows.mk₁ g)) =
      ComposableArrows.mk₁ (CategoryTheory.Prod.mkHom f g) := by
  have h_hom : (nerveProdIso C D).hom.app (op ⦋1⦌)
      (ComposableArrows.mk₁ (CategoryTheory.Prod.mkHom f g)) =
      FunctorToTypes.prodMk (ComposableArrows.mk₁ f) (ComposableArrows.mk₁ g) :=
    nerveProdIso_hom_app_mk₁ C D (CategoryTheory.Prod.mkHom f g)
  have h_iso : (nerveProdIso C D).inv.app (op ⦋1⦌)
      ((nerveProdIso C D).hom.app (op ⦋1⦌)
        (ComposableArrows.mk₁ (CategoryTheory.Prod.mkHom f g))) =
      ComposableArrows.mk₁ (CategoryTheory.Prod.mkHom f g) := by
    have h1 := Iso.hom_inv_id_app (nerveProdIso C D) (op ⦋1⦌)
    have h2 := ConcreteCategory.congr_hom h1 (ComposableArrows.mk₁ (CategoryTheory.Prod.mkHom f g))
    exact h2
  rw [h_hom] at h_iso
  exact h_iso

/-- Naturality of the strict nerve product isomorphism in each factor. -/
lemma nerveProdIso_natural (C C' D D' : Type u) [Category.{v} C] [Category.{v} C']
    [Category.{v} D] [Category.{v} D'] (F : C ⥤ C') (G : D ⥤ D') :
    nerveMap (F.prod G) ≫ (nerveProdIso C' D').hom =
      (nerveProdIso C D).hom ≫ Limits.prod.map (nerveMap F) (nerveMap G) := by
  apply Limits.prod.hom_ext
  · have hL : (nerveMap (F.prod G) ≫ (nerveProdIso C' D').hom) ≫ Limits.prod.fst =
        nerveMap ((F.prod G) ⋙ Prod.fst C' D') := by
      rw [Category.assoc, nerveProdIso_hom_comp_fst, nerveMap_comp]
    have hR : ((nerveProdIso C D).hom ≫
        Limits.prod.map (nerveMap F) (nerveMap G)) ≫ Limits.prod.fst =
        nerveMap (Prod.fst C D ⋙ F) := by
      rw [Category.assoc, Limits.prod.map_fst, ← Category.assoc,
        nerveProdIso_hom_comp_fst, nerveMap_comp]
    rw [hL, hR]
    rfl
  · have hL : (nerveMap (F.prod G) ≫ (nerveProdIso C' D').hom) ≫ Limits.prod.snd =
        nerveMap ((F.prod G) ⋙ Prod.snd C' D') := by
      rw [Category.assoc, nerveProdIso_hom_comp_snd, nerveMap_comp]
    have hR : ((nerveProdIso C D).hom ≫
        Limits.prod.map (nerveMap F) (nerveMap G)) ≫ Limits.prod.snd =
        nerveMap (Prod.snd C D ⋙ G) := by
      rw [Category.assoc, Limits.prod.map_snd, ← Category.assoc,
        nerveProdIso_hom_comp_snd, nerveMap_comp]
    rw [hL, hR]
    rfl

end CategoryTheory
