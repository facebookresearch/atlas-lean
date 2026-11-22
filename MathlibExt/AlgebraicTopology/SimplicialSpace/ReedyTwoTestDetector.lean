/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceIhomComponents

/-!
# Two original component tests detect Reedy weakness

The two tests construct one whole map in the reverse direction. Both full
component triangles are projected to every original outer degree, where the
raw scalar component dictionary and stronger weak-equivalence detector apply.
No fibrancy or inhabitedness hypothesis is imposed on the original endpoints.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped SimplicialSpace.Inner Simplicial
namespace SimplicialSpace

private lemma inner_postcomp_app_zero {A B C : SimplicialSpace.{u}}
    (b : A ⟶ B) (q : B ⟶ C) :
    ((innerHomFunctor.obj (op A)).map q).app (op ⦋0⦌)
        (innerHomEquiv A B b) = innerHomEquiv A C (b ≫ q) := by
  have h : eHomEquiv SSet.{u} b ≫ eHomWhiskerLeft SSet.{u} A q =
      eHomEquiv SSet.{u} (b ≫ q) := by
    rw [innerHom_comp, eHomWhiskerLeft]
    simp only [← Category.assoc, tensorHom_def]
    rw [rightUnitor_inv_naturality, unitors_inv_equal]
  exact congrArg (fun a : 𝟙_ SSet.{u} ⟶ (A ⟶[SSet.{u}] C) =>
    a.app (op ⦋0⦌) PUnit.unit) h

private lemma innerHomEquiv_π {A B : SimplicialSpace.{u}}
    (h : A ⟶ B) (m : SimplexCategoryᵒᵖ) :
    (innerHomπ A B m).app (op ⦋0⦌) (innerHomEquiv A B h) =
      SSet.ihomVertexEquiv (A.diagram.obj m) (B.diagram.obj m) (h.hom.app m) := by
  let _ : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  let hEnds : ∀ X Y : SimplicialObject SSet.{u},
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} X Y := inferInstance
  let _ := hEnds
  have hπ : eHomEquiv SSet.{u} h ≫ innerHomπ A B m =
      MonoidalClosed.curry' (h.hom.app m) := by
    change Enriched.FunctorCategory.homEquiv SSet.{u} h.hom ≫
        Enriched.FunctorCategory.enrichedHomπ SSet.{u} A.diagram B.diagram m =
      (eHomEquiv SSet.{u}) (h.hom.app m)
    exact Enriched.FunctorCategory.homEquiv_apply_π SSet.{u} h.hom m
  exact congrArg (fun a : 𝟙_ SSet.{u} ⟶
      (ihom (A.diagram.obj m)).obj (B.diagram.obj m) =>
    a.app (op ⦋0⦌) PUnit.unit) hπ

/-- Two original full component tests detect weakness in the named Reedy model. -/
theorem reedyWeak_of_surjective_injective_mapπ₀
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hSurj : Function.Surjective (SSet.mapπ₀ ((innerHomFunctor.map f.op).app X)))
    (hInj : Function.Injective (SSet.mapπ₀ ((innerHomFunctor.map f.op).app Y))) :
    letI : HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} :=
      ReedyModel.modelCategory
    HomotopicalAlgebra.WeakEquivalence f := by
  let _ : HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  obtain ⟨c, hc⟩ := hSurj (SSet.π₀.mk (innerHomEquiv X X (𝟙 X)))
  obtain ⟨v, hv⟩ := SSet.π₀.mk_surjective c
  let g : Y ⟶ X := (innerHomEquiv Y X).symm v
  have hg : innerHomEquiv Y X g = v := (innerHomEquiv Y X).apply_symm_apply v
  have hfg : SSet.π₀.mk (innerHomEquiv X X (f ≫ g)) =
      SSet.π₀.mk (innerHomEquiv X X (𝟙 X)) := by
    rw [← hv, SSet.mapπ₀_mk, ← hg, ReedyModel.inner_precomp_app_zero] at hc
    exact hc
  have hgf : SSet.π₀.mk (innerHomEquiv Y Y (g ≫ f)) =
      SSet.π₀.mk (innerHomEquiv Y Y (𝟙 Y)) := by
    apply hInj
    erw [SSet.mapπ₀_mk, SSet.mapπ₀_mk,
      ReedyModel.inner_precomp_app_zero, ReedyModel.inner_precomp_app_zero]
    have hpost := congrArg (SSet.mapπ₀ ((innerHomFunctor.obj (op X)).map f)) hfg
    erw [SSet.mapπ₀_mk, SSet.mapπ₀_mk,
      inner_postcomp_app_zero, inner_postcomp_app_zero] at hpost
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using hpost
  apply (ReedyModel.weakEquivalence_iff f).2
  intro n
  let m : SimplexCategoryᵒᵖ := op ⦋n⦌
  have hfgm := congrArg (SSet.mapπ₀ (innerHomπ X X m)) hfg
  have hgfm := congrArg (SSet.mapπ₀ (innerHomπ Y Y m)) hgf
  simp only [SSet.mapπ₀_mk, innerHomEquiv_π] at hfgm hgfm
  change SSet.π₀.mk (SSet.ihomVertexEquiv (X.diagram.obj m) (X.diagram.obj m)
      (f.hom.app m ≫ g.hom.app m)) =
    SSet.π₀.mk (SSet.ihomVertexEquiv (X.diagram.obj m) (X.diagram.obj m) (𝟙 _)) at hfgm
  change SSet.π₀.mk (SSet.ihomVertexEquiv (Y.diagram.obj m) (Y.diagram.obj m)
      (g.hom.app m ≫ f.hom.app m)) =
    SSet.π₀.mk (SSet.ihomVertexEquiv (Y.diagram.obj m) (Y.diagram.obj m) (𝟙 _)) at hgfm
  have hwfg : SSet.realizationWeakEquivalences (f.hom.app m ≫ g.hom.app m) :=
    (SSet.realizationWeakEquivalences_iff_of_ihom_component_eq hfgm).2
      (SSet.realizationWeakEquivalences.id_mem _)
  have hwgf : SSet.realizationWeakEquivalences (g.hom.app m ≫ f.hom.app m) :=
    (SSet.realizationWeakEquivalences_iff_of_ihom_component_eq hgfm).2
      (SSet.realizationWeakEquivalences.id_mem _)
  exact SSet.realizationWeakEquivalences.left_of_comp_comp
    (a := f.hom.app m) (b := g.hom.app m) (c := f.hom.app m) hwfg hwgf

end SimplicialSpace
