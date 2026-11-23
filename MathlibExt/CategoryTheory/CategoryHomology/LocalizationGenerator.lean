/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.InitialGenerator
public import MathlibExt.CategoryTheory.CategoryHomology.Localization

/-!
# Localization of canonical coefficient homology classes

Localization sends the degree-zero class of each coefficient object to the
canonical class for the localized coefficient functor, under the canonical
coefficient homology comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe uD vD uE vE u

namespace CategoryTheory.CategoryHomology

private lemma cancel_inverse_middle
    {C₀ : Type*} [Category* C₀] {X₀ X₁ X₂ X₃ X₄ X₅ Y : C₀}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (e : Y ≅ X₂)
    (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (f : X₄ ⟶ X₅) :
    a ≫ b ≫ e.inv ≫ e.hom ≫ c ≫ d ≫ f = a ≫ b ≫ c ≫ d ≫ f := by
  simp only [Iso.inv_hom_id_assoc]

private lemma collapse_middle
    {C₀ : Type*} [Category* C₀] {X₀ X₁ X₂ X₃ X₄ X₅ : C₀}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (g : X₁ ⟶ X₃) (h : b ≫ c = g) :
    a ≫ b ≫ c ≫ d ≫ e = a ≫ g ≫ d ≫ e := by
  simpa only [Category.assoc] using congrArg (fun t => a ≫ t ≫ d ≫ e) h

private lemma rewrite_middle_pair
    {C₀ : Type*} [Category* C₀] {X₀ X₁ X₂ X₃ X₄ Y : C₀}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₁ ⟶ Y) (e : Y ⟶ X₃) (f : X₃ ⟶ X₄) (h : b ≫ c = d ≫ e) :
    a ≫ b ≫ c ≫ f = a ≫ d ≫ e ≫ f := by
  simpa only [Category.assoc] using congrArg (fun t => a ≫ t ≫ f) h

variable {D : Type uD} [Category.{vD} D] [Abelian D]

section Preservation

variable {E : Type uE} [Category.{vE} E] [Abelian E]
  (H : D ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma mapped_homology_projection (S : ShortComplex D) :
    (S.map H).homologyπ ≫ (S.mapHomologyIso H).hom =
      (S.mapCyclesIso H).hom ≫ H.map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq H, h.mapCyclesIso_eq H]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, (h.map H).homologyπ_comp_homologyIso_hom]
  change ((h.map H).cyclesIso.hom ≫ H.map h.π) ≫ H.map h.homologyIso.inv =
    ((h.map H).cyclesIso.hom ≫ H.map h.cyclesIso.inv) ≫ H.map S.homologyπ
  simp only [Category.assoc, ← H.map_comp]
  rw [h.π_comp_homologyIso_inv]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma mapped_homologyZeroProjection (K : ChainComplex D ℕ) :
    H.map (ChainComplex.homologyZeroClass K) ≫
        ((HomologicalComplex.mapHomologyFunctorIso 0 H).app K).inv =
      ChainComplex.homologyZeroClass ((H.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) := by
  let KH := (H.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let e := (HomologicalComplex.mapHomologyFunctorIso 0 H).app K
  let c := (K.sc 0).mapCyclesIso H
  have hp : KH.homologyπ 0 ≫ e.hom = c.hom ≫ H.map (K.homologyπ 0) :=
    mapped_homology_projection H (K.sc 0)
  have hpi : H.map (K.homologyπ 0) ≫ e.inv = c.inv ≫ KH.homologyπ 0 := by
    apply (cancel_epi c.hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← hp,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hi : c.inv ≫ KH.iCycles 0 = H.map (K.iCycles 0) := by
    apply (cancel_epi c.hom).1
    rw [Iso.hom_inv_id_assoc]
    exact (ShortComplex.mapCyclesIso_hom_iCycles (S := K.sc 0) H).symm
  let l := K.liftCycles (𝟙 (K.X 0)) 0 (by simp) (by simp)
  let lH := KH.liftCycles (𝟙 (KH.X 0)) 0 (by simp) (by simp)
  have hl : H.map l ≫ c.inv = lH := by
    apply (cancel_mono (KH.iCycles 0)).1
    rw [Category.assoc, hi, ← H.map_comp]
    simp only [l, lH, HomologicalComplex.liftCycles_i, H.map_id]
    rfl
  have hq : ChainComplex.homologyZeroClass K = l ≫ K.homologyπ 0 := by
    simpa only [Category.id_comp] using comp_homologyZeroProjection_eq_class K (𝟙 (K.X 0))
  have hqH : ChainComplex.homologyZeroClass KH = lH ≫ KH.homologyπ 0 := by
    simpa only [Category.id_comp] using comp_homologyZeroProjection_eq_class KH (𝟙 (KH.X 0))
  change H.map (ChainComplex.homologyZeroClass K) ≫ e.inv = ChainComplex.homologyZeroClass KH
  rw [hq, H.map_comp, Category.assoc, hpi, ← Category.assoc, hl, hqH]

end Preservation

section Localization

variable {J A : Type u} [Category.{u} J] [CommRing A]
  (T : Submonoid A) (M : J ⥤ ModuleCat.{u} A)

local notation "L" => ModuleCat.localizedModuleFunctor T

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma localization_complex_component_zero :
    (coefficientBarComplexLocalizationIso T M).hom.f 0 =
      (coefficientBarLocalizationObjIso T M 0).hom := by
  unfold coefficientBarComplexLocalizationIso
  rw [Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom, AlgebraicTopology.alternatingFaceMapComplex_map_f]
  change (𝟙 _ ≫ (coefficientBarLocalizationSimplicialIso T M).hom.app (op ⦋0⦌)) = _
  rw [Category.id_comp]
  unfold coefficientBarLocalizationSimplicialIso
  rw [Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom,
    SimplicialObject.Data.toSimplicialObject_mapObjIso_hom_app_mk,
    SimplicialObject.Data.toSimplicialFunctor_map_app_mk]
  change 𝟙 ((L).obj (coefficientBarObj M 0)) ≫
      (coefficientBarLocalizationObjIso T M 0).hom = _
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma localization_normalized_homology_factorization :
    (homologyWithCoefficientsLocalizationIso T M 0).hom =
      (L).map (coefficientHomologyZeroComparison M).hom ≫
        ((HomologicalComplex.mapHomologyFunctorIso 0 L).app (coefficientBarComplex M)).inv ≫
          HomologicalComplex.homologyMap (coefficientBarComplexLocalizationIso T M).hom 0 ≫
            (coefficientHomologyZeroComparison (M ⋙ L)).inv := by
  let ν := AlgebraicTopology.inclusionOfMooreComplexMap (coefficientBarSimplicial M)
  have h := (HomologicalComplex.mapHomologyFunctorIso 0 L).inv.naturality ν
  change (L).map (coefficientHomologyZeroComparison M).hom ≫
      ((HomologicalComplex.mapHomologyFunctorIso 0 L).app (coefficientBarComplex M)).inv =
    ((HomologicalComplex.mapHomologyFunctorIso 0 L).app (normalizedCoefficientBarComplex M)).inv ≫
      HomologicalComplex.homologyMap
        (((L).mapHomologicalComplex (ComplexShape.down ℕ)).map ν) 0 at h
  change ((HomologicalComplex.mapHomologyFunctorIso 0 L).app
      (normalizedCoefficientBarComplex M)).inv ≫
      HomologicalComplex.homologyMap
        ((((L).mapHomologicalComplex (ComplexShape.down ℕ)).map ν) ≫
          (coefficientBarComplexLocalizationIso T M).hom ≫
            AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
              (coefficientBarSimplicial (M ⋙ L))) 0 = _
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  change _ = (L).map (coefficientHomologyZeroComparison M).hom ≫
      ((HomologicalComplex.mapHomologyFunctorIso 0 L).app (coefficientBarComplex M)).inv ≫
        HomologicalComplex.homologyMap (coefficientBarComplexLocalizationIso T M).hom 0 ≫
          HomologicalComplex.homologyMap
            (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
              (coefficientBarSimplicial (M ⋙ L))) 0
  rw [← Category.assoc, ← Category.assoc, ← h]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Localization carries each canonical coefficient homology class to the
canonical class of the localized coefficient functor. -/
@[reassoc]
theorem map_coefficientHomologyClass_comp_homologyWithCoefficientsLocalizationIso_hom
    (i : J) :
    (L).map (coefficientHomologyClass M i) ≫ (homologyWithCoefficientsLocalizationIso T M 0).hom =
      coefficientHomologyClass (M ⋙ L) i := by
  let K := coefficientBarComplex M
  let c := coefficientBarComplexLocalizationIso T M
  let K' := coefficientBarComplex (M ⋙ L)
  let ιM : M.obj i ⟶ K.X 0 := coefficientBarι M (ComposableArrows.mk₀ i)
  let ιN : (M ⋙ L).obj i ⟶ K'.X 0 := coefficientBarι (M ⋙ L) (ComposableArrows.mk₀ i)
  let e := coefficientHomologyZeroComparison M
  let e' := coefficientHomologyZeroComparison (M ⋙ L)
  let η := (HomologicalComplex.mapHomologyFunctorIso 0 L).app K
  let LK := ((L).mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let Hc := HomologicalComplex.homologyMap c.hom 0
  have hq : (L).map (ChainComplex.homologyZeroClass K) ≫ η.inv =
      ChainComplex.homologyZeroClass LK :=
    mapped_homologyZeroProjection L K
  have hc : ChainComplex.homologyZeroClass LK ≫ Hc =
      c.hom.f 0 ≫ ChainComplex.homologyZeroClass K' :=
    ChainComplex.homologyZeroClass_naturality c.hom
  have hι : (L).map ιM ≫ c.hom.f 0 = ιN := by
    rw [localization_complex_component_zero]
    exact map_coefficientBarι_comp_coefficientBarLocalizationObjIso_hom
      T M (ComposableArrows.mk₀ i)
  have hf : (homologyWithCoefficientsLocalizationIso T M 0).hom =
      (L).map e.hom ≫ η.inv ≫ Hc ≫ e'.inv :=
    localization_normalized_homology_factorization T M
  change (L).map (ιM ≫ ChainComplex.homologyZeroClass K ≫ e.inv) ≫
      (homologyWithCoefficientsLocalizationIso T M 0).hom =
    ιN ≫ ChainComplex.homologyZeroClass K' ≫ e'.inv
  calc
    _ = (L).map ιM ≫ (L).map (ChainComplex.homologyZeroClass K) ≫
        (L).map e.inv ≫ (L).map e.hom ≫ η.inv ≫ Hc ≫ e'.inv := by
      rw [hf]
      simp only [Functor.map_comp, Category.assoc]
    _ = (L).map ιM ≫ (L).map (ChainComplex.homologyZeroClass K) ≫ η.inv ≫ Hc ≫ e'.inv := by
      exact cancel_inverse_middle ((L).map ιM) ((L).map (ChainComplex.homologyZeroClass K))
        ((L).mapIso e) η.inv Hc e'.inv
    _ = (L).map ιM ≫ ChainComplex.homologyZeroClass LK ≫ Hc ≫ e'.inv := by
      exact collapse_middle ((L).map ιM) ((L).map (ChainComplex.homologyZeroClass K))
        η.inv Hc e'.inv (ChainComplex.homologyZeroClass LK) hq
    _ = (L).map ιM ≫ c.hom.f 0 ≫ ChainComplex.homologyZeroClass K' ≫ e'.inv := by
      exact rewrite_middle_pair ((L).map ιM) (ChainComplex.homologyZeroClass LK) Hc
        (c.hom.f 0) (ChainComplex.homologyZeroClass K') e'.inv hc
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ ChainComplex.homologyZeroClass K' ≫ e'.inv) hι

end Localization

end CategoryTheory.CategoryHomology

end
