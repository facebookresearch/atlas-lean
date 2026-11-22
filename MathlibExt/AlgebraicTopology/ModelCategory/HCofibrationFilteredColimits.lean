/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HCofibrationGluing
public import MathlibExt.AlgebraicTopology.ModelCategory.HCofibration
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Connected colimits of h-cofibrations

In a model category with colimits of a connected shape `J`, stability of weak
equivalences under `J`-colimits implies stability of h-cofibrations under the
same colimits.
The proof identifies colimits of pushout diagrams with pushouts of colimit
maps, preserving both pushout legs.
Filtered-colimit stability of weak equivalences, together with the stated
colimit existence, then yields transfinite-composition stability of
h-cofibrations.
This is the colimit argument in Pavlov–Scholbach, arXiv:1510.04969v3,
Lemma `i.cofibrations` (iv).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.HCofibrationFilteredColimits

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The filtered-colimit API uses the shared original composition theorem. -/
theorem hCof_comp {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    (hf : hCofibrations C f) (hg : hCofibrations C g) : hCofibrations C (f ≫ g) :=
  HomotopicalAlgebra.hCofibration_comp f g hf hg

section Colimits

variable {J : Type w} [Category.{w'} J] [IsConnected J]
  [HasColimitsOfShape J C]

/-- The colimit comparison of the original source cocone. -/
def coconeColimitIso {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c) : colimit F ≅ c.pt :=
  (colimit.isColimit F).coconePointUniqueUpToIso hc

/-- The colimit comparison of the original constant diagram. -/
def constantColimitIso (X : C) : colimit ((Functor.const J).obj X) ≅ X :=
  coconeColimitIso (constCocone J X) (isColimitConstCocone J X)

omit [ModelCategory C] in
theorem constantColimitIso_naturality {X Y : C} (f : X ⟶ Y) :
    colimMap ((Functor.const J).map f) ≫ (constantColimitIso (J := J) Y).hom =
      (constantColimitIso (J := J) X).hom ≫ f := by
  apply colimit.hom_ext
  intro j
  have hX : colimit.ι ((Functor.const J).obj X) j ≫
      (constantColimitIso (J := J) X).hom = 𝟙 X :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
  have hY : colimit.ι ((Functor.const J).obj Y) j ≫
      (constantColimitIso (J := J) Y).hom = 𝟙 Y :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
  rw [← Category.assoc, ι_colimMap, Category.assoc, hY]
  change f ≫ 𝟙 Y = colimit.ι ((Functor.const J).obj X) j ≫
    (constantColimitIso (J := J) X).hom ≫ f
  rw [Category.comp_id, ← Category.assoc, hX]
  exact (Category.id_comp f).symm

/-- The natural map from the original source diagram to its endpoint constant diagram. -/
def sourceToConstant {F : J ⥤ C} (c : Cocone F) {X : C} (a : c.pt ⟶ X) :
    F ⟶ (Functor.const J).obj X := c.ι ≫ (Functor.const J).map a

omit [ModelCategory C] [IsConnected J] [HasColimitsOfShape J C] in
theorem sourceToConstant_comp {F : J ⥤ C} (c : Cocone F) {X Y : C}
    (a : c.pt ⟶ X) (b : X ⟶ Y) :
    sourceToConstant c (a ≫ b) = sourceToConstant c a ≫ (Functor.const J).map b := by
  unfold sourceToConstant
  rw [Functor.map_comp, Category.assoc]

/-- The actual pointwise pushout of the original source diagrams. -/
abbrev sourcePushout {F G : J ⥤ C} (α : F ⟶ G) (c : Cocone F) {X : C} (a : c.pt ⟶ X) :
    J ⥤ C := pushout (sourceToConstant c a) α

/-- The colimit of the original pointwise pushouts has the caller's same endpoint and both legs. -/
def pushoutColimitData {F G : J ⥤ C} (α : F ⟶ G)
    (cF : Cocone F) (cG : Cocone G) (hcF : IsColimit cF) (hcG : IsColimit cG)
    (φ : cF.pt ⟶ cG.pt) (hφ : ∀ j, cF.ι.app j ≫ φ = α.app j ≫ cG.ι.app j)
    {X Y : C} (a : cF.pt ⟶ X) (q : X ⟶ Y) (b : cG.pt ⟶ Y)
    (sq : IsPushout a φ q b) :
    {e : colimit (sourcePushout α cF a) ≅ Y //
      (constantColimitIso (J := J) X).inv ≫ colimMap (pushout.inl (sourceToConstant cF a) α) ≫ e.hom = q ∧
      (coconeColimitIso cG hcG).inv ≫ colimMap (pushout.inr (sourceToConstant cF a) α) ≫ e.hom = b} := by
  let L : (J ⥤ C) ⥤ C := colim
  let eF := coconeColimitIso cF hcF
  let eG := coconeColimitIso cG hcG
  let eX := constantColimitIso (J := J) X
  have hF (j : J) : colimit.ι F j ≫ eF.hom = cF.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
  have hG (j : J) : colimit.ι G j ≫ eG.hom = cG.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
  have hX (j : J) : colimit.ι ((Functor.const J).obj X) j ≫ eX.hom = 𝟙 X :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
  have ha : L.map (sourceToConstant cF a) ≫ eX.hom = eF.hom ≫ a := by
    apply colimit.hom_ext
    intro j
    change colimit.ι F j ≫ colimMap (sourceToConstant cF a) ≫ eX.hom = _
    rw [← Category.assoc, ι_colimMap, Category.assoc, hX]
    change (cF.ι.app j ≫ a) ≫ 𝟙 X = colimit.ι F j ≫ eF.hom ≫ a
    rw [Category.comp_id, ← Category.assoc, hF]
  have hα : L.map α ≫ eG.hom = eF.hom ≫ φ := by
    apply colimit.hom_ext
    intro j
    change colimit.ι F j ≫ colimMap α ≫ eG.hom = _
    rw [← Category.assoc, ι_colimMap, Category.assoc, hG, ← hφ,
      ← Category.assoc, hF]
  let s := (IsPushout.of_hasPushout (sourceToConstant cF a) α).map L
  let q₀ : X ⟶ L.obj (sourcePushout α cF a) := eX.inv ≫ L.map (pushout.inl _ _)
  let b₀ : cG.pt ⟶ L.obj (sourcePushout α cF a) := eG.inv ≫ L.map (pushout.inr _ _)
  have s' : IsPushout a φ q₀ b₀ := s.of_iso eF eX eG (Iso.refl _) ha hα
    (by simp only [q₀, Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
    (by simp only [b₀, Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
  let e := s'.isoIsPushout _ _ sq
  refine ⟨e, ?_, ?_⟩
  · change eX.inv ≫ L.map (pushout.inl (sourceToConstant cF a) α) ≫ e.hom = q
    rw [← Category.assoc]
    exact s'.inl_isoIsPushout_hom _ _ sq
  · change eG.inv ≫ L.map (pushout.inr (sourceToConstant cF a) α) ≫ e.hom = b
    rw [← Category.assoc]
    exact s'.inr_isoIsPushout_hom _ _ sq

/-- Every actual weak map under the colimit source passes through the two genuine colimit pushouts. -/
theorem hCof_isStableUnderColimitsOfShape
    [(weakEquivalences C).IsStableUnderColimitsOfShape J] :
    (hCofibrations C).IsStableUnderColimitsOfShape J := by
  constructor
  intro F G cF cG hcF hcG α hα φ hφ X Y a q b sq
  constructor
  intro Z T r d γ st hγ
  let L : (J ⥤ C) ⥤ C := colim
  let a₀ := sourceToConstant cF a
  let a₁ := sourceToConstant cF (a ≫ γ)
  let Q := sourcePushout α cF a
  let R := sourcePushout α cF (a ≫ γ)
  let qQ : (Functor.const J).obj X ⟶ Q := pushout.inl a₀ α
  let bQ : G ⟶ Q := pushout.inr a₀ α
  let qR : (Functor.const J).obj Z ⟶ R := pushout.inl a₁ α
  let bR : G ⟶ R := pushout.inr a₁ α
  let sQ := IsPushout.of_hasPushout a₀ α
  let sR := IsPushout.of_hasPushout a₁ α
  have sR' : IsPushout (a₀ ≫ (Functor.const J).map γ) α qR bR := by
    rw [← sourceToConstant_comp]
    exact sR
  let τ : Q ⟶ R := sQ.desc ((Functor.const J).map γ ≫ qR) bR (by
    rw [← Category.assoc]
    exact sR'.w)
  have hqτ : qQ ≫ τ = (Functor.const J).map γ ≫ qR := sQ.inl_desc _ _ _
  have hbτ : bQ ≫ τ = bR := sQ.inr_desc _ _ _
  have sτ : IsPushout ((Functor.const J).map γ) qQ qR τ := IsPushout.of_left' sR' sQ
  have hτ : ∀ j : J, weakEquivalences C (τ.app j) := by
    intro j
    let E := (evaluation J C).obj j
    exact (hα j X (Q.obj j) (a₀.app j) (qQ.app j) (bQ.app j) (sQ.map E)).of_isPushout
      (sτ.flip.map E) hγ
  have hm : weakEquivalences C (L.map τ) := by
    apply MorphismProperty.colimitsOfShape_le (W := weakEquivalences C) (J := J)
    exact MorphismProperty.colimitsOfShape_colimMap (W := weakEquivalences C) τ hτ
  let dQ := pushoutColimitData α cF cG hcF hcG φ hφ a q b sq
  let dR := pushoutColimitData α cF cG hcF hcG φ hφ (a ≫ γ) r (b ≫ d) (sq.paste_horiz st.flip)
  let eQ := dQ.val
  let eR := dR.val
  let eX := constantColimitIso (J := J) X
  let eZ := constantColimitIso (J := J) Z
  let eG := coconeColimitIso cG hcG
  have hQq : L.map qQ ≫ eQ.hom = eX.hom ≫ q := by
    apply (cancel_epi eX.inv).mp
    have h := dQ.property.1
    change eX.inv ≫ L.map qQ ≫ eQ.hom = q at h
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  have hQb : L.map bQ ≫ eQ.hom = eG.hom ≫ b := by
    apply (cancel_epi eG.inv).mp
    have h := dQ.property.2
    change eG.inv ≫ L.map bQ ≫ eQ.hom = b at h
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  have hRr : L.map qR ≫ eR.hom = eZ.hom ≫ r := by
    apply (cancel_epi eZ.inv).mp
    have h := dR.property.1
    change eZ.inv ≫ L.map qR ≫ eR.hom = r at h
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  have hRb : L.map bR ≫ eR.hom = eG.hom ≫ b ≫ d := by
    apply (cancel_epi eG.inv).mp
    have h := dR.property.2
    change eG.inv ≫ L.map bR ≫ eR.hom = b ≫ d at h
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  have hγL : L.map ((Functor.const J).map γ) ≫ eZ.hom = eX.hom ≫ γ :=
    constantColimitIso_naturality γ
  have he : eQ.hom ≫ d = L.map τ ≫ eR.hom := by
    apply (sQ.map L).hom_ext
    · change L.map qQ ≫ (eQ.hom ≫ d) = L.map qQ ≫ (L.map τ ≫ eR.hom)
      rw [← Category.assoc, hQq, Category.assoc, st.w,
        ← Category.assoc (L.map qQ) (L.map τ), ← L.map_comp, hqτ, L.map_comp,
        Category.assoc, hRr]
      rw [← Category.assoc (L.map ((Functor.const J).map γ)) eZ.hom r, hγL]
      exact (Category.assoc eX.hom γ r).symm
    · change L.map bQ ≫ (eQ.hom ≫ d) = L.map bQ ≫ (L.map τ ≫ eR.hom)
      rw [← Category.assoc, hQb, Category.assoc,
        ← Category.assoc (L.map bQ) (L.map τ), ← L.map_comp, hbτ, hRb]
  exact ((weakEquivalences C).arrow_mk_iso_iff (Arrow.isoMk eQ eR he)).mp hm

end Colimits

section Transfinite

variable [MonoidalCategory C] (h : HMonoidality C)

include h in
theorem hCof_isMultiplicative : (hCofibrations C).IsMultiplicative where
  id_mem X := h.cofibrations_le_hCofibrations (𝟙 X) ((cofibration_iff _).mp inferInstance)
  comp_mem f g hf hg := HomotopicalAlgebra.hCofibration_comp f g hf hg

include h in
/-- The actual weak filtered-colimit source hypothesis earns the entire h-cofibration transfinite closure. -/
theorem hCof_isStableUnderTransfiniteComposition
    [HasColimitsOfSize.{w, w} C]
    [(weakEquivalences C).IsStableUnderFilteredColimits.{w, w}] :
    (hCofibrations C).IsStableUnderTransfiniteComposition.{w} := by
  let : (hCofibrations C).IsMultiplicative := hCof_isMultiplicative h
  constructor
  intro J _ _ _ _
  apply MorphismProperty.IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape
  intro K _ _ _ _
  let : IsConnected K := IsFiltered.isConnected K
  exact hCof_isStableUnderColimitsOfShape (J := K)

end Transfinite
end HomotopicalAlgebra.HCofibrationFilteredColimits
