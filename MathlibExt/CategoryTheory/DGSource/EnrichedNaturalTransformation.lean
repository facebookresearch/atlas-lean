/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Enriched/NaturalTransformation.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.Tactic.ApplyFun

/-!
# Natural transformations at the monoidal unit

The monoidal unit gives graded natural transformations with ordinary components. This module
relates their graded naturality to naturality after forgetting enrichment, and provides identity
and composition for these transformations.
-/

public section

open CategoryTheory MonoidalCategory

universe v u₁ u₂ w

namespace MathlibExt.DGSource

section GradedBridge

variable {V : Type v} [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
variable {C' : Type u₁} {D' : Type u₂} [EnrichedCategory V C'] [EnrichedCategory V D']

/-- Graded natural transformations whose degree is the monoidal unit. -/
abbrev UnitGradedNatTrans (F G : EnrichedFunctor V C' D') :=
  GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G

/-- Graded naturality at the monoidal unit is equivalent to the ordinary whiskering square.
The two sides differ by precomposition with the left unitor and the unit braiding. -/
theorem unitGradedNaturality_iff
    (F G : EnrichedFunctor V C' D') (X Y : C')
    (aX : 𝟙_ V ⟶ F.obj X ⟶[V] G.obj X)
    (aY : 𝟙_ V ⟶ F.obj Y ⟶[V] G.obj Y) :
    ((β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
      (F.map X Y ⊗ₘ aY) ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) =
      (aX ⊗ₘ G.map X Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y)) ↔
    (F.map X Y ≫ eHomWhiskerLeft V (ForgetEnrichment.of V (F.obj X))
      (ForgetEnrichment.homOf V aY) =
    G.map X Y ≫ eHomWhiskerRight V (ForgetEnrichment.homOf V aX)
      (ForgetEnrichment.of V (G.obj Y))) := by
  -- Unfold the two whiskers into unitors and enriched composition.
  change _ ↔
    (F.map X Y ≫ (ρ_ (F.obj X ⟶[V] F.obj Y)).inv ≫
      (F.obj X ⟶[V] F.obj Y) ◁ aY ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) =
    G.map X Y ≫ (λ_ (G.obj X ⟶[V] G.obj Y)).inv ≫
      aX ▷ (G.obj X ⟶[V] G.obj Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y))
  have hl : (λ_ (X ⟶[V] Y)).hom ≫ F.map X Y ≫ (ρ_ (F.obj X ⟶[V] F.obj Y)).inv ≫
      (F.obj X ⟶[V] F.obj Y) ◁ aY = (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ₘ aY) := by
    rw [← rightUnitor_inv_comp_tensorHom, braiding_tensorUnit_left, Category.assoc]
  have hr : (λ_ (X ⟶[V] Y)).hom ≫ G.map X Y ≫ (λ_ (G.obj X ⟶[V] G.obj Y)).inv ≫
      aX ▷ (G.obj X ⟶[V] G.obj Y) = aX ⊗ₘ G.map X Y := by
    rw [← leftUnitor_inv_comp_tensorHom]
    simp
  -- Rewrite the graded square by `hl` and `hr`, then cancel the left unitor.
  rw [← reassoc_of% hl, ← reassoc_of% hr, cancel_epi]

private theorem unitGradedNaturality
    (F G : EnrichedFunctor V C' D') (X Y : C')
    (aX : 𝟙_ V ⟶ F.obj X ⟶[V] G.obj X)
    (aY : 𝟙_ V ⟶ F.obj Y ⟶[V] G.obj Y)
    (h : (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
      (F.map X Y ⊗ₘ aY) ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) =
      (aX ⊗ₘ G.map X Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y))
    (f : 𝟙_ V ⟶ X ⟶[V] Y) :
    (λ_ (𝟙_ V)).inv ≫ ((f ≫ F.map X Y) ⊗ₘ aY) ≫
      eComp V (F.obj X) (F.obj Y) (G.obj Y) =
    (λ_ (𝟙_ V)).inv ≫ (aX ⊗ₘ (f ≫ G.map X Y)) ≫
      eComp V (F.obj X) (G.obj X) (G.obj Y) := by
  have hs := (unitGradedNaturality_iff F G X Y aX aY).mp h
  have hs' := congrArg (fun q => f ≫ q) hs
  -- A morphism in `ForgetEnrichment` is a unit-shaped enriched morphism; expand its whiskers.
  change f ≫ F.map X Y ≫ (ρ_ (F.obj X ⟶[V] F.obj Y)).inv ≫
      (F.obj X ⟶[V] F.obj Y) ◁ aY ≫ eComp V (F.obj X) (F.obj Y) (G.obj Y) =
    f ≫ G.map X Y ≫ (λ_ (G.obj X ⟶[V] G.obj Y)).inv ≫
      aX ▷ (G.obj X ⟶[V] G.obj Y) ≫ eComp V (F.obj X) (G.obj X) (G.obj Y) at hs'
  have hL : (λ_ (𝟙_ V)).inv ≫ ((f ≫ F.map X Y) ⊗ₘ aY) =
      f ≫ F.map X Y ≫ (ρ_ (F.obj X ⟶[V] F.obj Y)).inv ≫
        (F.obj X ⟶[V] F.obj Y) ◁ aY := by
    rw [unitors_inv_equal, rightUnitor_inv_comp_tensorHom]
    simp only [Category.assoc]
  have hR : (λ_ (𝟙_ V)).inv ≫ (aX ⊗ₘ (f ≫ G.map X Y)) =
      f ≫ G.map X Y ≫ (λ_ (G.obj X ⟶[V] G.obj Y)).inv ≫
        aX ▷ (G.obj X ⟶[V] G.obj Y) := by
    rw [leftUnitor_inv_comp_tensorHom]
    simp only [Category.assoc]
  rw [reassoc_of% hL, reassoc_of% hR]
  exact hs'

namespace UnitGradedNatTrans

/-- Forget enrichment of a graded natural transformation at the monoidal unit. -/
noncomputable def toOrdinary
    {F G : EnrichedFunctor V C' D'}
    (α : UnitGradedNatTrans F G) :
    F.forget ⟶ G.forget where
  app X := α.app (ForgetEnrichment.to V X)
  naturality := by
    intro X Y f
    apply_fun ForgetEnrichment.homTo V
    · -- The ordinary components are `homOf` of the graded components.
      change
        ForgetEnrichment.homTo V
          (F.forget.map f ≫ ForgetEnrichment.homOf (C := D') V (α.app _)) =
        ForgetEnrichment.homTo V
          (ForgetEnrichment.homOf (C := D') V (α.app _) ≫ G.forget.map f)
      simp only [ForgetEnrichment.homTo_comp, EnrichedFunctor.forget_map]
      dsimp [ForgetEnrichment.homTo, ForgetEnrichment.homOf,
        ForgetEnrichment.to, ForgetEnrichment.of]
      simpa only [ForgetEnrichment.to, ForgetEnrichment.homTo, Category.assoc] using
        (unitGradedNaturality F G (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y)
          (α.app _) (α.app _) (α.naturality _ _) (ForgetEnrichment.homTo V f))
    · intro a b hab
      simpa using congrArg (ForgetEnrichment.homOf V) hab

/-- Forgetting enrichment leaves the component of a unit-graded transformation unchanged. -/
@[simp]
theorem toOrdinary_app
    {F G : EnrichedFunctor V C' D'}
    (α : UnitGradedNatTrans F G) (X : C') :
    (toOrdinary α).app (ForgetEnrichment.of V X) =
      ForgetEnrichment.homOf V (α.app X) := by
  unfold toOrdinary
  rfl

end UnitGradedNatTrans

omit [BraidedCategory V] in
/-- Two enriched whiskering squares compose along their ordinary components. -/
theorem comp_eHomWhiskerLeft_comp_eq_comp_eHomWhiskerRight_comp
    {E : Type u₂} [Category E] [EnrichedOrdinaryCategory V E]
    {FX GX HX FY GY HY : E} {M : V}
    (fMap : M ⟶ FX ⟶[V] FY) (gMap : M ⟶ GX ⟶[V] GY)
    (hMap : M ⟶ HX ⟶[V] HY)
    (aX : FX ⟶ GX) (aY : FY ⟶ GY)
    (bX : GX ⟶ HX) (bY : GY ⟶ HY)
    (ha : fMap ≫ eHomWhiskerLeft V FX aY =
      gMap ≫ eHomWhiskerRight V aX GY)
    (hb : gMap ≫ eHomWhiskerLeft V GX bY =
      hMap ≫ eHomWhiskerRight V bX HY) :
    fMap ≫ eHomWhiskerLeft V FX (aY ≫ bY) =
      hMap ≫ eHomWhiskerRight V (aX ≫ bX) HY := by
  rw [eHomWhiskerLeft_comp, eHomWhiskerRight_comp, reassoc_of% ha, ← eHom_whisker_exchange,
    reassoc_of% hb]

namespace UnitGradedNatTrans

/-- Composition of graded natural transformations at the monoidal unit. -/
noncomputable def comp {F G H : EnrichedFunctor V C' D'}
    (α : UnitGradedNatTrans F G)
    (γ : UnitGradedNatTrans G H) :
    UnitGradedNatTrans F H where
  app X := eHomEquiv V
    (ForgetEnrichment.homOf V (α.app X) ≫ ForgetEnrichment.homOf V (γ.app X))
  naturality X Y := by
    have hα := (unitGradedNaturality_iff F G X Y (α.app X) (α.app Y)).mp (α.naturality X Y)
    have hγ := (unitGradedNaturality_iff G H X Y (γ.app X) (γ.app Y)).mp (γ.naturality X Y)
    dsimp [Center.ofBraided, Center.ofBraidedObj] at hα hγ ⊢
    apply (unitGradedNaturality_iff F H X Y _ _).mpr
    let aX := ForgetEnrichment.homOf V (α.app X)
    let aY := ForgetEnrichment.homOf V (α.app Y)
    let bX := ForgetEnrichment.homOf V (γ.app X)
    let bY := ForgetEnrichment.homOf V (γ.app Y)
    -- `eHomEquiv` is the identity equivalence on the forgetful ordinary category.
    change F.map X Y ≫ eHomWhiskerLeft V (ForgetEnrichment.of V (F.obj X))
        (aY ≫ bY) =
      H.map X Y ≫ eHomWhiskerRight V (aX ≫ bX)
        (ForgetEnrichment.of V (H.obj Y))
    exact comp_eHomWhiskerLeft_comp_eq_comp_eHomWhiskerRight_comp (V := V)
      (F.map X Y) (G.map X Y) (H.map X Y) aX aY bX bY hα hγ

/-- A component of the composite at the monoidal unit. -/
-- This remains outside `simp`: it would make `comp_app_homOf` fail `simpNF`.
theorem comp_app {F G H : EnrichedFunctor V C' D'}
    (α : UnitGradedNatTrans F G)
    (γ : UnitGradedNatTrans G H) (X : C') :
    (comp α γ).app X = eHomEquiv V
      (ForgetEnrichment.homOf V (α.app X) ≫ ForgetEnrichment.homOf V (γ.app X)) := by
  unfold comp
  rfl

/-- The ordinary component of a composite is the composite of ordinary components. -/
@[simp]
theorem comp_app_homOf {F G H : EnrichedFunctor V C' D'}
    (α : UnitGradedNatTrans F G)
    (γ : UnitGradedNatTrans G H) (X : C') :
    ForgetEnrichment.homOf V ((comp α γ).app X) =
      ForgetEnrichment.homOf V (α.app X) ≫ ForgetEnrichment.homOf V (γ.app X) := by
  rw [comp_app]
  -- `eHomEquiv` is the identity equivalence on `ForgetEnrichment`.
  rfl

/-- Identity graded natural transformation at the monoidal unit. -/
noncomputable def id (F : EnrichedFunctor V C' D') : UnitGradedNatTrans F F where
  app X := eId V (F.obj X)
  naturality X Y := by
    dsimp [Center.ofBraided, Center.ofBraidedObj]
    -- Put `eId` next to `eComp` on both sides; `simp` then closes the goal with the enriched
    -- unit laws `e_comp_id` and `e_id_comp` and the unit braiding `braiding_tensorUnit_left`.
    rw [tensorHom_def]
    conv_rhs => rw [tensorHom_def']
    simp

/-- A component of the identity at the monoidal unit. -/
@[simp]
theorem id_app (F : EnrichedFunctor V C' D') (X : C') :
    (id F).app X = eId V (F.obj X) := by
  unfold id
  rfl

end UnitGradedNatTrans

end GradedBridge

end MathlibExt.DGSource
