/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.GradedInputComposition

/-!
# Full graded composition and genuine ordinary input actions

The raw component laws use complete enriched composition and its ordinary
source, target and middle naturalities. Both central grades are retained.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV uD vD
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for full enriched middle-arrow naturality.
private theorem enrichedComp_middle {D : Type uD} [Category.{vD} D]
    [EnrichedOrdinaryCategory V D] (F G H K : D) (q : G ⟶ H) :
    (eHomWhiskerLeft V F q ▷ (H ⟶[V] K)) ≫ eComp V F H K =
      ((F ⟶[V] G) ◁ eHomWhiskerRight V q K) ≫ eComp V F G K := by
  dsimp only [eHomWhiskerLeft, eHomWhiskerRight]
  rw [comp_whiskerRight_assoc, comp_whiskerRight_assoc, ← e_assoc',
    associator_naturality_middle_assoc,
    ← triangle_assoc_comp_left_inv_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp]

variable [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the full raw codomain composition equation.
omit [BraidedCategory V] in
private theorem closedComp_target (F G H K : V) (q : H ⟶ K) :
    eComp V F G H ≫ (ihom F).map q =
      ((ihom F).obj G ◁ (ihom G).map q) ≫ eComp V F G K := by
  have h := eComp_eHomWhiskerLeft V F G q
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft] at h
  exact h

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the full raw source composition equation.
omit [BraidedCategory V] in
private theorem closedComp_source (F' F G H : V) (p : F' ⟶ F) :
    eComp V F G H ≫ (MonoidalClosed.pre p).app H =
      ((MonoidalClosed.pre p).app G ▷ (ihom G).obj H) ≫ eComp V F' G H := by
  have h := eComp_eHomWhiskerRight V p G H
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at h
  exact h

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the full raw middle composition equation.
omit [BraidedCategory V] in
private theorem closedComp_middle (F G H K : V) (q : G ⟶ H) :
    ((ihom F).map q ▷ (ihom H).obj K) ≫ eComp V F H K =
      ((ihom F).obj G ◁ (MonoidalClosed.pre q).app K) ≫ eComp V F G K := by
  have h := enrichedComp_middle (V := V) F G H K q
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at h
  exact h

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for genuine postcomposition in both central grades.
set_option backward.isDefEq.respectTransparency false in
/-- Tensor composition commutes with every genuine final target transformation. -/
theorem tensorComp_gradedPostcomp {Γ Δ : Center V} {F G H K : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor)
    (u : GradedNatTrans Δ G.toEnrichedFunctor H.toEnrichedFunctor) (q : H ⟶ K) :
    gradedPostcomp (Γ ⊗ Δ) (GradedNatTrans.tensorComp t u) q =
      GradedNatTrans.tensorComp t (gradedPostcomp Δ u q) := by
  apply GradedNatTrans.ext
  funext a
  rw [gradedPostcomp_app, GradedNatTrans.tensorComp_app,
    GradedNatTrans.tensorComp_app, gradedPostcomp_app]
  have hc := closedComp_target (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
    (H.toEnrichedFunctor.obj a) (K.toEnrichedFunctor.obj a) (component q a)
  have ht : (t.app a ⊗ₘ u.app a) ≫
      ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a) ◁
        (ihom (G.toEnrichedFunctor.obj a)).map (component q a)) =
    t.app a ⊗ₘ (u.app a ≫ (ihom (G.toEnrichedFunctor.obj a)).map (component q a)) := by
    simp only [tensorHom_def, Category.assoc]
    exact congrArg (fun h => (t.app a ▷ Δ.1) ≫ h)
      (whiskerLeft_comp
        ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a)) (u.app a)
        ((ihom (G.toEnrichedFunctor.obj a)).map (component q a))).symm
  calc
    _ = (t.app a ⊗ₘ u.app a) ≫
        eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (H.toEnrichedFunctor.obj a) ≫
        (ihom (F.toEnrichedFunctor.obj a)).map (component q a) := Category.assoc _ _ _
    _ = (t.app a ⊗ₘ u.app a) ≫
        ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a) ◁
          (ihom (G.toEnrichedFunctor.obj a)).map (component q a)) ≫
        eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (K.toEnrichedFunctor.obj a) := congrArg (fun h => (t.app a ⊗ₘ u.app a) ≫ h) hc
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun h => h ≫ eComp V (F.toEnrichedFunctor.obj a)
        (G.toEnrichedFunctor.obj a) (K.toEnrichedFunctor.obj a)) ht)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for genuine precomposition in both central grades.
set_option backward.isDefEq.respectTransparency false in
/-- Tensor composition commutes with every genuine initial source transformation. -/
theorem tensorComp_gradedPrecomp {Γ Δ : Center V} {F' F G H : EnrichedFunctorCat V A}
    (p : F' ⟶ F) (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor)
    (u : GradedNatTrans Δ G.toEnrichedFunctor H.toEnrichedFunctor) :
    gradedPrecomp (Γ ⊗ Δ) p (GradedNatTrans.tensorComp t u) =
      GradedNatTrans.tensorComp (gradedPrecomp Γ p t) u := by
  apply GradedNatTrans.ext
  funext a
  rw [gradedPrecomp_app, GradedNatTrans.tensorComp_app,
    GradedNatTrans.tensorComp_app, gradedPrecomp_app]
  have hc := closedComp_source (F'.toEnrichedFunctor.obj a) (F.toEnrichedFunctor.obj a)
    (G.toEnrichedFunctor.obj a) (H.toEnrichedFunctor.obj a) (component p a)
  have ht : (t.app a ⊗ₘ u.app a) ≫
      ((MonoidalClosed.pre (component p a)).app (G.toEnrichedFunctor.obj a) ▷
        (ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a)) =
      (t.app a ≫ (MonoidalClosed.pre (component p a)).app
        (G.toEnrichedFunctor.obj a)) ⊗ₘ u.app a := by
    simp only [tensorHom_def', Category.assoc]
    exact congrArg (fun h => (Γ.1 ◁ u.app a) ≫ h)
      (comp_whiskerRight (t.app a)
        ((MonoidalClosed.pre (component p a)).app (G.toEnrichedFunctor.obj a))
        ((ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a))).symm
  calc
    _ = (t.app a ⊗ₘ u.app a) ≫
        eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (H.toEnrichedFunctor.obj a) ≫
        (MonoidalClosed.pre (component p a)).app (H.toEnrichedFunctor.obj a) :=
      Category.assoc _ _ _
    _ = (t.app a ⊗ₘ u.app a) ≫
        ((MonoidalClosed.pre (component p a)).app (G.toEnrichedFunctor.obj a) ▷
          (ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a)) ≫
        eComp V (F'.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (H.toEnrichedFunctor.obj a) := congrArg (fun h => (t.app a ⊗ₘ u.app a) ≫ h) hc
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun h => h ≫ eComp V (F'.toEnrichedFunctor.obj a)
        (G.toEnrichedFunctor.obj a) (H.toEnrichedFunctor.obj a)) ht)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for full graded middle-arrow interchange.
set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary genuine middle transformation moves between both full graded factors. -/
theorem tensorComp_gradedMiddle {Γ Δ : Center V} {F G H K : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H)
    (u : GradedNatTrans Δ H.toEnrichedFunctor K.toEnrichedFunctor) :
    GradedNatTrans.tensorComp (gradedPostcomp Γ t q) u =
      GradedNatTrans.tensorComp t (gradedPrecomp Δ q u) := by
  apply GradedNatTrans.ext
  funext a
  rw [GradedNatTrans.tensorComp_app, gradedPostcomp_app,
    GradedNatTrans.tensorComp_app, gradedPrecomp_app]
  have hc := closedComp_middle (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
    (H.toEnrichedFunctor.obj a) (K.toEnrichedFunctor.obj a) (component q a)
  have hL : (t.app a ⊗ₘ u.app a) ≫
      ((ihom (F.toEnrichedFunctor.obj a)).map (component q a) ▷
        (ihom (H.toEnrichedFunctor.obj a)).obj (K.toEnrichedFunctor.obj a)) =
    (t.app a ≫ (ihom (F.toEnrichedFunctor.obj a)).map (component q a)) ⊗ₘ u.app a := by
    simp only [tensorHom_def', Category.assoc]
    exact congrArg (fun h => (Γ.1 ◁ u.app a) ≫ h)
      (comp_whiskerRight (t.app a)
        ((ihom (F.toEnrichedFunctor.obj a)).map (component q a))
        ((ihom (H.toEnrichedFunctor.obj a)).obj (K.toEnrichedFunctor.obj a))).symm
  have hR : (t.app a ⊗ₘ u.app a) ≫
      ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a) ◁
        (MonoidalClosed.pre (component q a)).app (K.toEnrichedFunctor.obj a)) =
      t.app a ⊗ₘ (u.app a ≫ (MonoidalClosed.pre (component q a)).app
        (K.toEnrichedFunctor.obj a)) := by
    simp only [tensorHom_def, Category.assoc]
    exact congrArg (fun h => (t.app a ▷ Δ.1) ≫ h)
      (whiskerLeft_comp
        ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a)) (u.app a)
        ((MonoidalClosed.pre (component q a)).app (K.toEnrichedFunctor.obj a))).symm
  calc
    _ = (t.app a ⊗ₘ u.app a) ≫
        ((ihom (F.toEnrichedFunctor.obj a)).map (component q a) ▷
          (ihom (H.toEnrichedFunctor.obj a)).obj (K.toEnrichedFunctor.obj a)) ≫
        eComp V (F.toEnrichedFunctor.obj a) (H.toEnrichedFunctor.obj a)
          (K.toEnrichedFunctor.obj a) :=
      (congrArg (fun h => h ≫ eComp V (F.toEnrichedFunctor.obj a)
        (H.toEnrichedFunctor.obj a) (K.toEnrichedFunctor.obj a)) hL.symm).trans
        (Category.assoc _ _ _)
    _ = (t.app a ⊗ₘ u.app a) ≫
        ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a) ◁
          (MonoidalClosed.pre (component q a)).app (K.toEnrichedFunctor.obj a)) ≫
        eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (K.toEnrichedFunctor.obj a) := congrArg (fun h => (t.app a ⊗ₘ u.app a) ≫ h) hc
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun h => h ≫ eComp V (F.toEnrichedFunctor.obj a)
        (G.toEnrichedFunctor.obj a) (K.toEnrichedFunctor.obj a)) hR)

end CategoryTheory.EnrichedFunctorCat
