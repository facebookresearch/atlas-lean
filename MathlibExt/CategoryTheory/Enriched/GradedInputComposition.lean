/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FunctorCategory
public import MathlibExt.CategoryTheory.Enriched.GradedComposition

/-!
# Ordinary input composition in every central grade

The transformations use actual tensor composition, regrading, and the genuine
monoidal unit comparison from the ambient braided base to its center. The raw
components retain internal-Hom precomposition and postcomposition.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

private def unitGradeTensorLeft (Γ : Center V) :
    Γ ⟶ (Center.ofBraided V).obj (𝟙_ V) ⊗ Γ :=
  (λ_ Γ).inv ≫ (Functor.LaxMonoidal.ε (Center.ofBraided V) ▷ Γ)

omit [MonoidalClosed V] in
private theorem unitGradeTensorLeft_f (Γ : Center V) :
    (unitGradeTensorLeft Γ).f = (λ_ Γ.1).inv := by
  simp only [unitGradeTensorLeft, Center.comp_f, Center.leftUnitor_inv_f,
    Center.whiskerRight_f, Center.ofBraided_ε_f]
  change (λ_ Γ.1).inv ≫ (𝟙 (𝟙_ V) ▷ Γ.1) = (λ_ Γ.1).inv
  exact (congrArg (fun h : 𝟙_ V ⊗ Γ.1 ⟶ 𝟙_ V ⊗ Γ.1 => (λ_ Γ.1).inv ≫ h)
    (id_whiskerRight (𝟙_ V) Γ.1)).trans (Category.comp_id _)

private def unitGradeTensorRight (Γ : Center V) :
    Γ ⟶ Γ ⊗ (Center.ofBraided V).obj (𝟙_ V) :=
  (ρ_ Γ).inv ≫ (Γ ◁ Functor.LaxMonoidal.ε (Center.ofBraided V))

omit [MonoidalClosed V] in
private theorem unitGradeTensorRight_f (Γ : Center V) :
    (unitGradeTensorRight Γ).f = (ρ_ Γ.1).inv := by
  simp only [unitGradeTensorRight, Center.comp_f, Center.rightUnitor_inv_f,
    Center.whiskerLeft_f, Center.ofBraided_ε_f]
  change (ρ_ Γ.1).inv ≫ (Γ.1 ◁ 𝟙 (𝟙_ V)) = (ρ_ Γ.1).inv
  exact (congrArg (fun h : Γ.1 ⊗ 𝟙_ V ⟶ Γ.1 ⊗ 𝟙_ V => (ρ_ Γ.1).inv ≫ h)
    (whiskerLeft_id Γ.1 (𝟙_ V))).trans (Category.comp_id _)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for actual source composition in the center.
/-- Precompose a graded transformation using actual tensor composition and central unitality. -/
@[no_expose]
def gradedPrecomp (Γ : Center V) {F G H : EnrichedFunctorCat V A}
    (p : F ⟶ G) (t : GradedNatTrans Γ G.toEnrichedFunctor H.toEnrichedFunctor) :
    GradedNatTrans Γ F.toEnrichedFunctor H.toEnrichedFunctor :=
  GradedNatTrans.regrade (unitGradeTensorLeft Γ) (GradedNatTrans.tensorComp p t)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the full raw source component formula.
set_option backward.isDefEq.respectTransparency false in
/-- Central unitality reduces actual source composition to internal-Hom precomposition. -/
theorem gradedPrecomp_app (Γ : Center V) {F G H : EnrichedFunctorCat V A}
    (p : F ⟶ G) (t : GradedNatTrans Γ G.toEnrichedFunctor H.toEnrichedFunctor) (a : A) :
    (gradedPrecomp Γ p t).app a =
      t.app a ≫ (MonoidalClosed.pre (component p a)).app (H.toEnrichedFunctor.obj a) := by
  change (GradedNatTrans.regrade (unitGradeTensorLeft Γ)
    (GradedNatTrans.tensorComp p t)).app a = _
  rw [GradedNatTrans.regrade_app, unitGradeTensorLeft_f, GradedNatTrans.tensorComp_app]
  have hEval :
      (λ_ ((ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a))).inv ≫
          p.app a ▷ ((ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a)) ≫
          eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
            (H.toEnrichedFunctor.obj a) =
        (MonoidalClosed.pre (component p a)).app (H.toEnrichedFunctor.obj a) := by
    have h := MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight
      V (component p a) (H.toEnrichedFunctor.obj a)
    change (λ_ ((ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a))).inv ≫
        (eHomEquiv V (component p a)) ▷
          ((ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a)) ≫
        eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (H.toEnrichedFunctor.obj a) = _ at h
    simp only [component, Equiv.apply_symm_apply] at h
    exact h
  calc
    _ = (λ_ Γ.1).inv ≫ 𝟙_ V ◁ t.app a ≫
        p.app a ▷ ((ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a)) ≫
        eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (H.toEnrichedFunctor.obj a) := by
      simp only [tensorHom_def', Category.assoc]
      rfl
    _ = (t.app a ≫
          (λ_ ((ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a))).inv) ≫
        p.app a ▷ ((ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a)) ≫
        eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (H.toEnrichedFunctor.obj a) := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun h : Γ.1 ⟶ 𝟙_ V ⊗
            ((ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a)) =>
          h ≫ p.app a ▷ ((ihom (G.toEnrichedFunctor.obj a)).obj (H.toEnrichedFunctor.obj a)) ≫
            eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
              (H.toEnrichedFunctor.obj a)) (leftUnitor_inv_naturality (t.app a)).symm)
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun h => t.app a ≫ h) hEval)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for actual target composition in the center.
/-- Postcompose a graded transformation using actual tensor composition and central unitality. -/
@[no_expose]
def gradedPostcomp (Γ : Center V) {F G H : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H) :
    GradedNatTrans Γ F.toEnrichedFunctor H.toEnrichedFunctor :=
  GradedNatTrans.regrade (unitGradeTensorRight Γ) (GradedNatTrans.tensorComp t q)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the full raw target component formula.
set_option backward.isDefEq.respectTransparency false in
/-- Central unitality reduces actual target composition to the full internal-Hom map. -/
theorem gradedPostcomp_app (Γ : Center V) {F G H : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H) (a : A) :
    (gradedPostcomp Γ t q).app a =
      t.app a ≫ (ihom (F.toEnrichedFunctor.obj a)).map (component q a) := by
  change (GradedNatTrans.regrade (unitGradeTensorRight Γ)
    (GradedNatTrans.tensorComp t q)).app a = _
  rw [GradedNatTrans.regrade_app, unitGradeTensorRight_f, GradedNatTrans.tensorComp_app]
  have hEval :
      (ρ_ ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a))).inv ≫
          ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a)) ◁ q.app a ≫
          eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
            (H.toEnrichedFunctor.obj a) =
        (ihom (F.toEnrichedFunctor.obj a)).map (component q a) := by
    have h := MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft
      V (F.toEnrichedFunctor.obj a) (component q a)
    change (ρ_ ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a))).inv ≫
        ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a)) ◁
          eHomEquiv V (component q a) ≫
        eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (H.toEnrichedFunctor.obj a) = _ at h
    simp only [component, Equiv.apply_symm_apply] at h
    exact h
  calc
    _ = (ρ_ Γ.1).inv ≫ t.app a ▷ 𝟙_ V ≫
        ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a)) ◁ q.app a ≫
        eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (H.toEnrichedFunctor.obj a) := by
      simp only [tensorHom_def, Category.assoc]
      rfl
    _ = (t.app a ≫
          (ρ_ ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a))).inv) ≫
        ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a)) ◁ q.app a ≫
        eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
          (H.toEnrichedFunctor.obj a) := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun h : Γ.1 ⟶
            ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a)) ⊗ 𝟙_ V =>
          h ≫ ((ihom (F.toEnrichedFunctor.obj a)).obj (G.toEnrichedFunctor.obj a)) ◁ q.app a ≫
            eComp V (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a)
              (H.toEnrichedFunctor.obj a)) (rightUnitor_inv_naturality (t.app a)).symm)
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun h => t.app a ≫ h) hEval)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the actual source identity.
/-- Identity source transformations preserve every central-graded transformation. -/
theorem gradedPrecomp_id (Γ : Center V) {F G : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedPrecomp Γ (𝟙 F) t = t := by
  apply GradedNatTrans.ext
  funext a
  simp only [gradedPrecomp_app, component_id, MonoidalClosed.pre_id,
    NatTrans.id_app]
  exact Category.comp_id (t.app a)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for actual source composition.
/-- Source composition acts on every central grade by the original internal-Hom pre-map. -/
theorem gradedPrecomp_comp (Γ : Center V) {F G H K : EnrichedFunctorCat V A}
    (p : F ⟶ G) (q : G ⟶ H)
    (t : GradedNatTrans Γ H.toEnrichedFunctor K.toEnrichedFunctor) :
    gradedPrecomp Γ (p ≫ q) t = gradedPrecomp Γ p (gradedPrecomp Γ q t) := by
  apply GradedNatTrans.ext
  funext a
  simp only [gradedPrecomp_app, component_comp, MonoidalClosed.pre_map,
    NatTrans.comp_app, Category.assoc]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the actual target identity.
/-- Identity target transformations preserve every central-graded transformation. -/
theorem gradedPostcomp_id (Γ : Center V) {F G : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedPostcomp Γ t (𝟙 G) = t := by
  apply GradedNatTrans.ext
  funext a
  simp only [gradedPostcomp_app, component_id, Functor.map_id]
  exact Category.comp_id (t.app a)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for actual target composition.
/-- Target composition acts on every central grade by the original internal-Hom map. -/
theorem gradedPostcomp_comp (Γ : Center V) {F G H K : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor)
    (q : G ⟶ H) (r : H ⟶ K) :
    gradedPostcomp Γ t (q ≫ r) = gradedPostcomp Γ (gradedPostcomp Γ t q) r := by
  apply GradedNatTrans.ext
  funext a
  simp only [gradedPostcomp_app, component_comp, Functor.map_comp, Category.assoc]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for source action after actual regrading.
/-- Actual source composition commutes with every central reparameterization. -/
theorem gradedPrecomp_regrade {Γ Γ' : Center V} (u : Γ ⟶ Γ')
    {F G H : EnrichedFunctorCat V A} (p : F ⟶ G)
    (t : GradedNatTrans Γ' G.toEnrichedFunctor H.toEnrichedFunctor) :
    gradedPrecomp Γ p (GradedNatTrans.regrade u t) =
      GradedNatTrans.regrade u (gradedPrecomp Γ' p t) := by
  apply GradedNatTrans.ext
  funext a
  rw [gradedPrecomp_app, GradedNatTrans.regrade_app, GradedNatTrans.regrade_app,
    gradedPrecomp_app]
  exact Category.assoc _ _ _

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for target action after actual regrading.
/-- Actual target composition commutes with every central reparameterization. -/
theorem gradedPostcomp_regrade {Γ Γ' : Center V} (u : Γ ⟶ Γ')
    {F G H : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ' F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H) :
    gradedPostcomp Γ (GradedNatTrans.regrade u t) q =
      GradedNatTrans.regrade u (gradedPostcomp Γ' t q) := by
  apply GradedNatTrans.ext
  funext a
  rw [gradedPostcomp_app, GradedNatTrans.regrade_app, GradedNatTrans.regrade_app,
    gradedPostcomp_app]
  exact Category.assoc _ _ _

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for interchange of the two actual input actions.
set_option backward.isDefEq.respectTransparency false in
/-- Actual source and target composition commute on every central-graded transformation. -/
theorem gradedPrecomp_postcomp (Γ : Center V) {F' F G G' : EnrichedFunctorCat V A}
    (p : F' ⟶ F) (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ G') :
    gradedPrecomp Γ p (gradedPostcomp Γ t q) = gradedPostcomp Γ (gradedPrecomp Γ p t) q := by
  apply GradedNatTrans.ext
  funext a
  rw [gradedPrecomp_app, gradedPostcomp_app, gradedPostcomp_app, gradedPrecomp_app]
  simp only [Category.assoc]
  exact congrArg (fun h => t.app a ≫ h)
    ((MonoidalClosed.pre (component p a)).naturality (component q a))

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for source action in the genuine unit carrier.
set_option backward.isDefEq.respectTransparency false in
/-- Source action in the canonical unit grade is genuine diagram composition. -/
theorem gradedPrecomp_unit {F G H : EnrichedFunctorCat V A} (p : F ⟶ G) (t : G ⟶ H) :
    gradedPrecomp ((Center.ofBraided V).obj (𝟙_ V)) p t = p ≫ t := by
  apply hom_ext
  intro a
  change (ρ_ (F.toEnrichedFunctor.obj a)).inv ≫
      MonoidalClosed.uncurry
        ((gradedPrecomp ((Center.ofBraided V).obj (𝟙_ V)) p t).app a) = _
  rw [gradedPrecomp_app, MonoidalClosed.uncurry_pre_app, component_comp]
  change (ρ_ (F.toEnrichedFunctor.obj a)).inv ≫
      (component p a ▷ 𝟙_ V) ≫ MonoidalClosed.uncurry (t.app a) =
    component p a ≫ ((ρ_ (G.toEnrichedFunctor.obj a)).inv ≫
      MonoidalClosed.uncurry (t.app a))
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun h => h ≫ MonoidalClosed.uncurry (t.app a))
      (rightUnitor_inv_naturality (component p a)).symm)).trans (Category.assoc _ _ _)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for target action in the genuine unit carrier.
set_option backward.isDefEq.respectTransparency false in
/-- Target action in the canonical unit grade is genuine diagram composition. -/
theorem gradedPostcomp_unit {F G H : EnrichedFunctorCat V A} (t : F ⟶ G) (q : G ⟶ H) :
    gradedPostcomp ((Center.ofBraided V).obj (𝟙_ V)) t q = t ≫ q := by
  apply hom_ext
  intro a
  change (ρ_ (F.toEnrichedFunctor.obj a)).inv ≫
      MonoidalClosed.uncurry
        ((gradedPostcomp ((Center.ofBraided V).obj (𝟙_ V)) t q).app a) = _
  rw [gradedPostcomp_app, MonoidalClosed.uncurry_natural_right, component_comp]
  change (ρ_ (F.toEnrichedFunctor.obj a)).inv ≫
      MonoidalClosed.uncurry (t.app a) ≫ component q a =
    ((ρ_ (F.toEnrichedFunctor.obj a)).inv ≫ MonoidalClosed.uncurry (t.app a)) ≫ component q a
  exact (Category.assoc _ _ _).symm

end CategoryTheory.EnrichedFunctorCat
