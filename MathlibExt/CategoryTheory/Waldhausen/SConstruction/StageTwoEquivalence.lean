/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwoFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwoExtraction
public import Mathlib.CategoryTheory.Equivalence

/-!
# Categorical degree-two Waldhausen stage equivalence

The blueprint's categorical degree-two statement:
`CofiberSequenceCategory C ≌ Stage C 2`.

Forward is the existing `stageTwoFunctor`; inverse is `stageTwoExtraction`.
The cofiber-side unit reuses the public `stageTwo` computation laws and
`ComposableArrows` extensionality; the stage-side counit follows the
`StageOneEquivalence` componentwise pattern with the existing `Ar 2`
interval classification, using chosen-zero uniqueness on diagonals.

This is a categorical `S₂` statement only. It proves no reindexing,
simplicial object, nerve, realization, additivity, `G`-theory, or `Q`/`S`
comparison.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every diagonal `Ar 2` object equals the diagonal at its left endpoint. -/
theorem stageTwo_ar2_eq_diag_of_eq {A : Ar 2} (ha : A.left = A.right) :
    A = diag A.left := by
  cases A with
  | mk l r h =>
    have ha' : l = r := by simpa using ha
    subst ha'
    have hhom : h = homOfLE le_rfl := Subsingleton.elim _ _
    subst hhom
    rfl

/-- The staged-then-extracted underlying object has the same first leg. -/
theorem stageTwoRoundtrip_map01 (S : CofiberSequenceCategory C) :
    (((stageTwoFunctor C ⋙ stageTwoExtraction C).obj S).obj.map' 0 1) =
      S.obj.map' 0 1 := by
  have hE := stageTwoExtraction_map'_zero_one C ((stageTwoFunctor C).obj S)
  have hF := stageTwo_map_horiz_012 (C := C) (S.obj.obj' 0) (S.obj.obj' 1)
    (S.obj.obj' 2) (S.obj.map' 0 1) (S.obj.map' 1 2) S.property
    (show (0 : Fin 3) ≤ 1 by decide) (show (1 : Fin 3) ≤ 2 by decide)
  simpa [Functor.comp_obj] using hE.trans hF

/-- The staged-then-extracted underlying object has the same second leg. -/
theorem stageTwoRoundtrip_map12 (S : CofiberSequenceCategory C) :
    (((stageTwoFunctor C ⋙ stageTwoExtraction C).obj S).obj.map' 1 2) =
      S.obj.map' 1 2 := by
  have hE := stageTwoExtraction_map'_one_two C ((stageTwoFunctor C).obj S)
  have hF := stageTwo_map_vert_012 (C := C) (S.obj.obj' 0) (S.obj.obj' 1)
    (S.obj.obj' 2) (S.obj.map' 0 1) (S.obj.map' 1 2) S.property
    (show (0 : Fin 3) ≤ 1 by decide) (show (1 : Fin 3) ≤ 2 by decide)
  simpa [Functor.comp_obj] using hE.trans hF

/-- Cofiber-side unit component: staging then extracting recovers the sequence,
via identity component isomorphisms. -/
noncomputable def stageTwoUnitAppIso (S : CofiberSequenceCategory C) :
    S ≅ ((stageTwoFunctor C ⋙ stageTwoExtraction C).obj S) :=
  ObjectProperty.isoMk _ (ComposableArrows.isoMk₂
    (Iso.refl (S.obj.obj' 0)) (Iso.refl (S.obj.obj' 1)) (Iso.refl (S.obj.obj' 2))
    (by
      simp only [Iso.refl_hom, stageTwoRoundtrip_map01 C S]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
    (by
      simp only [Iso.refl_hom, stageTwoRoundtrip_map12 C S]
      exact (Category.comp_id _).trans (Category.id_comp _).symm))

/-- Naturality of the cofiber-side unit in the sequence argument. -/
theorem stageTwoUnit_naturality {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    φ ≫ (stageTwoUnitAppIso C T).hom =
      (stageTwoUnitAppIso C S).hom ≫ ((stageTwoFunctor C ⋙ stageTwoExtraction C).map φ) := by
  apply ObjectProperty.hom_ext
  apply ComposableArrows.hom_ext₂
  · simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, stageTwoUnitAppIso]
    have hEx := stageTwoExtraction_app_zero C ((stageTwoFunctor C).map φ)
    have hFu := stageTwoFunctor_map_01 C φ
    have h01E : ComposableArrows.app' (((stageTwoFunctor C ⋙ stageTwoExtraction C).map φ).hom) 0 =
        ComposableArrows.app' φ.hom 0 := by
      simpa [Functor.comp_map] using hEx.trans hFu
    change ComposableArrows.app' φ.hom 0 ≫ 𝟙 _ =
      𝟙 _ ≫ ComposableArrows.app' (((stageTwoFunctor C ⋙ stageTwoExtraction C).map φ).hom) 0
    simp only [Category.comp_id, Category.id_comp]
    exact h01E.symm
  · simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, stageTwoUnitAppIso]
    have hEx := stageTwoExtraction_app_one C ((stageTwoFunctor C).map φ)
    have hFu := stageTwoFunctor_map_02 C φ
    have h02E : ComposableArrows.app' (((stageTwoFunctor C ⋙ stageTwoExtraction C).map φ).hom) 1 =
        ComposableArrows.app' φ.hom 1 := by
      simpa [Functor.comp_map] using hEx.trans hFu
    change ComposableArrows.app' φ.hom 1 ≫ 𝟙 _ =
      𝟙 _ ≫ ComposableArrows.app' (((stageTwoFunctor C ⋙ stageTwoExtraction C).map φ).hom) 1
    simp only [Category.comp_id, Category.id_comp]
    exact h02E.symm
  · simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, stageTwoUnitAppIso]
    have hEx := stageTwoExtraction_app_two C ((stageTwoFunctor C).map φ)
    have hFu := stageTwoFunctor_map_12 C φ
    have h12E : ComposableArrows.app' (((stageTwoFunctor C ⋙ stageTwoExtraction C).map φ).hom) 2 =
        ComposableArrows.app' φ.hom 2 := by
      simpa [Functor.comp_map] using hEx.trans hFu
    change ComposableArrows.app' φ.hom 2 ≫ 𝟙 _ =
      𝟙 _ ≫ ComposableArrows.app' (((stageTwoFunctor C ⋙ stageTwoExtraction C).map φ).hom) 2
    simp only [Category.comp_id, Category.id_comp]
    exact h12E.symm

/-- Cofiber-side unit (pre-unit supplied to `Equivalence.mk`, not necessarily
definitionally the adjointified `unitIso`): extracting the staged sequence
recovers it. -/
noncomputable def stageTwoUnit :
    𝟭 (CofiberSequenceCategory C) ≅ stageTwoFunctor C ⋙ stageTwoExtraction C :=
  NatIso.ofComponents (stageTwoUnitAppIso C) (fun f => stageTwoUnit_naturality C f)

/-- The extracted-then-staged diagram is zero at every diagonal. -/
theorem stageTwoRoundtrip_obj_eq_zero_of_diag (A : Stage C 2) {B : Ar 2}
    (hb : B.left = B.right) :
    ((((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj B)) = (0 : C) := by
  have hB : B = diag B.left := stageTwo_ar2_eq_diag_of_eq hb
  rw [hB]
  exact stageTwoFunctor_obj_diag C _ _

/-- The extracted-then-staged diagram recovers the `(0, 1)` value. -/
theorem stageTwoRoundtrip_obj_eq_01 (A : Stage C 2) :
    ((((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj
      (interval (0 : Fin 3) 1 (by decide)))) =
      A.obj.obj (interval (0 : Fin 3) 1 (by decide)) := by
  simp only [Functor.comp_obj, stageTwoFunctor_obj_01]
  rfl

/-- Component isomorphism for the stage-side counit at one index. -/
noncomputable def stageTwoCounitAppIso (A : Stage C 2) (B : Ar 2) :
    (((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj B) ≅ A.obj.obj B := by
  classical
  by_cases hb : B.left = B.right
  · have hL := stageTwoRoundtrip_obj_eq_zero_of_diag C A hb
    have hA : B = diag B.left := stageTwo_ar2_eq_diag_of_eq hb
    have hR : IsZero (A.obj.obj B) := hA.symm ▸ A.property.diag_isZero _
    exact eqToIso hL ≪≫ (isZero_zero C).iso hR
  · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
    · have hB : B = interval (0 : Fin 3) 1 (by decide) :=
        stageTwo_ar2_eq_interval01 hb01
      have hL : ((((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj B)) =
          A.obj.obj (interval (0 : Fin 3) 1 (by decide)) := by
        rw [hB]
        exact stageTwoRoundtrip_obj_eq_01 C A
      have hR : A.obj.obj B = A.obj.obj (interval (0 : Fin 3) 1 (by decide)) := by
        rw [hB]
      exact eqToIso (hL.trans hR.symm)
    · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
      · have hB : B = interval (0 : Fin 3) 2 (by decide) :=
          stageTwo_ar2_eq_interval02 hb02
        have hL : ((((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj B)) =
            A.obj.obj (interval (0 : Fin 3) 2 (by decide)) := by
          rw [hB]
          simp only [Functor.comp_obj, stageTwoFunctor_obj_02]
          rfl
        have hR : A.obj.obj B = A.obj.obj (interval (0 : Fin 3) 2 (by decide)) := by
          rw [hB]
        exact eqToIso (hL.trans hR.symm)
      · have hB : B = interval (1 : Fin 3) 2 (by decide) :=
          stageTwo_ar2_eq_interval12 hb hb01 hb02
        have hL : ((((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj B)) =
            A.obj.obj (interval (1 : Fin 3) 2 (by decide)) := by
          rw [hB]
          simp only [Functor.comp_obj, stageTwoFunctor_obj_12]
          rfl
        have hR : A.obj.obj B = A.obj.obj (interval (1 : Fin 3) 2 (by decide)) := by
          rw [hB]
        exact eqToIso (hL.trans hR.symm)

/-- Naturality of the component isomorphisms in the `Ar 2` index. -/
theorem stageTwoCounitAppIso_naturality (A : Stage C 2) {B D : Ar 2} (φ : B ⟶ D) :
    ((((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.map φ)) ≫
        (stageTwoCounitAppIso C A D).hom =
      (stageTwoCounitAppIso C A B).hom ≫ A.obj.map φ := by
  classical
  by_cases hb : B.left = B.right
  · by_cases hd : D.left = D.right
    · have hEq : (((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj B) =
          (0 : C) := stageTwoRoundtrip_obj_eq_zero_of_diag C A hb
      have hL0 : IsZero (((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj B) := by
        rw [hEq]
        exact isZero_zero C
      exact hL0.eq_of_src _ _
    · have hEq : (((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj B) =
          (0 : C) := stageTwoRoundtrip_obj_eq_zero_of_diag C A hb
      have hL0 : IsZero (((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj B) := by
        rw [hEq]
        exact isZero_zero C
      exact hL0.eq_of_src _ _
  · by_cases hd : D.left = D.right
    · have hR0 : IsZero (A.obj.obj D) := by
        have hD : D = diag D.left := stageTwo_ar2_eq_diag_of_eq hd
        rw [hD]
        exact A.property.diag_isZero _
      exact hR0.eq_of_tgt _ _
    · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
      · by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
        · have hB : B = interval (0 : Fin 3) 1 (by decide) :=
            stageTwo_ar2_eq_interval01 hb01
          have hD : D = interval (0 : Fin 3) 1 (by decide) :=
            stageTwo_ar2_eq_interval01 hd01
          subst hB
          subst hD
          have hφ : φ = 𝟙 _ :=
            Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
          rw [hφ]
          simp only [Functor.map_id, Category.id_comp, Category.comp_id]
        · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
          · have hB : B = interval (0 : Fin 3) 1 (by decide) :=
              stageTwo_ar2_eq_interval01 hb01
            have hD : D = interval (0 : Fin 3) 2 (by decide) :=
              stageTwo_ar2_eq_interval02 hd02
            subst hB
            subst hD
            have hφ : φ = horiz (show (0 : Fin 3) ≤ 1 by decide)
                (show (1 : Fin 3) ≤ 2 by decide) :=
              Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
            have hL : ((((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.map φ)) =
                A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
                  (show (1 : Fin 3) ≤ 2 by decide)) := by
              rw [hφ]
              rfl
            have hR : A.obj.map φ =
                A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
                  (show (1 : Fin 3) ≤ 2 by decide)) := by
              rw [hφ]
            rw [hL, hR]
            change A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
                (show (1 : Fin 3) ≤ 2 by decide)) ≫
                eqToHom (rfl : A.obj.obj (interval (0 : Fin 3) 2 (by decide)) =
                  A.obj.obj (interval (0 : Fin 3) 2 (by decide))) =
              eqToHom (rfl : A.obj.obj (interval (0 : Fin 3) 1 (by decide)) =
                A.obj.obj (interval (0 : Fin 3) 1 (by decide))) ≫
                A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
                  (show (1 : Fin 3) ≤ 2 by decide))
            simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
          · have hB : B = interval (0 : Fin 3) 1 (by decide) :=
              stageTwo_ar2_eq_interval01 hb01
            have hD : D = interval (1 : Fin 3) 2 (by decide) :=
              stageTwo_ar2_eq_interval12 hd hd01 hd02
            subst hB
            subst hD
            have hφ : φ = (horiz (show (0 : Fin 3) ≤ 1 by decide)
                (show (1 : Fin 3) ≤ 2 by decide)) ≫
                (vert (show (0 : Fin 3) ≤ 1 by decide)
                  (show (1 : Fin 3) ≤ 2 by decide)) :=
              Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
            rw [hφ, Functor.map_comp, Functor.map_comp]
            change (A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
                (show (1 : Fin 3) ≤ 2 by decide)) ≫
                A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
                  (show (1 : Fin 3) ≤ 2 by decide))) ≫
                eqToHom (rfl : A.obj.obj (interval (1 : Fin 3) 2 (by decide)) =
                  A.obj.obj (interval (1 : Fin 3) 2 (by decide))) =
              eqToHom (rfl : A.obj.obj (interval (0 : Fin 3) 1 (by decide)) =
                A.obj.obj (interval (0 : Fin 3) 1 (by decide))) ≫
                (A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
                  (show (1 : Fin 3) ≤ 2 by decide)) ≫
                A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
                  (show (1 : Fin 3) ≤ 2 by decide)))
            simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
        · by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
          · exfalso
            have hB : B = interval (0 : Fin 3) 2 (by decide) :=
              stageTwo_ar2_eq_interval02 hb02
            have hD : D = interval (0 : Fin 3) 1 (by decide) :=
              stageTwo_ar2_eq_interval01 hd01
            subst hB
            subst hD
            have hle : (2 : Fin 3) ≤ (1 : Fin 3) := leOfHom φ.right
            exact absurd hle (by decide)
          · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
            · have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval02 hb02
              have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval02 hd02
              subst hB
              subst hD
              have hφ : φ = 𝟙 _ :=
                Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
              rw [hφ]
              simp only [Functor.map_id, Category.id_comp, Category.comp_id]
            · have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval02 hb02
              have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval12 hd hd01 hd02
              subst hB
              subst hD
              have hφ : φ = vert (show (0 : Fin 3) ≤ 1 by decide)
                  (show (1 : Fin 3) ≤ 2 by decide) :=
                Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
              rw [hφ]
              change A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
                  (show (1 : Fin 3) ≤ 2 by decide)) ≫
                  eqToHom (rfl : A.obj.obj (interval (1 : Fin 3) 2 (by decide)) =
                    A.obj.obj (interval (1 : Fin 3) 2 (by decide))) =
                eqToHom (rfl : A.obj.obj (interval (0 : Fin 3) 2 (by decide)) =
                  A.obj.obj (interval (0 : Fin 3) 2 (by decide))) ≫
                  A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
                    (show (1 : Fin 3) ≤ 2 by decide))
              simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        · by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
          · exfalso
            have hB : B = interval (1 : Fin 3) 2 (by decide) :=
              stageTwo_ar2_eq_interval12 hb hb01 hb02
            have hD : D = interval (0 : Fin 3) 1 (by decide) :=
              stageTwo_ar2_eq_interval01 hd01
            subst hB
            subst hD
            have hleL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom φ.left
            exact absurd hleL (by decide)
          · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
            · exfalso
              have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval12 hb hb01 hb02
              have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval02 hd02
              subst hB
              subst hD
              have hleL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom φ.left
              exact absurd hleL (by decide)
            · have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval12 hb hb01 hb02
              have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval12 hd hd01 hd02
              subst hB
              subst hD
              have hφ : φ = 𝟙 _ :=
                Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
              rw [hφ]
              simp only [Functor.map_id, Category.id_comp, Category.comp_id]

/-- Underlying diagram isomorphism for the stage-side counit at one stage. -/
noncomputable def stageTwoCounitUnderlyingIso (A : Stage C 2) :
    (((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj) ≅ A.obj :=
  NatIso.ofComponents (stageTwoCounitAppIso C A) (stageTwoCounitAppIso_naturality C A)

/-- Stage-side component isomorphism, lifted through the full subcategory. -/
noncomputable def stageTwoCounitAppStageIso (A : Stage C 2) :
    ((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A) ≅ A :=
  ObjectProperty.isoMk _ (stageTwoCounitUnderlyingIso C A)

/-- Naturality of the stage-side counit in the stage argument. -/
theorem stageTwoCounit_naturality {S T : Stage C 2} (f : S ⟶ T) :
    ((stageTwoExtraction C ⋙ stageTwoFunctor C).map f) ≫ (stageTwoCounitAppStageIso C T).hom =
      (stageTwoCounitAppStageIso C S).hom ≫ f := by
  apply ObjectProperty.hom_ext
  ext B
  classical
  by_cases hb : B.left = B.right
  · have hEq : ((((stageTwoExtraction C ⋙ stageTwoFunctor C).obj S).obj.obj B)) =
        (0 : C) := stageTwoRoundtrip_obj_eq_zero_of_diag C S hb
    have hLs : IsZero (((stageTwoExtraction C ⋙ stageTwoFunctor C).obj S).obj.obj B) := by
      rw [hEq]
      exact isZero_zero C
    exact hLs.eq_of_src _ _
  · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
    · have hB : B = interval (0 : Fin 3) 1 (by decide) :=
        stageTwo_ar2_eq_interval01 hb01
      subst hB
      have hmap : ((((stageTwoExtraction C ⋙ stageTwoFunctor C).map f).hom.app
          (interval (0 : Fin 3) 1 (by decide)))) =
          f.hom.app (interval (0 : Fin 3) 1 (by decide)) := by
        simp only [Functor.comp_map, stageTwoFunctor_map_01]
        exact stageTwoExtraction_app_zero C f
      simp only [stageTwoCounitAppStageIso, stageTwoCounitUnderlyingIso,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
      rw [hmap]
      change f.hom.app (interval (0 : Fin 3) 1 (by decide)) ≫
          eqToHom (rfl : T.obj.obj (interval (0 : Fin 3) 1 (by decide)) =
            T.obj.obj (interval (0 : Fin 3) 1 (by decide))) =
        eqToHom (rfl : S.obj.obj (interval (0 : Fin 3) 1 (by decide)) =
          S.obj.obj (interval (0 : Fin 3) 1 (by decide))) ≫
          f.hom.app (interval (0 : Fin 3) 1 (by decide))
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
      · have hB : B = interval (0 : Fin 3) 2 (by decide) :=
          stageTwo_ar2_eq_interval02 hb02
        subst hB
        have hmap : ((((stageTwoExtraction C ⋙ stageTwoFunctor C).map f).hom.app
            (interval (0 : Fin 3) 2 (by decide)))) =
            f.hom.app (interval (0 : Fin 3) 2 (by decide)) := by
          simp only [Functor.comp_map, stageTwoFunctor_map_02]
          exact stageTwoExtraction_app_one C f
        simp only [stageTwoCounitAppStageIso, stageTwoCounitUnderlyingIso,
          ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
        rw [hmap]
        change f.hom.app (interval (0 : Fin 3) 2 (by decide)) ≫
            eqToHom (rfl : T.obj.obj (interval (0 : Fin 3) 2 (by decide)) =
              T.obj.obj (interval (0 : Fin 3) 2 (by decide))) =
          eqToHom (rfl : S.obj.obj (interval (0 : Fin 3) 2 (by decide)) =
            S.obj.obj (interval (0 : Fin 3) 2 (by decide))) ≫
            f.hom.app (interval (0 : Fin 3) 2 (by decide))
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      · have hB : B = interval (1 : Fin 3) 2 (by decide) :=
          stageTwo_ar2_eq_interval12 hb hb01 hb02
        subst hB
        have hmap : ((((stageTwoExtraction C ⋙ stageTwoFunctor C).map f).hom.app
            (interval (1 : Fin 3) 2 (by decide)))) =
            f.hom.app (interval (1 : Fin 3) 2 (by decide)) := by
          simp only [Functor.comp_map, stageTwoFunctor_map_12]
          exact stageTwoExtraction_app_two C f
        simp only [stageTwoCounitAppStageIso, stageTwoCounitUnderlyingIso,
          ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
        rw [hmap]
        change f.hom.app (interval (1 : Fin 3) 2 (by decide)) ≫
            eqToHom (rfl : T.obj.obj (interval (1 : Fin 3) 2 (by decide)) =
              T.obj.obj (interval (1 : Fin 3) 2 (by decide))) =
          eqToHom (rfl : S.obj.obj (interval (1 : Fin 3) 2 (by decide)) =
            S.obj.obj (interval (1 : Fin 3) 2 (by decide))) ≫
            f.hom.app (interval (1 : Fin 3) 2 (by decide))
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Stage-side counit: extracting then staging recovers the stage. -/
noncomputable def stageTwoCounit :
    stageTwoExtraction C ⋙ stageTwoFunctor C ≅ 𝟭 (Stage C 2) :=
  NatIso.ofComponents (stageTwoCounitAppStageIso C) (fun f => stageTwoCounit_naturality C f)

/-- Categorical degree-two equivalence from cofiber sequences to stages. -/
noncomputable def stageTwoEquivalence : CofiberSequenceCategory C ≌ Stage C 2 :=
  CategoryTheory.Equivalence.mk (stageTwoFunctor C) (stageTwoExtraction C)
    (stageTwoUnit C) (stageTwoCounit C)

/-- Forward projection of the degree-two equivalence. -/
@[simp]
theorem stageTwoEquivalence_functor :
    (stageTwoEquivalence C).functor = stageTwoFunctor C :=
  rfl

/-- Inverse projection of the degree-two equivalence. -/
@[simp]
theorem stageTwoEquivalence_inverse :
    (stageTwoEquivalence C).inverse = stageTwoExtraction C :=
  rfl

end CategoryTheory.Waldhausen.SConstruction
