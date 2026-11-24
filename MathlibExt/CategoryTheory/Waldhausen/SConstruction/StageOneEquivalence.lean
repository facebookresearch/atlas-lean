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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOne
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FiniteStage
public import Mathlib.CategoryTheory.Equivalence

/-!
# Categorical degree-one Waldhausen stage equivalence

The blueprint's categorical degree-one statement: `C ≌ Stage C 1`.

Forward is the existing `stageOne C`; inverse is `stageOneEval C`, which evaluates
at the unique off-diagonal interval `(0, 1)`. The `C`-side isomorphism reuses
`stageOne_obj_interval_zero_one` and `stageOne_map_interval_zero_one`.
The `Stage C 1`-side isomorphism is built componentwise: chosen-zero
isomorphisms on diagonals and transported identities at the unique
off-diagonal, following the four-case diagonal/off-diagonal pattern from
`StageOne.lean` with its `Fin 2` order argument.

This is a categorical `S₁` statement only. It proves no simplicial object,
nerve, realization, weak equivalence, `K`/`G`-theory group identification,
or `Q`/`S` comparison.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Inverse direction: evaluation at the unique off-diagonal `(0, 1)` interval. -/
noncomputable def stageOneEval : Stage C 1 ⥤ C :=
  eval C 1 (interval (0 : Fin 2) 1 (by decide))

/-- The composite `stageOne ⋙ stageOneEval` is the identity on objects. -/
theorem stageOneEval_obj (X : C) :
    ((stageOne C ⋙ stageOneEval C).obj X) = X :=
  stageOne_obj_interval_zero_one C X (by decide : (0 : Fin 2) ≤ 1)

/-- The composite `stageOne ⋙ stageOneEval` is the identity on maps. -/
private theorem stageOneEval_map {X Y : C} (f : X ⟶ Y) :
    ((stageOne C ⋙ stageOneEval C).map f) = f :=
  stageOne_map_interval_zero_one C f

/-- `C`-side unit: evaluating the canonical stage recovers the object,
as definitional as the accepted API allows. -/
noncomputable def stageOneEvalUnit : 𝟭 C ≅ stageOne C ⋙ stageOneEval C :=
  NatIso.ofComponents
    (fun X => eqToIso (stageOneEval_obj C X).symm)
    (fun {X Y} f => by
      have hcomp : ((stageOne C ⋙ stageOneEval C).map f) =
          (stageOneEval C).map ((stageOne C).map f) := rfl
      have hmap : (stageOneEval C).map ((stageOne C).map f) = f :=
        stageOneEval_map C f
      have hFmap : ((stageOne C ⋙ stageOneEval C).map f) = f :=
        hcomp.trans hmap
      have hX : ((stageOne C ⋙ stageOneEval C).obj X) = X :=
        stageOneEval_obj C X
      have hY : ((stageOne C ⋙ stageOneEval C).obj Y) = Y :=
        stageOneEval_obj C Y
      have hL : f ≫ eqToHom hY.symm ≍ f :=
        comp_eqToHom_heq f hY.symm
      have hR : eqToHom hX.symm ≫ ((stageOne C ⋙ stageOneEval C).map f) ≍
          ((stageOne C ⋙ stageOneEval C).map f) :=
        eqToHom_comp_heq _ hX.symm
      have hHEq : ((stageOne C ⋙ stageOneEval C).map f) ≍ f :=
        heq_of_eq hFmap
      exact eq_of_heq (hL.trans (hHEq.symm.trans hR.symm)))

/-- Every diagonal `Ar 1` object equals the diagonal at its left endpoint. -/
private theorem ar1_eq_diag_of_eq {A : Ar 1} (ha : A.left = A.right) :
    A = diag A.left := by
  cases A with
  | mk l r h =>
    have ha' : l = r := by simpa using ha
    subst ha'
    have hhom : h = homOfLE le_rfl := Subsingleton.elim _ _
    subst hhom
    rfl

/-- The canonical stage diagram is zero at every diagonal `Ar 1` object. -/
theorem stageOne_obj_eq_zero_of_diag (X : C) {A : Ar 1}
    (ha : A.left = A.right) :
    (((stageOne C).obj X).obj.obj A) = (0 : C) := by
  have hA : A = diag A.left := ar1_eq_diag_of_eq ha
  rw [hA]
  exact stageOne_obj_diag C X _

/-- The canonical stage diagram recovers `X` at every off-diagonal object. -/
theorem stageOne_obj_eq_X_of_offdiag (X : C) {A : Ar 1}
    (hne : ¬ A.left = A.right) :
    (((stageOne C).obj X).obj.obj A) = X := by
  have hA : A = interval (0 : Fin 2) 1 (by decide) :=
    ar1_eq_interval01_of_ne hne
  rw [hA]
  exact stageOne_obj_interval_zero_one C X _

/-- Every stage diagram is zero at every diagonal `Ar 1` object. -/
theorem isZero_stage_obj_of_diag (S : Stage C 1) {A : Ar 1}
    (ha : A.left = A.right) : IsZero (S.obj.obj A) := by
  have hA : A = diag A.left := ar1_eq_diag_of_eq ha
  rw [hA]
  exact S.property.diag_isZero _

/-- Every stage diagram agrees with evaluation at every off-diagonal object. -/
theorem stage_obj_eq_eval_of_offdiag (S : Stage C 1) {A : Ar 1}
    (hne : ¬ A.left = A.right) :
    S.obj.obj A = (stageOneEval C).obj S := by
  have hA : A = interval (0 : Fin 2) 1 (by decide) :=
    ar1_eq_interval01_of_ne hne
  rw [hA]
  rfl

/-- Component isomorphism for the `Stage`-side counit at one index. -/
noncomputable def counitAppIso (S : Stage C 1) (A : Ar 1) :
    ((((stageOneEval C ⋙ stageOne C).obj S).obj.obj A)) ≅ S.obj.obj A := by
  classical
  by_cases ha : A.left = A.right
  · have hL : ((((stageOneEval C ⋙ stageOne C).obj S).obj.obj A)) = (0 : C) :=
      stageOne_obj_eq_zero_of_diag C _ ha
    have hR : IsZero (S.obj.obj A) := isZero_stage_obj_of_diag C S ha
    exact eqToIso hL ≪≫ (isZero_zero C).iso hR
  · have hL : ((((stageOneEval C ⋙ stageOne C).obj S).obj.obj A)) =
        (stageOneEval C).obj S :=
      stageOne_obj_eq_X_of_offdiag C _ ha
    have hR : S.obj.obj A = (stageOneEval C).obj S :=
      stage_obj_eq_eval_of_offdiag C S ha
    exact eqToIso (hL.trans hR.symm)

/-- Naturality of the component isomorphisms in the `Ar 1` index. -/
theorem counitAppIso_naturality (S : Stage C 1) {A B : Ar 1}
    (φ : A ⟶ B) :
    ((((stageOneEval C ⋙ stageOne C).obj S).obj.map φ)) ≫
        (counitAppIso C S B).hom =
      (counitAppIso C S A).hom ≫ S.obj.map φ := by
  classical
  by_cases ha : A.left = A.right
  · by_cases hb : B.left = B.right
    · have hEq : ((((stageOneEval C ⋙ stageOne C).obj S).obj.obj A)) = (0 : C) :=
        stageOne_obj_eq_zero_of_diag C _ ha
      have hL0 : IsZero (((((stageOneEval C ⋙ stageOne C).obj S).obj.obj A))) := by
        rw [hEq]
        exact isZero_zero C
      exact hL0.eq_of_src _ _
    · have hEq : ((((stageOneEval C ⋙ stageOne C).obj S).obj.obj A)) = (0 : C) :=
        stageOne_obj_eq_zero_of_diag C _ ha
      have hL0 : IsZero (((((stageOneEval C ⋙ stageOne C).obj S).obj.obj A))) := by
        rw [hEq]
        exact isZero_zero C
      exact hL0.eq_of_src _ _
  · by_cases hb : B.left = B.right
    · have hR0 : IsZero (S.obj.obj B) := isZero_stage_obj_of_diag C S hb
      exact hR0.eq_of_tgt _ _
    · have hA : A = interval (0 : Fin 2) 1 (by decide) :=
        ar1_eq_interval01_of_ne ha
      have hB : B = interval (0 : Fin 2) 1 (by decide) :=
        ar1_eq_interval01_of_ne hb
      subst hA
      subst hB
      have : Subsingleton
          (interval (0 : Fin 2) 1 (by decide) ⟶ interval (0 : Fin 2) 1 (by decide)) :=
        ⟨fun f g => Arrow.hom_ext f g (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
      have hφ : φ = 𝟙 _ := Subsingleton.elim _ _
      rw [hφ]
      simp only [Functor.map_id, Category.id_comp, Category.comp_id]

/-- Underlying diagram isomorphism for the `Stage`-side counit at one stage. -/
noncomputable def counitUnderlyingIso (S : Stage C 1) :
    (((stageOneEval C ⋙ stageOne C).obj S).obj) ≅ S.obj :=
  NatIso.ofComponents (counitAppIso C S) (counitAppIso_naturality C S)

/-- `Stage`-side component isomorphism, lifted through the full subcategory. -/
noncomputable def counitAppStageIso (S : Stage C 1) :
    ((stageOneEval C ⋙ stageOne C).obj S) ≅ S :=
  ObjectProperty.isoMk _ (counitUnderlyingIso C S)

/-- Evaluation followed by the canonical stage is the identity on maps at
diagonals, with explicit transports. -/
private theorem stageOneEval_map_diag {S T : Stage C 1} (f : S ⟶ T)
    (i : Fin 2) :
    eqToHom (stageOne_obj_eq_zero_of_diag C ((stageOneEval C).obj S) rfl).symm ≫
        ((((stageOneEval C ⋙ stageOne C).map f).hom.app (diag i))) ≫
        eqToHom (stageOne_obj_eq_zero_of_diag C ((stageOneEval C).obj T) rfl) =
      𝟙 (0 : C) := by
  have heval : (stageOneEval C).map f = f.hom.app (interval (0 : Fin 2) 1 (by decide)) :=
    rfl
  have hcomp : ((((stageOneEval C ⋙ stageOne C).map f).hom.app (diag i))) =
      (((stageOne C).map ((stageOneEval C).map f)).hom.app (diag i)) := rfl
  rw [hcomp, heval]
  exact stageOne_map_diag _ _ i

/-- Naturality of the `Stage`-side counit in the stage argument. -/
theorem counit_naturality {S T : Stage C 1} (f : S ⟶ T) :
    ((stageOneEval C ⋙ stageOne C).map f) ≫ (counitAppStageIso C T).hom =
      (counitAppStageIso C S).hom ≫ f := by
  apply ObjectProperty.hom_ext
  ext A
  classical
  by_cases ha : A.left = A.right
  · have hEq : ((((stageOneEval C ⋙ stageOne C).obj S).obj.obj A)) = (0 : C) :=
        stageOne_obj_eq_zero_of_diag C _ ha
    have hLs : IsZero (((((stageOneEval C ⋙ stageOne C).obj S).obj.obj A))) := by
      rw [hEq]
      exact isZero_zero C
    exact hLs.eq_of_src _ _
  · have hA : A = interval (0 : Fin 2) 1 (by decide) :=
      ar1_eq_interval01_of_ne ha
    subst hA
    have hmap : ((((stageOneEval C ⋙ stageOne C).map f).hom.app
        (interval (0 : Fin 2) 1 (by decide)))) =
        f.hom.app (interval (0 : Fin 2) 1 (by decide)) := by
      have heval : (stageOneEval C).map f =
          f.hom.app (interval (0 : Fin 2) 1 (by decide)) := rfl
      rw [show ((((stageOneEval C ⋙ stageOne C).map f).hom.app _)) =
        (((stageOne C).map ((stageOneEval C).map f)).hom.app _) from rfl]
      rw [heval]
      exact stageOne_map_interval_zero_one C _
    simp only [counitAppStageIso, counitUnderlyingIso,
      ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app]
    rw [hmap]
    change f.hom.app (interval (0 : Fin 2) 1 (by decide)) ≫
        eqToHom (rfl : T.obj.obj (interval (0 : Fin 2) 1 (by decide)) =
          T.obj.obj (interval (0 : Fin 2) 1 (by decide))) =
        eqToHom (rfl : S.obj.obj (interval (0 : Fin 2) 1 (by decide)) =
          S.obj.obj (interval (0 : Fin 2) 1 (by decide))) ≫
        f.hom.app (interval (0 : Fin 2) 1 (by decide))
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- `Stage`-side counit: staging the evaluation recovers the stage. -/
noncomputable def stageOneEvalCounit :
    stageOneEval C ⋙ stageOne C ≅ 𝟭 (Stage C 1) :=
  NatIso.ofComponents (counitAppStageIso C) (fun f => counit_naturality C f)

/-- Categorical degree-one equivalence `C ≌ Stage C 1`. -/
noncomputable def stageOneEquivalence : C ≌ Stage C 1 :=
  CategoryTheory.Equivalence.mk (stageOne C) (stageOneEval C)
    (stageOneEvalUnit C) (stageOneEvalCounit C)

/-- Forward projection of the degree-one equivalence. -/
@[simp]
theorem stageOneEquivalence_functor :
    (stageOneEquivalence C).functor = stageOne C :=
  rfl

/-- Inverse projection of the degree-one equivalence. -/
@[simp]
theorem stageOneEquivalence_inverse :
    (stageOneEquivalence C).inverse = stageOneEval C :=
  rfl

end CategoryTheory.Waldhausen.SConstruction
