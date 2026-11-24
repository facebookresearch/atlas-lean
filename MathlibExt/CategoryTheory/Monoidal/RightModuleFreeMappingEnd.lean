/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEnd
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeCoefficient
public import Mathlib.CategoryTheory.HomCongr

/-!
# The mapping equalizer out of an actual free right module

Generator evaluation and the original parameterized free extension identify
the full right-module mapping equalizer with the ambient internal Hom.
The scalar monoid need not be commutative. All coefficient parameters and
both original source and target actions are retained.
-/

@[expose] public section

set_option autoImplicit false
-- The original free carrier is constructed through the monoidal opposite.
-- Normalize its class endpoints when reading back actual carrier maps.
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.CommutativeModuleConversion (RightModule)
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.RightModuleMappingEnd

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasEqualizers C]
  (R : C) [MonObj R]

omit [MonoidalClosed C] [HasEqualizers C] in
-- This is the actual permutation needed to compare coefficient linearity
-- with the two original right-action arrows.
@[reassoc]
private theorem parameter_action_crossing (A B P : C) :
    ((β_ A B).hom ▷ P) ≫ (α_ B A P).hom ≫ (β_ B (A ⊗ P)).hom =
      (β_ (A ⊗ B) P).hom ≫ (α_ P A B).inv ≫ ((β_ P A).hom ▷ B) := by
  rw [braiding_tensor_right_hom, braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    ← comp_whiskerRight, SymmetricCategory.symmetry, id_whiskerRight,
    Category.id_comp, Category.comp_id]

omit [HasEqualizers C] in
private theorem condition_uncurry (M N : RightModule R) (P : C)
    (q : P ⟶ ambient R M N) :
    (q ≫ sourceActionMap R M N = q ≫ targetActionMap R M N) ↔
      (M.action ▷ P) ≫ MonoidalClosed.uncurry q =
        ((β_ M.X R).hom ▷ P) ≫ (α_ R M.X P).hom ≫
          (R ◁ MonoidalClosed.uncurry q) ≫ (β_ R N.X).hom ≫ N.action := by
  have hs : MonoidalClosed.uncurry (q ≫ sourceActionMap R M N) =
      (M.action ▷ P) ≫ MonoidalClosed.uncurry q := by
    rw [sourceActionMap, MonoidalClosed.uncurry_pre_app]
  have ht : MonoidalClosed.uncurry (q ≫ targetActionMap R M N) =
      ((β_ M.X R).hom ▷ P) ≫ (α_ R M.X P).hom ≫
        (R ◁ MonoidalClosed.uncurry q) ≫ (β_ R N.X).hom ≫ N.action := by
    rw [targetActionMap, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_curry]
    rw [whisker_exchange_assoc, associator_naturality_right_assoc,
      ← whiskerLeft_comp_assoc]
    rfl
  constructor
  · intro h
    exact hs.symm.trans ((congrArg MonoidalClosed.uncurry h).trans ht)
  · intro h
    apply MonoidalClosed.uncurry_injective
    exact hs.trans (h.trans ht.symm)

omit [HasEqualizers C] in
theorem condition_coefficient_iff (M N : RightModule R) (P : C)
    (q : P ⟶ ambient R M N) :
    (q ≫ sourceActionMap R M N = q ≫ targetActionMap R M N) ↔
      (RightModuleFree.coefficientTensor R P M).action ≫
          ((β_ P M.X).hom ≫ MonoidalClosed.uncurry q) =
        (((β_ P M.X).hom ≫ MonoidalClosed.uncurry q) ▷ R) ≫ N.action := by
  let g : M.X ⊗ P ⟶ N.X := MonoidalClosed.uncurry q
  let t : P ⊗ M.X ⟶ N.X := (β_ P M.X).hom ≫ g
  let a : (M.X ⊗ R) ⊗ P ⟶ (P ⊗ M.X) ⊗ R :=
    (β_ (M.X ⊗ R) P).hom ≫ (α_ P M.X R).inv
  have ha : Epi a := by dsimp only [a]; infer_instance
  have hs : a ≫ (RightModuleFree.coefficientTensor R P M).action ≫ t =
      (M.action ▷ P) ≫ g := by
    simp only [a, t, RightModuleFree.coefficientTensor_action, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [braiding_naturality_right_assoc P M.action]
    simp only [SymmetricCategory.symmetry_assoc]
  have ht : a ≫ (t ▷ R) ≫ N.action =
      ((β_ M.X R).hom ▷ P) ≫ (α_ R M.X P).hom ≫
        (R ◁ g) ≫ (β_ R N.X).hom ≫ N.action := by
    simp only [a, t, comp_whiskerRight, Category.assoc]
    rw [← parameter_action_crossing_assoc M.X R P]
    rw [← braiding_naturality_right_assoc R g]
  change _ ↔ (RightModuleFree.coefficientTensor R P M).action ≫ t =
    (t ▷ R) ≫ N.action
  constructor
  · intro h
    apply (cancel_epi a).1
    exact hs.trans (((condition_uncurry R M N P q).mp h).trans ht.symm)
  · intro h
    apply (condition_uncurry R M N P q).mpr
    exact hs.symm.trans ((congrArg (fun k => a ≫ k) h).trans ht)

/-- A full source-compatible family is an actual map from the existing
coefficient tensor, through the original symmetry. -/
def coefficientFamilyToModule (M N : RightModule R) (P : C)
    (q : Family R M N P) : RightModuleFree.coefficientTensor R P M ⟶ N :=
  Mod.Hom.mk' ((β_ P M.X).hom ≫ MonoidalClosed.uncurry q.app)
    ((condition_coefficient_iff R M N P q.app).mp q.condition)

/-- An actual coefficient-tensor module map gives its complete original
source-action-compatible family. -/
def coefficientModuleToFamily (M N : RightModule R) (P : C)
    (f : RightModuleFree.coefficientTensor R P M ⟶ N) : Family R M N P where
  app := MonoidalClosed.curry ((β_ M.X P).hom ≫ f.hom)
  condition := by
    apply (condition_coefficient_iff R M N P _).mpr
    have h : (β_ P M.X).hom ≫
        MonoidalClosed.uncurry (MonoidalClosed.curry ((β_ M.X P).hom ≫ f.hom)) =
        f.hom := by
      rw [MonoidalClosed.uncurry_curry, ← Category.assoc,
        SymmetricCategory.symmetry, Category.id_comp]
    rw [h]
    exact CommutativeModuleConversion.RightModule.comm f

omit [HasEqualizers C] in
theorem coefficientFamilyToModule_toFamily (M N : RightModule R) (P : C)
    (f : RightModuleFree.coefficientTensor R P M ⟶ N) :
    coefficientFamilyToModule R M N P (coefficientModuleToFamily R M N P f) = f := by
  apply Mod.hom_ext
  change (β_ P M.X).hom ≫
    MonoidalClosed.uncurry (MonoidalClosed.curry ((β_ M.X P).hom ≫ f.hom)) = f.hom
  rw [MonoidalClosed.uncurry_curry, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp]

omit [HasEqualizers C] in
theorem coefficientModuleToFamily_toModule (M N : RightModule R) (P : C)
    (q : Family R M N P) :
    coefficientModuleToFamily R M N P (coefficientFamilyToModule R M N P q) = q := by
  apply Family.ext
  change MonoidalClosed.curry
    ((β_ M.X P).hom ≫ ((β_ P M.X).hom ≫ MonoidalClosed.uncurry q.app)) = q.app
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
    MonoidalClosed.curry_uncurry]

def coefficientFamilyEquiv (M N : RightModule R) (P : C) :
    Family R M N P ≃ (RightModuleFree.coefficientTensor R P M ⟶ N) where
  toFun := coefficientFamilyToModule R M N P
  invFun := coefficientModuleToFamily R M N P
  left_inv := coefficientModuleToFamily_toModule R M N P
  right_inv := coefficientFamilyToModule_toFamily R M N P

/-- The full parameterized correspondence uses the original equalizer,
coefficient-free comparison, free adjunction and ambient closed adjunction. -/
def freeSourceParameterEquiv (X : C) (N : RightModule R) (P : C) :
    (P ⟶ Hom R (RightModuleFree.freeObject R X) N) ≃ (P ⟶ (ihom X).obj N.X) :=
  (parameterEquiv R (RightModuleFree.freeObject R X) N P).trans
    ((coefficientFamilyEquiv R (RightModuleFree.freeObject R X) N P).trans
      ((Iso.homCongr (RightModuleFree.coefficientFreeIso R P X) (Iso.refl N)).trans
        ((RightModuleFree.freeHomEquiv R (P ⊗ X) N).trans
          ((Iso.homCongr (β_ P X) (Iso.refl N.X)).trans
            ((ihom.adjunction X).homEquiv P N.X)))))

/-- Restrict the entire original mapping family along the actual free generator. -/
def freeSourceForward (X : C) (N : RightModule R) :
    Hom R (RightModuleFree.freeObject R X) N ⟶ (ihom X).obj N.X :=
  ι R (RightModuleFree.freeObject R X) N ≫
    (MonoidalClosed.pre (RightModuleFree.freeGenerator R X)).app N.X

/-- The original free extension after its actual coefficient-free comparison. -/
def freeSourceExtensionModule (X P : C) (N : RightModule R) (q : X ⊗ P ⟶ N.X) :
    RightModuleFree.coefficientTensor R P (RightModuleFree.freeObject R X) ⟶ N :=
  (RightModuleFree.coefficientFreeIso R P X).hom ≫
    RightModuleFree.extendFree R (P ⊗ X) N ((β_ P X).hom ≫ q)

/-- The whole free extension retains every coefficient, in the original
free-carrier then parameter order. -/
def freeSourceExtension (X P : C) (N : RightModule R) (q : X ⊗ P ⟶ N.X) :
    (RightModuleFree.freeObject R X).X ⊗ P ⟶ N.X :=
  (β_ (RightModuleFree.freeObject R X).X P).hom ≫
    (freeSourceExtensionModule R X P N q).hom

/-- The parameterized extension gives its actual full source-balanced family. -/
def freeSourceExtensionFamily (X P : C) (N : RightModule R) (q : X ⊗ P ⟶ N.X) :
    Family R (RightModuleFree.freeObject R X) N P :=
  coefficientModuleToFamily R (RightModuleFree.freeObject R X) N P
    (freeSourceExtensionModule R X P N q)

omit [HasEqualizers C] in
/-- The original balanced family has the transpose of the whole extension as component. -/
theorem freeSourceExtensionFamily_app (X P : C) (N : RightModule R)
    (q : X ⊗ P ⟶ N.X) :
    (freeSourceExtensionFamily R X P N q).app =
      MonoidalClosed.curry (freeSourceExtension R X P N q) := rfl

/-- The full correspondence restricts every entire family along the actual free generator. -/
theorem freeSourceParameterEquiv_apply (X : C) (N : RightModule R) (P : C)
    (p : P ⟶ Hom R (RightModuleFree.freeObject R X) N) :
    freeSourceParameterEquiv R X N P p = p ≫ freeSourceForward R X N := by
  simp only [freeSourceParameterEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]
  let f : RightModuleFree.freeObject R (P ⊗ X) ⟶ N :=
    (RightModuleFree.coefficientFreeIso R P X).inv ≫
      coefficientFamilyToModule R (RightModuleFree.freeObject R X) N P
        (toFamily R (RightModuleFree.freeObject R X) N p)
  change MonoidalClosed.curry
    ((β_ P X).inv ≫ RightModuleFree.freeHomEquiv R (P ⊗ X) N f) = _
  have hf : RightModuleFree.freeHomEquiv R (P ⊗ X) N f =
      RightModuleFree.freeGenerator R (P ⊗ X) ≫ f.hom :=
    congrFun (RightModuleFree.freeHomEquiv_toFun R (P ⊗ X) N) f
  rw [hf]
  simp only [f, Mod.comp_hom', coefficientFamilyToModule, toFamily]
  have hg : RightModuleFree.freeGenerator R (P ⊗ X) ≫
      (RightModuleFree.coefficientFreeIso R P X).inv.hom =
        P ◁ RightModuleFree.freeGenerator R X :=
    RightModuleFree.freeGenerator_associator R P X
  change MonoidalClosed.curry
      ((β_ P X).inv ≫
        (RightModuleFree.freeGenerator R (P ⊗ X) ≫
          (RightModuleFree.coefficientFreeIso R P X).inv.hom ≫
            (β_ P (RightModuleFree.freeObject R X).X).hom ≫
            MonoidalClosed.uncurry
              (p ≫ ι R (RightModuleFree.freeObject R X) N))) =
    p ≫ freeSourceForward R X N
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry]
  conv_rhs => rw [freeSourceForward, ← Category.assoc, MonoidalClosed.uncurry_pre_app]
  slice_lhs 2 3 => rw [hg]
  rw [braiding_naturality_right]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The inverse correspondence lifts the actual whole parameterized extension family. -/
@[reassoc]
theorem freeSourceParameterEquiv_symm_ι (X : C) (N : RightModule R) (P : C)
    (q : P ⟶ (ihom X).obj N.X) :
    (freeSourceParameterEquiv R X N P).symm q ≫
        ι R (RightModuleFree.freeObject R X) N =
      MonoidalClosed.curry (freeSourceExtension R X P N (MonoidalClosed.uncurry q)) := by
  simp only [freeSourceParameterEquiv, Equiv.symm_trans_apply, Iso.homCongr_symm,
    Iso.homCongr_apply, Iso.symm_inv, Iso.refl_symm, Iso.refl_hom, Category.comp_id]
  change lift R (RightModuleFree.freeObject R X) N
      (coefficientModuleToFamily R (RightModuleFree.freeObject R X) N P
        (freeSourceExtensionModule R X P N (MonoidalClosed.uncurry q))) ≫
        ι R (RightModuleFree.freeObject R X) N = _
  rw [lift_ι]
  rfl

/-- Every inverse parameter map is the literal original equalizer lift. -/
theorem freeSourceParameterEquiv_symm_eq_lift (X : C) (N : RightModule R) (P : C)
    (q : P ⟶ (ihom X).obj N.X) :
    (freeSourceParameterEquiv R X N P).symm q =
      lift R (RightModuleFree.freeObject R X) N
        (freeSourceExtensionFamily R X P N (MonoidalClosed.uncurry q)) := by
  apply hom_ext R (RightModuleFree.freeObject R X) N
  rw [freeSourceParameterEquiv_symm_ι, lift_ι, freeSourceExtensionFamily_app]

omit [HasEqualizers C] in
/-- The full parameterized extension satisfies the original complete right-action equation. -/
theorem freeSourceExtension_action (X P : C) (N : RightModule R)
    (q : X ⊗ P ⟶ N.X) :
    ((RightModuleFree.freeObject R X).action ▷ P) ≫ freeSourceExtension R X P N q =
      ((β_ (RightModuleFree.freeObject R X).X R).hom ▷ P) ≫
        (α_ R (RightModuleFree.freeObject R X).X P).hom ≫
          (R ◁ freeSourceExtension R X P N q) ≫ (β_ R N.X).hom ≫ N.action := by
  have h := (condition_uncurry R (RightModuleFree.freeObject R X) N P
    (freeSourceExtensionFamily R X P N q).app).mp
      (freeSourceExtensionFamily R X P N q).condition
  rw [freeSourceExtensionFamily_app, MonoidalClosed.uncurry_curry] at h
  exact h

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The extension keeps exactly the original coefficient/right-factor reassociation,
evaluation arrow and unchanged target action. -/
theorem freeSourceExtension_reassociation (X P : C) (N : RightModule R)
    (q : X ⊗ P ⟶ N.X) :
    freeSourceExtension R X P N q =
      (α_ X R P).hom ≫ (X ◁ (β_ R P).hom) ≫ (α_ X P R).inv ≫
        (q ▷ R) ≫ N.action := by
  simp only [freeSourceExtension, freeSourceExtensionModule, Mod.comp_hom',
    RightModuleFree.coefficientFreeIso_hom, RightModuleFree.extendFree_hom_apply,
    comp_whiskerRight, Category.assoc]
  change (β_ (X ⊗ R) P).hom ≫
      (α_ P X R).inv ≫ ((β_ P X).hom ▷ R) ≫ (q ▷ R) ≫ N.action = _
  rw [braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    SymmetricCategory.symmetry_assoc]

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The original free extension recovers every entire coefficient arrow at its generator. -/
@[reassoc]
theorem freeSourceExtension_generator (X P : C) (N : RightModule R)
    (q : X ⊗ P ⟶ N.X) :
    (RightModuleFree.freeGenerator R X ▷ P) ≫ freeSourceExtension R X P N q = q := by
  have h : (P ◁ RightModuleFree.freeGenerator R X) ≫
      (freeSourceExtensionModule R X P N q).hom = (β_ P X).hom ≫ q := by
    rw [← RightModuleFree.freeGenerator_associator R P X]
    simp only [freeSourceExtensionModule, Mod.comp_hom',
      RightModuleFree.coefficientFreeIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact RightModuleFree.freeGenerator_extend R (P ⊗ X) N ((β_ P X).hom ≫ q)
  rw [freeSourceExtension, ← Category.assoc, braiding_naturality_left,
    Category.assoc, h, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The whole extension uses the selected original free-adjunction counit. -/
theorem freeSourceExtensionModule_counit (X P : C) (N : RightModule R)
    (q : X ⊗ P ⟶ N.X) :
    freeSourceExtensionModule R X P N q =
      (RightModuleFree.coefficientFreeIso R P X).hom ≫
        RightModuleFree.freeMap R ((β_ P X).hom ≫ q) ≫ RightModuleFree.actionCounit R N := by
  exact congrArg (fun f => (RightModuleFree.coefficientFreeIso R P X).hom ≫ f)
    ((RightModuleFree.adjunction R).homEquiv_counit (P ⊗ X) N ((β_ P X).hom ≫ q))

/-- The full original generator restriction evaluates before the actual equalizer evaluation. -/
theorem freeSourceForward_evaluation (X : C) (N : RightModule R) :
    MonoidalClosed.uncurry (freeSourceForward R X N) =
      (RightModuleFree.freeGenerator R X ▷ Hom R (RightModuleFree.freeObject R X) N) ≫
        evaluation R (RightModuleFree.freeObject R X) N := by
  exact MonoidalClosed.uncurry_pre_app N.X
    (ι R (RightModuleFree.freeObject R X) N) (RightModuleFree.freeGenerator R X)

/-- The forward map uses the selected actual free-adjunction unit. -/
theorem freeSourceForward_unit (X : C) (N : RightModule R) :
    freeSourceForward R X N = ι R (RightModuleFree.freeObject R X) N ≫
      (MonoidalClosed.pre ((RightModuleFree.adjunction R).unit.app X)).app N.X := by
  rw [RightModuleFree.adjunction_unit]
  rfl

/-- The inverse is the original equalizer lift of the full free extension of evaluation. -/
def freeSourceBackward (X : C) (N : RightModule R) :
    (ihom X).obj N.X ⟶ Hom R (RightModuleFree.freeObject R X) N :=
  lift R (RightModuleFree.freeObject R X) N
    (freeSourceExtensionFamily R X ((ihom X).obj N.X) N ((ihom.ev X).app N.X))

/-- The whole inverse map is the inverse parameter correspondence at the identity coefficient. -/
theorem freeSourceBackward_eq_parameter (X : C) (N : RightModule R) :
    freeSourceBackward R X N =
      (freeSourceParameterEquiv R X N ((ihom X).obj N.X)).symm (𝟙 _) := by
  rw [freeSourceParameterEquiv_symm_eq_lift, MonoidalClosed.uncurry_id_eq_ev]
  rfl

/-- The inverse retains the complete original extension transpose under the equalizer inclusion. -/
@[reassoc]
theorem freeSourceBackward_ι (X : C) (N : RightModule R) :
    freeSourceBackward R X N ≫ ι R (RightModuleFree.freeObject R X) N =
      MonoidalClosed.curry
        (freeSourceExtension R X ((ihom X).obj N.X) N ((ihom.ev X).app N.X)) := by
  rw [freeSourceBackward, lift_ι, freeSourceExtensionFamily_app]

/-- Evaluating the whole inverse gives the original parameterized free extension. -/
theorem freeSourceBackward_evaluation (X : C) (N : RightModule R) :
    ((RightModuleFree.freeObject R X).X ◁ freeSourceBackward R X N) ≫
        evaluation R (RightModuleFree.freeObject R X) N =
      freeSourceExtension R X ((ihom X).obj N.X) N ((ihom.ev X).app N.X) := by
  rw [evaluation, ← MonoidalClosed.uncurry_natural_left, freeSourceBackward_ι,
    MonoidalClosed.uncurry_curry]

/-- Free extension followed by generator restriction recovers the entire ambient internal Hom. -/
theorem freeSourceBackward_forward (X : C) (N : RightModule R) :
    freeSourceBackward R X N ≫ freeSourceForward R X N = 𝟙 _ := by
  rw [← freeSourceParameterEquiv_apply, freeSourceBackward_eq_parameter]
  exact (freeSourceParameterEquiv R X N ((ihom X).obj N.X)).apply_symm_apply (𝟙 _)

/-- Generator restriction followed by free extension recovers the entire original mapping end. -/
theorem freeSourceForward_backward (X : C) (N : RightModule R) :
    freeSourceForward R X N ≫ freeSourceBackward R X N = 𝟙 _ := by
  apply (freeSourceParameterEquiv R X N (Hom R (RightModuleFree.freeObject R X) N)).injective
  rw [freeSourceParameterEquiv_apply, Category.assoc, freeSourceBackward_forward,
    Category.comp_id, freeSourceParameterEquiv_apply, Category.id_comp]

/-- The original free-source mapping equalizer is the complete coefficient internal Hom,
without any commutativity assumption on the scalar monoid. -/
def freeSourceIso (X : C) (N : RightModule R) :
    Hom R (RightModuleFree.freeObject R X) N ≅ (ihom X).obj N.X where
  hom := freeSourceForward R X N
  inv := freeSourceBackward R X N
  hom_inv_id := freeSourceForward_backward R X N
  inv_hom_id := freeSourceBackward_forward R X N

/-- The actual whole forward is generator restriction after the original inclusion. -/
theorem freeSourceIso_hom (X : C) (N : RightModule R) :
    (freeSourceIso R X N).hom = ι R (RightModuleFree.freeObject R X) N ≫
      (MonoidalClosed.pre (RightModuleFree.freeGenerator R X)).app N.X := rfl

/-- The actual whole inverse retains the full original parameterized extension projection. -/
@[reassoc]
theorem freeSourceIso_inv_ι (X : C) (N : RightModule R) :
    (freeSourceIso R X N).inv ≫ ι R (RightModuleFree.freeObject R X) N =
      MonoidalClosed.curry
        (freeSourceExtension R X ((ihom X).obj N.X) N ((ihom.ev X).app N.X)) :=
  freeSourceBackward_ι R X N

/-- Every entire inverse coefficient family is composition with the actual inverse isomorphism. -/
theorem freeSourceParameterEquiv_symm_apply (X : C) (N : RightModule R) (P : C)
    (q : P ⟶ (ihom X).obj N.X) :
    (freeSourceParameterEquiv R X N P).symm q = q ≫ freeSourceBackward R X N := by
  apply (freeSourceParameterEquiv R X N P).injective
  rw [Equiv.apply_symm_apply, freeSourceParameterEquiv_apply, Category.assoc,
    freeSourceBackward_forward, Category.comp_id]

/-- Restriction retains every whole source-module arrow, through its actual generator value. -/
@[reassoc]
theorem freeSourceForward_pre {X X' : C}
    (f : RightModuleFree.freeObject R X' ⟶ RightModuleFree.freeObject R X)
    (N : RightModule R) :
    pre R f N ≫ freeSourceForward R X' N =
      ι R (RightModuleFree.freeObject R X) N ≫
        (MonoidalClosed.pre (RightModuleFree.freeGenerator R X' ≫ f.hom)).app N.X := by
  rw [freeSourceForward, ← Category.assoc, pre_ι, Category.assoc,
    ← NatTrans.comp_app, ← MonoidalClosed.pre_map]

/-- The whole forward is natural in every original source-object arrow. -/
@[reassoc]
theorem freeSourceForward_naturality_source {X X' : C} (f : X' ⟶ X)
    (N : RightModule R) :
    pre R (RightModuleFree.freeMap R f) N ≫ freeSourceForward R X' N =
      freeSourceForward R X N ≫ (MonoidalClosed.pre f).app N.X := by
  have h : RightModuleFree.freeGenerator R X' ≫ (RightModuleFree.freeMap R f).hom =
      f ≫ RightModuleFree.freeGenerator R X :=
    RightModuleFree.freeGenerator_naturality R f
  rw [freeSourceForward_pre, h, MonoidalClosed.pre_map, NatTrans.comp_app,
    freeSourceForward, Category.assoc]

/-- The whole forward is natural in every original target-module arrow. -/
@[reassoc]
theorem freeSourceForward_naturality_target (X : C) {N N' : RightModule R}
    (g : N ⟶ N') :
    post R (RightModuleFree.freeObject R X) g ≫ freeSourceForward R X N' =
      freeSourceForward R X N ≫ (ihom X).map g.hom := by
  rw [freeSourceForward, ← Category.assoc, post_ι, Category.assoc,
    (MonoidalClosed.pre (RightModuleFree.freeGenerator R X)).naturality g.hom]
  rw [freeSourceForward, Category.assoc]

/-- The whole inverse is natural in every original source-object arrow. -/
@[reassoc]
theorem freeSourceBackward_naturality_source {X X' : C} (f : X' ⟶ X)
    (N : RightModule R) :
    (MonoidalClosed.pre f).app N.X ≫ freeSourceBackward R X' N =
      freeSourceBackward R X N ≫ pre R (RightModuleFree.freeMap R f) N := by
  apply (freeSourceParameterEquiv R X' N ((ihom X).obj N.X)).injective
  rw [freeSourceParameterEquiv_apply, Category.assoc, freeSourceBackward_forward,
    Category.comp_id, freeSourceParameterEquiv_apply, Category.assoc,
    freeSourceForward_naturality_source, ← Category.assoc,
    freeSourceBackward_forward, Category.id_comp]

/-- The whole inverse is natural in every original target-module arrow. -/
@[reassoc]
theorem freeSourceBackward_naturality_target (X : C) {N N' : RightModule R}
    (g : N ⟶ N') :
    (ihom X).map g.hom ≫ freeSourceBackward R X N' =
      freeSourceBackward R X N ≫ post R (RightModuleFree.freeObject R X) g := by
  apply (freeSourceParameterEquiv R X N' ((ihom X).obj N.X)).injective
  rw [freeSourceParameterEquiv_apply, Category.assoc, freeSourceBackward_forward,
    Category.comp_id, freeSourceParameterEquiv_apply, Category.assoc,
    freeSourceForward_naturality_target, ← Category.assoc,
    freeSourceBackward_forward, Category.id_comp]

/-- Every whole coefficient arrow commutes with the forward parameter correspondence. -/
theorem freeSourceParameterEquiv_naturality_parameter (X : C) (N : RightModule R)
    {P Q : C} (f : Q ⟶ P) (p : P ⟶ Hom R (RightModuleFree.freeObject R X) N) :
    freeSourceParameterEquiv R X N Q (f ≫ p) =
      f ≫ freeSourceParameterEquiv R X N P p := by
  rw [freeSourceParameterEquiv_apply, freeSourceParameterEquiv_apply, Category.assoc]

/-- Every whole coefficient arrow commutes with the inverse parameter correspondence. -/
theorem freeSourceParameterEquiv_symm_naturality_parameter (X : C) (N : RightModule R)
    {P Q : C} (f : Q ⟶ P) (q : P ⟶ (ihom X).obj N.X) :
    (freeSourceParameterEquiv R X N Q).symm (f ≫ q) =
      f ≫ (freeSourceParameterEquiv R X N P).symm q := by
  rw [freeSourceParameterEquiv_symm_apply, freeSourceParameterEquiv_symm_apply,
    Category.assoc]

/-- The forward correspondence retains every complete source-object map at every coefficient. -/
theorem freeSourceParameterEquiv_naturality_source {X X' : C} (f : X' ⟶ X)
    (N : RightModule R) (P : C) (p : P ⟶ Hom R (RightModuleFree.freeObject R X) N) :
    freeSourceParameterEquiv R X' N P (p ≫ pre R (RightModuleFree.freeMap R f) N) =
      freeSourceParameterEquiv R X N P p ≫ (MonoidalClosed.pre f).app N.X := by
  rw [freeSourceParameterEquiv_apply, Category.assoc, freeSourceForward_naturality_source,
    freeSourceParameterEquiv_apply, Category.assoc]

/-- The inverse correspondence retains every complete source-object map at every coefficient. -/
theorem freeSourceParameterEquiv_symm_naturality_source {X X' : C} (f : X' ⟶ X)
    (N : RightModule R) (P : C) (q : P ⟶ (ihom X).obj N.X) :
    (freeSourceParameterEquiv R X' N P).symm (q ≫ (MonoidalClosed.pre f).app N.X) =
      (freeSourceParameterEquiv R X N P).symm q ≫ pre R (RightModuleFree.freeMap R f) N := by
  rw [freeSourceParameterEquiv_symm_apply, Category.assoc,
    freeSourceBackward_naturality_source, freeSourceParameterEquiv_symm_apply,
    Category.assoc]

/-- The forward correspondence retains every complete target-module map at every coefficient. -/
theorem freeSourceParameterEquiv_naturality_target (X : C) {N N' : RightModule R}
    (g : N ⟶ N') (P : C) (p : P ⟶ Hom R (RightModuleFree.freeObject R X) N) :
    freeSourceParameterEquiv R X N' P (p ≫ post R (RightModuleFree.freeObject R X) g) =
      freeSourceParameterEquiv R X N P p ≫ (ihom X).map g.hom := by
  rw [freeSourceParameterEquiv_apply, Category.assoc, freeSourceForward_naturality_target,
    freeSourceParameterEquiv_apply, Category.assoc]

/-- The inverse correspondence retains every complete target-module map at every coefficient. -/
theorem freeSourceParameterEquiv_symm_naturality_target (X : C) {N N' : RightModule R}
    (g : N ⟶ N') (P : C) (q : P ⟶ (ihom X).obj N.X) :
    (freeSourceParameterEquiv R X N' P).symm (q ≫ (ihom X).map g.hom) =
      (freeSourceParameterEquiv R X N P).symm q ≫ post R (RightModuleFree.freeObject R X) g := by
  rw [freeSourceParameterEquiv_symm_apply, Category.assoc,
    freeSourceBackward_naturality_target, freeSourceParameterEquiv_symm_apply,
    Category.assoc]

/-- The whole extension transpose is exactly the inverse isomorphism's original ambient family. -/
theorem freeSourceExtension_curry (X P : C) (N : RightModule R) (q : X ⊗ P ⟶ N.X) :
    MonoidalClosed.curry (freeSourceExtension R X P N q) =
      (MonoidalClosed.curry q ≫ freeSourceBackward R X N) ≫
        ι R (RightModuleFree.freeObject R X) N := by
  have h := freeSourceParameterEquiv_symm_ι R X N P (MonoidalClosed.curry q)
  rw [MonoidalClosed.uncurry_curry, freeSourceParameterEquiv_symm_apply] at h
  exact h.symm

/-- The complete extension commutes with every original coefficient arrow. -/
theorem freeSourceExtension_naturality_parameter (X : C) {P Q : C} (f : Q ⟶ P)
    (N : RightModule R) (q : X ⊗ P ⟶ N.X) :
    ((RightModuleFree.freeObject R X).X ◁ f) ≫ freeSourceExtension R X P N q =
      freeSourceExtension R X Q N ((X ◁ f) ≫ q) := by
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_natural_left, freeSourceExtension_curry,
    freeSourceExtension_curry, MonoidalClosed.curry_natural_left]
  simp only [Category.assoc]

/-- The complete extension commutes with every original source-object arrow. -/
theorem freeSourceExtension_naturality_source {X X' : C} (f : X' ⟶ X)
    (P : C) (N : RightModule R) (q : X ⊗ P ⟶ N.X) :
    ((RightModuleFree.freeMap R f).hom ▷ P) ≫ freeSourceExtension R X P N q =
      freeSourceExtension R X' P N ((f ▷ P) ≫ q) := by
  apply MonoidalClosed.curry_injective
  rw [← MonoidalClosed.curry_pre_app, freeSourceExtension_curry,
    freeSourceExtension_curry, ← MonoidalClosed.curry_pre_app]
  simp only [Category.assoc]
  rw [← pre_ι, ← freeSourceBackward_naturality_source_assoc]

/-- The complete extension commutes with every original target-module arrow. -/
theorem freeSourceExtension_naturality_target (X P : C) {N N' : RightModule R}
    (g : N ⟶ N') (q : X ⊗ P ⟶ N.X) :
    freeSourceExtension R X P N q ≫ g.hom = freeSourceExtension R X P N' (q ≫ g.hom) := by
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_natural_right, freeSourceExtension_curry,
    freeSourceExtension_curry, MonoidalClosed.curry_natural_right]
  simp only [Category.assoc]
  rw [← post_ι, ← freeSourceBackward_naturality_target_assoc]

end CategoryTheory.RightModuleMappingEnd
