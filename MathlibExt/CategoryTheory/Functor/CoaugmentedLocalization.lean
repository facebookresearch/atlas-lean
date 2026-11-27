/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Localization.Predicate
public import MathlibExt.CategoryTheory.Functor.CoaugmentedReflection

/-!
# Original coaugmentations on the actual localization at a weak class

The original functor preserves the supplied weak class, and both actual
iterated unit families are weak. The canonical localization construction
then retains the full functor, original-map equations and both Hom functions
of its genuine reflection. No model structure on the localized category,
adjunction, unit-Hom bijection or desired detection law is an argument.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory

namespace CategoryTheory.Functor.CoaugmentedLocalization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) (F : C ⥤ C) (η : 𝟭 C ⟶ F)
variable (hpreserve : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → W (F.map f))

include hpreserve in
/-- The original weak-preserving functor is followed by the same canonical localization. -/
theorem inverts : W.IsInvertedBy (F ⋙ W.Q) :=
  fun _ _ f hf => W.Q_inverts (F.map f) (hpreserve f hf)

/-- The actual canonical path/quotient construction descends the original whole functor. -/
def localizedFunctor : W.Localization ⥤ W.Localization :=
  Localization.Construction.lift (F ⋙ W.Q) (inverts W F hpreserve)

/-- Every descended object is the original functor object in the same localization. -/
theorem localizedFunctor_obj (X : C) :
    (localizedFunctor W F hpreserve).obj (W.Q.obj X) = W.Q.obj (F.obj X) := rfl

/-- Every descended original map is the actual localized original functor map. -/
theorem localizedFunctor_map {X Y : C} (f : X ⟶ Y) :
    (localizedFunctor W F hpreserve).map (W.Q.map f) = W.Q.map (F.map f) := by
  have h := Functor.congr_hom
    (Localization.Construction.fac (F ⋙ W.Q) (inverts W F hpreserve)) f
  change (localizedFunctor W F hpreserve).map (W.Q.map f) =
    (𝟙 (W.Q.obj (F.obj X))) ≫ W.Q.map (F.map f) ≫ (𝟙 (W.Q.obj (F.obj Y))) at h
  simpa only [Category.id_comp, Category.comp_id] using h

/-- The original whole unit is mapped by the same canonical localization. -/
def mappedUnit : W.Q ⟶ F ⋙ W.Q where
  app X := W.Q.map (η.app X)
  naturality {X Y} f := by
    change W.Q.map f ≫ W.Q.map (η.app Y) = W.Q.map (η.app X) ≫ W.Q.map (F.map f)
    rw [← W.Q.map_comp, ← W.Q.map_comp]
    exact W.Q.congr_map (η.naturality f)

/-- The entire unit descends on all localization arrows by the actual universal property. -/
def localizedUnit : 𝟭 W.Localization ⟶ localizedFunctor W F hpreserve := by
  let _ : Localization.Lifting W.Q W W.Q (𝟭 W.Localization) := ⟨W.Q.rightUnitor⟩
  let _ : Localization.Lifting W.Q W (F ⋙ W.Q) (localizedFunctor W F hpreserve) :=
    ⟨eqToIso (Localization.Construction.fac (F ⋙ W.Q) (inverts W F hpreserve))⟩
  exact Localization.liftNatTrans W.Q W W.Q (F ⋙ W.Q) (𝟭 W.Localization)
    (localizedFunctor W F hpreserve) (mappedUnit W F η)

/-- The full descended unit component is the original unit map in the same localization. -/
theorem localizedUnit_app (X : C) :
    (localizedUnit W F η hpreserve).app (W.Q.obj X) = W.Q.map (η.app X) := by
  unfold localizedUnit
  rw [Localization.liftNatTrans_app]
  change (𝟙 (W.Q.obj X)) ≫ W.Q.map (η.app X) ≫
    eqToHom (rfl : W.Q.obj (F.obj X) = W.Q.obj (F.obj X)) = W.Q.map (η.app X)
  rw [eqToHom_refl, Category.id_comp, Category.comp_id]

variable (hunit : ∀ X, W (η.app (F.obj X)))
variable (hmap : ∀ X, W (F.map (η.app X)))

include hunit in
/-- Every actual localized image has its original iterated unit inverted. -/
theorem localizedUnit_obj_isIso (X : W.Localization) :
    IsIso ((localizedUnit W F η hpreserve).app ((localizedFunctor W F hpreserve).obj X)) := by
  rcases X with ⟨⟨X⟩⟩
  change IsIso ((localizedUnit W F η hpreserve).app (W.Q.obj (F.obj X)))
  rw [localizedUnit_app]
  exact W.Q_inverts _ (hunit X)

include hmap in
/-- Every actual descended unit map is inverted by the descended original functor. -/
theorem localizedFunctor_unit_isIso (X : W.Localization) :
    IsIso ((localizedFunctor W F hpreserve).map
      ((localizedUnit W F η hpreserve).app X)) := by
  rcases X with ⟨⟨X⟩⟩
  change IsIso ((localizedFunctor W F hpreserve).map
    ((localizedUnit W F η hpreserve).app (W.Q.obj X)))
  rw [localizedUnit_app]
  change IsIso ((localizedFunctor W F hpreserve).map (W.Q.map (η.app X)))
  rw [localizedFunctor_map]
  exact W.Q_inverts _ (hmap X)

/-- The actual weak unit at a target supplies both full localized Hom functions. -/
def unitHomEquiv (X Z : C) (hZ : W (η.app Z)) :
    (W.Q.obj (F.obj X) ⟶ W.Q.obj Z) ≃ (W.Q.obj X ⟶ W.Q.obj Z) := by
  let _ : IsIso ((localizedUnit W F η hpreserve).app (W.Q.obj Z)) := by
    rw [localizedUnit_app]
    exact W.Q_inverts _ hZ
  exact CoaugmentedReflection.unitHomEquiv (localizedFunctor W F hpreserve)
    (localizedUnit W F η hpreserve)
    (localizedUnit_obj_isIso W F η hpreserve hunit)
    (localizedFunctor_unit_isIso W F η hpreserve hmap) (W.Q.obj X) (W.Q.obj Z)

/-- The entire forward Hom function uses the original unit, not an alternative comparison. -/
theorem unitHomEquiv_apply (X Z : C) (hZ : W (η.app Z))
    (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    unitHomEquiv W F η hpreserve hunit hmap X Z hZ g = W.Q.map (η.app X) ≫ g := by
  change (localizedUnit W F η hpreserve).app (W.Q.obj X) ≫ g = _
  rw [localizedUnit_app]
  rfl

/-- The entire inverse acts on arbitrary localization morphisms and uses the actual inverse unit. -/
theorem unitHomEquiv_symm_apply (X Z : C) (hZ : W (η.app Z))
    (g : W.Q.obj X ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm g =
      (localizedFunctor W F hpreserve).map g ≫
        (Localization.Construction.wIso (η.app Z) hZ).inv := by
  let _ : IsIso ((localizedUnit W F η hpreserve).app (W.Q.obj Z)) := by
    rw [localizedUnit_app]
    exact W.Q_inverts _ hZ
  change (localizedFunctor W F hpreserve).map g ≫
    CategoryTheory.inv ((localizedUnit W F η hpreserve).app (W.Q.obj Z)) = _
  apply congrArg (fun a => (localizedFunctor W F hpreserve).map g ≫ a)
  apply IsIso.inv_eq_of_hom_inv_id
  change (localizedUnit W F η hpreserve).app (W.Q.obj Z) ≫
      (Localization.Construction.wIso (η.app Z) hZ).inv = 𝟙 (W.Q.obj Z)
  rw [localizedUnit_app]
  exact (Localization.Construction.wIso (η.app Z) hZ).hom_inv_id

include hpreserve hunit hmap in
/-- The original unit precomposition function is bijective on the whole localized Hom carrier. -/
theorem precomp_unit_bijective (X Z : C) (hZ : W (η.app Z)) :
    Function.Bijective (fun g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z => W.Q.map (η.app X) ≫ g) := by
  have h := (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).bijective
  change Function.Bijective
    (fun g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z =>
      unitHomEquiv W F η hpreserve hunit hmap X Z hZ g) at h
  simp only [unitHomEquiv_apply] at h
  exact h

variable (P : C → Prop) (himage : ∀ X, P (F.obj X))
variable (hfixed : ∀ Z, P Z → W (η.app Z))

include η hpreserve hunit hmap himage hfixed in
/-- The actual image/test class identifies all original maps inverted after the functor. -/
theorem map_isIso_iff_homtests {X Y : C} (f : X ⟶ Y) :
    IsIso (W.Q.map (F.map f)) ↔
      ∀ Z, P Z → Function.Bijective
        (fun g : W.Q.obj Y ⟶ W.Q.obj Z => W.Q.map f ≫ g) := by
  let P' : W.Localization → Prop := fun Z => P Z.as.obj
  have hI : ∀ X, P' ((localizedFunctor W F hpreserve).obj X) := by
    rintro ⟨⟨X⟩⟩
    exact himage X
  have hF : ∀ Z, P' Z → IsIso ((localizedUnit W F η hpreserve).app Z) := by
    rintro ⟨⟨Z⟩⟩ hZ
    change IsIso ((localizedUnit W F η hpreserve).app (W.Q.obj Z))
    rw [localizedUnit_app]
    exact W.Q_inverts _ (hfixed Z hZ)
  have h := CoaugmentedReflection.map_isIso_iff_fixed_homtests
    (localizedFunctor W F hpreserve) (localizedUnit W F η hpreserve)
    (localizedUnit_obj_isIso W F η hpreserve hunit)
    (localizedFunctor_unit_isIso W F η hpreserve hmap) P' hI hF (W.Q.map f)
  rw [localizedFunctor_map] at h
  apply h.trans
  constructor
  · intro hf Z hZ
    exact hf (W.Q.obj Z) hZ
  · intro hf
    rintro ⟨⟨Z⟩⟩ hZ
    exact hf Z hZ

end CategoryTheory.Functor.CoaugmentedLocalization


namespace CategoryTheory.Functor.CoaugmentedLocalization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) (F : C ⥤ C) (η : 𝟭 C ⟶ F)
variable (hpreserve : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → W (F.map f))
variable (hunit : ∀ X, W (η.app (F.obj X)))
variable (hmap : ∀ X, W (F.map (η.app X)))

/-- Every original source map preserves the complete localized forward Hom function. -/
theorem unitHomEquiv_source {X X' : C} (a : X' ⟶ X) (Z : C) (hZ : W (η.app Z))
    (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    unitHomEquiv W F η hpreserve hunit hmap X' Z hZ (W.Q.map (F.map a) ≫ g) =
      W.Q.map a ≫ unitHomEquiv W F η hpreserve hunit hmap X Z hZ g := by
  rw [unitHomEquiv_apply, unitHomEquiv_apply]
  calc
    W.Q.map (η.app X') ≫ (W.Q.map (F.map a) ≫ g) =
        W.Q.map (η.app X' ≫ F.map a) ≫ g := by rw [W.Q.map_comp, Category.assoc]
    _ = W.Q.map (a ≫ η.app X) ≫ g := by
      congr 2
      exact (η.naturality a).symm
    _ = W.Q.map a ≫ (W.Q.map (η.app X) ≫ g) := by rw [W.Q.map_comp, Category.assoc]

/-- Every original source map preserves the complete localized inverse Hom function. -/
theorem unitHomEquiv_source_symm {X X' : C} (a : X' ⟶ X) (Z : C) (hZ : W (η.app Z))
    (g : W.Q.obj X ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X' Z hZ).symm (W.Q.map a ≫ g) =
      W.Q.map (F.map a) ≫ (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm g := by
  apply (unitHomEquiv W F η hpreserve hunit hmap X' Z hZ).injective
  rw [Equiv.apply_symm_apply, unitHomEquiv_source, Equiv.apply_symm_apply]

/-- Arbitrary target localization morphisms preserve the whole forward function. -/
theorem unitHomEquiv_target (X Z Z' : C) (hZ : W (η.app Z)) (hZ' : W (η.app Z'))
    (b : W.Q.obj Z ⟶ W.Q.obj Z') (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    unitHomEquiv W F η hpreserve hunit hmap X Z' hZ' (g ≫ b) =
      unitHomEquiv W F η hpreserve hunit hmap X Z hZ g ≫ b := by
  rw [unitHomEquiv_apply, unitHomEquiv_apply]
  exact (Category.assoc _ _ _).symm

/-- Arbitrary target localization morphisms preserve the whole inverse function. -/
theorem unitHomEquiv_target_symm (X Z Z' : C) (hZ : W (η.app Z)) (hZ' : W (η.app Z'))
    (b : W.Q.obj Z ⟶ W.Q.obj Z') (g : W.Q.obj X ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X Z' hZ').symm (g ≫ b) =
      (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm g ≫ b := by
  apply (unitHomEquiv W F η hpreserve hunit hmap X Z' hZ').injective
  rw [Equiv.apply_symm_apply,
    unitHomEquiv_target W F η hpreserve hunit hmap X Z Z' hZ hZ',
    Equiv.apply_symm_apply]

end CategoryTheory.Functor.CoaugmentedLocalization


namespace CategoryTheory.Functor.CoaugmentedLocalization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) (F : C ⥤ C) (η : 𝟭 C ⟶ F)
variable (hpreserve : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → W (F.map f))
variable (hunit : ∀ X, W (η.app (F.obj X)))
variable (hmap : ∀ X, W (F.map (η.app X)))

include hunit hmap in
/-- All actual localization unit arrows have their full iterated-unit coherence. -/
theorem localizedFunctor_unit_eq (X : W.Localization) :
    (localizedFunctor W F hpreserve).map ((localizedUnit W F η hpreserve).app X) =
      (localizedUnit W F η hpreserve).app ((localizedFunctor W F hpreserve).obj X) :=
  CoaugmentedReflection.map_unit_eq_unit_obj (localizedFunctor W F hpreserve)
    (localizedUnit W F η hpreserve)
    (localizedUnit_obj_isIso W F η hpreserve hunit)
    (localizedFunctor_unit_isIso W F η hpreserve hmap) X

/-- Arbitrary localization source morphisms retain the complete forward unit-Hom function. -/
theorem unitHomEquiv_source_hom (X X' Z : C)
    (a : W.Q.obj X' ⟶ W.Q.obj X) (hZ : W (η.app Z))
    (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    unitHomEquiv W F η hpreserve hunit hmap X' Z hZ
      ((localizedFunctor W F hpreserve).map a ≫ g) =
      a ≫ unitHomEquiv W F η hpreserve hunit hmap X Z hZ g := by
  rw [unitHomEquiv_apply, unitHomEquiv_apply]
  have h := (localizedUnit W F η hpreserve).naturality a
  change a ≫ (localizedUnit W F η hpreserve).app (W.Q.obj X) =
    (localizedUnit W F η hpreserve).app (W.Q.obj X') ≫
      (localizedFunctor W F hpreserve).map a at h
  rw [localizedUnit_app, localizedUnit_app] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ g) h.symm).trans (Category.assoc _ _ _))

/-- Arbitrary localization source morphisms retain the complete inverse unit-Hom function. -/
theorem unitHomEquiv_source_hom_symm (X X' Z : C)
    (a : W.Q.obj X' ⟶ W.Q.obj X) (hZ : W (η.app Z))
    (g : W.Q.obj X ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X' Z hZ).symm (a ≫ g) =
      (localizedFunctor W F hpreserve).map a ≫
        (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm g := by
  apply (unitHomEquiv W F η hpreserve hunit hmap X' Z hZ).injective
  calc
    unitHomEquiv W F η hpreserve hunit hmap X' Z hZ
        ((unitHomEquiv W F η hpreserve hunit hmap X' Z hZ).symm (a ≫ g)) = a ≫ g :=
      (unitHomEquiv W F η hpreserve hunit hmap X' Z hZ).apply_symm_apply _
    _ = a ≫ unitHomEquiv W F η hpreserve hunit hmap X Z hZ
        ((unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm g) :=
      congrArg (fun b => a ≫ b)
        ((unitHomEquiv W F η hpreserve hunit hmap X Z hZ).apply_symm_apply g).symm
    _ = unitHomEquiv W F η hpreserve hunit hmap X' Z hZ
        ((localizedFunctor W F hpreserve).map a ≫
          (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm g) :=
      (unitHomEquiv_source_hom W F η hpreserve hunit hmap X X' Z a hZ _).symm

/-- The whole localized inverse is uniquely characterized by the original localized unit. -/
theorem unitHomEquiv_characteristic (X Z : C) (hZ : W (η.app Z))
    (f : W.Q.obj X ⟶ W.Q.obj Z) (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm f = g ↔
      W.Q.map (η.app X) ≫ g = f := by
  constructor
  · intro h
    rw [← h]
    exact (unitHomEquiv_apply W F η hpreserve hunit hmap X Z hZ
      ((unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm f)).symm.trans
        ((unitHomEquiv W F η hpreserve hunit hmap X Z hZ).apply_symm_apply f)
  · intro h
    apply (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).injective
    exact ((unitHomEquiv W F η hpreserve hunit hmap X Z hZ).apply_symm_apply f).trans
      ((unitHomEquiv_apply W F η hpreserve hunit hmap X Z hZ g).trans h).symm

include hpreserve hunit hmap in
/-- The original localized unit followed by the full inverse Hom function is the original arrow. -/
theorem unitHomEquiv_right_triangle (X Z : C) (hZ : W (η.app Z))
    (f : W.Q.obj X ⟶ W.Q.obj Z) :
    W.Q.map (η.app X) ≫ ((localizedFunctor W F hpreserve).map f ≫
      (Localization.Construction.wIso (η.app Z) hZ).inv) = f := by
  have h := (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).apply_symm_apply f
  rw [unitHomEquiv_apply, unitHomEquiv_symm_apply] at h
  exact h

include hunit hmap in
/-- The full inverse Hom function returns every original forward localized arrow unchanged. -/
theorem unitHomEquiv_left_triangle (X Z : C) (hZ : W (η.app Z))
    (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    (localizedFunctor W F hpreserve).map (W.Q.map (η.app X) ≫ g) ≫
      (Localization.Construction.wIso (η.app Z) hZ).inv = g := by
  have h := (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm_apply_apply g
  rw [unitHomEquiv_symm_apply, unitHomEquiv_apply] at h
  exact h

end CategoryTheory.Functor.CoaugmentedLocalization
