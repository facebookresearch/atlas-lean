/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Whole closed-power interchange laws

The native currying and braiding isomorphisms are used on the whole objects.
No fibrancy, Segal, completeness, weak equivalence or completion outcome is
assumed. The coefficient map is contravariant and the target map covariant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Category MonoidalCategory MonoidalClosed Opposite BraidedCategory
open scoped MonoidalCategory

namespace CategoryTheory.ClosedPowerInterchange

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C]

/-- The existing internal currying isomorphisms, joined by the actual braiding. -/
def interchange (A D W : C) :
    (ihom A).obj ((ihom D).obj W) ≅ (ihom D).obj ((ihom A).obj W) :=
  (ihomCurryIso D A W).symm ≪≫
    ((internalHom.mapIso (β_ A D).op).app W) ≪≫ ihomCurryIso A D W

theorem interchange_hom (A D W : C) :
    (interchange A D W).hom = ihomUncurry D A W ≫
      (pre (β_ A D).hom).app W ≫ ihomCurry A D W := rfl

theorem interchange_inv (A D W : C) :
    (interchange A D W).inv = ihomUncurry A D W ≫
      (pre (β_ A D).inv).app W ≫ ihomCurry D A W := by
  change (ihomUncurry A D W ≫ (pre (β_ A D).inv).app W) ≫ ihomCurry D A W = _
  exact Category.assoc _ _ _

omit [BraidedCategory C] [MonoidalClosed C] in
private theorem move_swap {R S W : C} (A D : C) (f : R ⟶ S)
    (g : A ⊗ D ⟶ D ⊗ A) (h : (D ⊗ A) ⊗ S ⟶ W) :
    A ◁ (D ◁ f) ≫ (α_ A D S).inv ≫ g ▷ S ≫ h =
      (α_ A D R).inv ≫ g ▷ R ≫ (D ⊗ A) ◁ f ≫ h := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]

omit [BraidedCategory C] in
private theorem double_uncurry_native_swap {R : C} (A D W : C)
    (f : R ⟶ (ihom (D ⊗ A)).obj W) (g : A ⊗ D ⟶ D ⊗ A) :
    uncurry (uncurry (f ≫ (pre g).app W ≫ ihomCurry A D W)) =
      (α_ A D R).inv ≫ g ▷ R ≫ uncurry f := by
  calc
    _ = A ◁ (D ◁ f) ≫ (α_ A D ((ihom (D ⊗ A)).obj W)).inv ≫
        (A ⊗ D) ◁ (pre g).app W ≫ (ihom.ev (A ⊗ D)).app W := by
      simp only [uncurry_natural_left, uncurry_ihomCurry, uncurry_curry]
      rw [associator_inv_naturality_right_assoc]
    _ = A ◁ (D ◁ f) ≫ (α_ A D ((ihom (D ⊗ A)).obj W)).inv ≫
        g ▷ (ihom (D ⊗ A)).obj W ≫ (ihom.ev (D ⊗ A)).app W := by
      rw [id_tensor_pre_app_comp_ev]
    _ = (α_ A D R).inv ≫ g ▷ R ≫ (D ⊗ A) ◁ f ≫ (ihom.ev (D ⊗ A)).app W :=
      move_swap A D f g _
    _ = _ := by rw [uncurry_eq]

/-- The forward whole evaluation diagram, including both counits and all associators. -/
theorem interchange_hom_double_uncurry (A D W : C) :
    uncurry (uncurry (interchange A D W).hom) =
      (α_ A D ((ihom A).obj ((ihom D).obj W))).inv ≫
      ((β_ A D).hom ▷ (ihom A).obj ((ihom D).obj W)) ≫
      (α_ D A ((ihom A).obj ((ihom D).obj W))).hom ≫
      (D ◁ (ihom.ev A).app ((ihom D).obj W)) ≫ (ihom.ev D).app W := by
  have h := double_uncurry_native_swap A D W (ihomUncurry D A W) (β_ A D).hom
  rw [uncurry_ihomUncurry] at h
  exact h

/-- The inverse uses the genuine inverse braiding and the reverse two counits. -/
theorem interchange_inv_double_uncurry (A D W : C) :
    uncurry (uncurry (interchange A D W).inv) =
      (α_ D A ((ihom D).obj ((ihom A).obj W))).inv ≫
      ((β_ A D).inv ▷ (ihom D).obj ((ihom A).obj W)) ≫
      (α_ A D ((ihom D).obj ((ihom A).obj W))).hom ≫
      (A ◁ (ihom.ev D).app ((ihom A).obj W)) ≫ (ihom.ev A).app W := by
  have h := double_uncurry_native_swap D A W (ihomUncurry A D W) (β_ A D).inv
  rw [uncurry_ihomUncurry] at h
  rw [interchange_inv]
  exact h

omit [BraidedCategory C] in
private theorem nested_evaluation_target (A D : C) {W V : C} (f : W ⟶ V) :
    (D ◁ (A ◁ (ihom A).map ((ihom D).map f))) ≫
      (D ◁ (ihom.ev A).app ((ihom D).obj V)) ≫ (ihom.ev D).app V =
    (D ◁ (ihom.ev A).app ((ihom D).obj W)) ≫ (ihom.ev D).app W ≫ f := by
  rw [← whiskerLeft_comp_assoc, ihom.ev_naturality,
    whiskerLeft_comp, Category.assoc, ihom.ev_naturality]

omit [BraidedCategory C] in
private theorem nested_evaluation_coefficient (A : C) {D D' : C}
    (g : D' ⟶ D) (W : C) :
    (D' ◁ (A ◁ (ihom A).map ((pre g).app W))) ≫
      (D' ◁ (ihom.ev A).app ((ihom D').obj W)) ≫ (ihom.ev D').app W =
    (g ▷ (A ⊗ (ihom A).obj ((ihom D).obj W))) ≫
      (D ◁ (ihom.ev A).app ((ihom D).obj W)) ≫ (ihom.ev D).app W := by
  rw [← whiskerLeft_comp_assoc, ihom.ev_naturality,
    whiskerLeft_comp, Category.assoc, id_tensor_pre_app_comp_ev]
  exact whisker_exchange_assoc g ((ihom.ev A).app ((ihom D).obj W)) ((ihom.ev D).app W)

omit [BraidedCategory C] in
private theorem double_uncurry_pre {A D W R S : C} (f : R ⟶ S)
    (r : S ⟶ (ihom D).obj ((ihom A).obj W)) :
    uncurry (uncurry (f ≫ r)) = A ◁ (D ◁ f) ≫ uncurry (uncurry r) := by
  rw [uncurry_natural_left, uncurry_natural_left]

omit [BraidedCategory C] in
private theorem double_uncurry_target {A D W V R : C}
    (r : R ⟶ (ihom D).obj ((ihom A).obj W)) (f : W ⟶ V) :
    uncurry (uncurry (r ≫ (ihom D).map ((ihom A).map f))) =
      uncurry (uncurry r) ≫ f := by
  rw [uncurry_natural_right, uncurry_natural_right]

omit [BraidedCategory C] in
private theorem double_uncurry_coefficient {A D D' W R : C}
    (r : R ⟶ (ihom D).obj ((ihom A).obj W)) (g : D' ⟶ D) :
    uncurry (uncurry (r ≫ (pre g).app ((ihom A).obj W))) =
      A ◁ (g ▷ R) ≫ uncurry (uncurry r) := by
  rw [uncurry_pre_app, uncurry_natural_left]

/-- Every target map commutes with the same whole interchange. -/
theorem interchange_target_naturality (A D : C) {W V : C} (f : W ⟶ V) :
    (ihom A).map ((ihom D).map f) ≫ (interchange A D V).hom =
      (interchange A D W).hom ≫ (ihom D).map ((ihom A).map f) := by
  apply uncurry_injective
  apply uncurry_injective
  have hL := double_uncurry_pre
    ((ihom A).map ((ihom D).map f)) (interchange A D V).hom
  have hR := double_uncurry_target (interchange A D W).hom f
  refine hL.trans (Eq.trans ?_ hR.symm)
  simp only [interchange_hom_double_uncurry, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, nested_evaluation_target]


/-- Every original coefficient restriction retains its actual contravariant direction. -/
theorem interchange_coefficient_naturality (A : C) {D D' : C} (g : D' ⟶ D) (W : C) :
    (ihom A).map ((pre g).app W) ≫ (interchange A D' W).hom =
      (interchange A D W).hom ≫ (pre g).app ((ihom A).obj W) := by
  apply uncurry_injective
  apply uncurry_injective
  have hL := double_uncurry_pre
    ((ihom A).map ((pre g).app W)) (interchange A D' W).hom
  have hR := double_uncurry_coefficient (interchange A D W).hom g
  refine hL.trans (Eq.trans ?_ hR.symm)
  simp only [interchange_hom_double_uncurry]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, nested_evaluation_coefficient]
  rw [← associator_naturality_left_assoc, ← comp_whiskerRight_assoc,
    ← braiding_naturality_right, comp_whiskerRight_assoc,
    ← associator_inv_naturality_middle_assoc]


/-- The inverse target square follows from the forward square and native Iso identities. -/
theorem interchange_inv_target_naturality (A D : C) {W V : C} (f : W ⟶ V) :
    (ihom D).map ((ihom A).map f) ≫ (interchange A D V).inv =
      (interchange A D W).inv ≫ (ihom A).map ((ihom D).map f) := by
  exact CommSq.w <| .vert_inv <| .mk (interchange_target_naturality A D f)

/-- The inverse coefficient square uses the same coefficient map, never its reversed variance. -/
theorem interchange_inv_coefficient_naturality (A : C) {D D' : C}
    (g : D' ⟶ D) (W : C) :
    (pre g).app ((ihom A).obj W) ≫ (interchange A D' W).inv =
      (interchange A D W).inv ≫ (ihom A).map ((pre g).app W) := by
  exact CommSq.w <| .vert_inv <| .mk (interchange_coefficient_naturality A g W)

end CategoryTheory.ClosedPowerInterchange
