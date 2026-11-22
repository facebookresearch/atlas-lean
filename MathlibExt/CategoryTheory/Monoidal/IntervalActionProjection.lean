/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.IntervalAction
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Projection maps of transported and tensored interval actions

Original source maps and endpoint/cocone equations are retained. These
constructions supply the categorical source framework used in MMSS
Definition 6.8 and its cone, cylinder and homotopy-pushout applications.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory
open MonoidalCategory

namespace CategoryTheory.Functor.CoreMonoidal

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- A strong monoidal image retains the full projection of the actual interval action. -/
theorem intervalActionImage_collapse (F : C ⥤ D) (hF : F.CoreMonoidal)
    {T J : C} (H : T ⊗ J ⟶ J) (cT : T ⟶ 𝟙_ C) (cJ : J ⟶ 𝟙_ C)
    (h : H ≫ cJ = (cT ⊗ₘ cJ) ≫ (λ_ (𝟙_ C)).hom) :
    intervalActionImage F hF H ≫ intervalCollapseImage F hF cJ =
      (intervalCollapseImage F hF cT ⊗ₘ intervalCollapseImage F hF cJ) ≫
        (λ_ (𝟙_ D)).hom := by
  have hUnit : (hF.μIso (𝟙_ C) (𝟙_ C)).hom ≫ F.map (λ_ (𝟙_ C)).hom =
      hF.εIso.inv ▷ F.obj (𝟙_ C) ≫ (λ_ (F.obj (𝟙_ C))).hom := by
    have hu := congrArg
      (fun f : 𝟙_ D ⊗ F.obj (𝟙_ C) ⟶ F.obj (𝟙_ C) =>
        hF.εIso.inv ▷ F.obj (𝟙_ C) ≫ f) (hF.left_unitality (𝟙_ C))
    simpa only [Category.assoc, inv_hom_whiskerRight_assoc] using hu.symm
  have hTensor : (hF.μIso T J).hom ≫ F.map (cT ⊗ₘ cJ) =
      (F.map cT ⊗ₘ F.map cJ) ≫ (hF.μIso (𝟙_ C) (𝟙_ C)).hom := by
    rw [tensorHom_def, F.map_comp, ← Category.assoc,
      ← hF.μIso_hom_natural_left, Category.assoc,
      ← hF.μIso_hom_natural_right, ← Category.assoc, ← tensorHom_def]
  change ((hF.μIso T J).hom ≫ F.map H) ≫ (F.map cJ ≫ hF.εIso.inv) =
    ((F.map cT ≫ hF.εIso.inv) ⊗ₘ (F.map cJ ≫ hF.εIso.inv)) ≫ (λ_ (𝟙_ D)).hom
  calc
    _ = (hF.μIso T J).hom ≫ F.map (H ≫ cJ) ≫ hF.εIso.inv := by
      rw [F.map_comp]; simp only [Category.assoc]
    _ = (hF.μIso T J).hom ≫ F.map (cT ⊗ₘ cJ) ≫
        F.map (λ_ (𝟙_ C)).hom ≫ hF.εIso.inv := by
      rw [h, F.map_comp]; simp only [Category.assoc]
    _ = (F.map cT ⊗ₘ F.map cJ) ≫ (hF.μIso (𝟙_ C) (𝟙_ C)).hom ≫
        F.map (λ_ (𝟙_ C)).hom ≫ hF.εIso.inv := by
      rw [← Category.assoc ((hF.μIso T J).hom), hTensor]
      simp only [Category.assoc]
    _ = (F.map cT ⊗ₘ F.map cJ) ≫ hF.εIso.inv ▷ F.obj (𝟙_ C) ≫
        (λ_ (F.obj (𝟙_ C))).hom ≫ hF.εIso.inv := by
      rw [← Category.assoc ((hF.μIso (𝟙_ C) (𝟙_ C)).hom), hUnit]
      simp only [Category.assoc]
    _ = (F.map cT ⊗ₘ F.map cJ) ≫ (hF.εIso.inv ⊗ₘ hF.εIso.inv) ≫
        (λ_ (𝟙_ D)).hom := by
      rw [← leftUnitor_naturality, ← Category.assoc (hF.εIso.inv ▷ F.obj (𝟙_ C)),
        ← tensorHom_def]
    _ = _ := by rw [← Category.assoc, tensorHom_comp_tensorHom]

end CategoryTheory.Functor.CoreMonoidal

namespace CategoryTheory.MonoidalCategory

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]

/-- Tensoring an actual interval action retains the original full projection map. -/
theorem tensorIntervalMap_projection {T J : C} (H : T ⊗ J ⟶ J)
    (cT : T ⟶ 𝟙_ C) (cJ : J ⟶ 𝟙_ C)
    (h : H ≫ cJ = (cT ⊗ₘ cJ) ≫ (λ_ (𝟙_ C)).hom) (X : C) :
    tensorIntervalMap H X ≫ (cJ ▷ X) =
      (cT ▷ (J ⊗ X) ≫ (λ_ (J ⊗ X)).hom) ≫ (cJ ▷ X) := by
  have hu : (𝟙_ C ◁ cJ) ▷ X ≫ (λ_ (𝟙_ C)).hom ▷ X =
      (λ_ J).hom ▷ X ≫ cJ ▷ X := by
    rw [← comp_whiskerRight, leftUnitor_naturality, comp_whiskerRight]
  rw [tensorIntervalMap, tensorHom_id]
  rw [Category.assoc, ← comp_whiskerRight, h, comp_whiskerRight, tensorHom_def,
    comp_whiskerRight]
  calc
    _ = cT ▷ (J ⊗ X) ≫ (α_ (𝟙_ C) J X).inv ≫
        ((𝟙_ C ◁ cJ) ▷ X ≫ (λ_ (𝟙_ C)).hom ▷ X) := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ (𝟙_ C ◁ cJ) ▷ X ≫ (λ_ (𝟙_ C)).hom ▷ X)
        (associator_inv_naturality_left cT J X).symm
    _ = cT ▷ (J ⊗ X) ≫ (α_ (𝟙_ C) J X).inv ≫
        (λ_ J).hom ▷ X ≫ cJ ▷ X := by rw [hu]
    _ = _ := by rw [leftUnitor_tensor_hom]; simp only [Category.assoc]

end CategoryTheory.MonoidalCategory
