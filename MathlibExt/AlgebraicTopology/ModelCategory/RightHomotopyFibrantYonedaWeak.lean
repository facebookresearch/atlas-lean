/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.RightHomotopyClassWeakPostcomp
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenRightMateWeak
import Mathlib.AlgebraicTopology.ModelCategory.CofibrantObjectHomotopy

/-!
# Genuine fibrant-target weak recognition by original model classes

Actual postcomposition on right homotopy classes from every cofibrant
source recognizes weakness between the original fibrant targets. The
canonical cofibrant resolutions, their actual weak maps and their
original lifted map reduce to the bifibrant Whitehead argument. No
cofibrancy of the original targets or inverse outcome is assumed.
-/

noncomputable section
universe u v
open CategoryTheory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Actual original postcomposition tests recognize weak maps between bifibrant targets. -/
theorem weakEquivalence_iff_rightHomotopyClass_postcomp_bijective
    {X Y : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence f ↔ ∀ (Z : C) [IsCofibrant Z],
      Function.Bijective (fun g : RightHomotopyClass Z X => g.postcompOfCofibrant f) := by
  constructor
  · intro hf Z _
    let _ : WeakEquivalence f := hf
    exact RightHomotopyClass.postcompOfCofibrant_bijective_of_weakEquivalence f
  · intro h
    obtain ⟨g, hg⟩ := (h Y).surjective (RightHomotopyClass.mk (𝟙 Y))
    obtain ⟨g, rfl⟩ := g.mk_surjective
    have hgf : RightHomotopyRel (g ≫ f) (𝟙 Y) := by
      rw [← RightHomotopyClass.mk_eq_mk_iff]
      exact hg
    have hfg : RightHomotopyRel (f ≫ g) (𝟙 X) := by
      rw [← RightHomotopyClass.mk_eq_mk_iff]
      apply (h X).injective
      change RightHomotopyClass.mk ((f ≫ g) ≫ f) = RightHomotopyClass.mk ((𝟙 X) ≫ f)
      apply RightHomotopyClass.sound
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using hgf.precomp f
    exact weakEquivalence_of_rightHomotopyInverse f g hfg hgf

/-- With only original target fibrancy, actual postcomposition tests from all cofibrant sources
recognize the SAME
original weak map. -/
theorem weakEquivalence_iff_rightHomotopyClass_postcomp_bijective_of_fibrant
    {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence f ↔ ∀ (Z : C) [IsCofibrant Z],
      Function.Bijective (fun g : RightHomotopyClass Z X => g.postcompOfCofibrant f) := by
  constructor
  · intro hf Z _
    let _ : WeakEquivalence f := hf
    exact RightHomotopyClass.postcompOfCofibrant_bijective_of_weakEquivalence f
  · intro h
    let X' := CofibrantObject.HoCat.resolutionObj X
    let Y' := CofibrantObject.HoCat.resolutionObj Y
    let f' : X' ⟶ Y' := CofibrantObject.HoCat.resolutionMap f
    have hf' : WeakEquivalence f' :=
      (weakEquivalence_iff_rightHomotopyClass_postcomp_bijective f').mpr (by
        intro Z _
        let qX := CofibrantObject.HoCat.pResolutionObj X
        let qY := CofibrantObject.HoCat.pResolutionObj Y
        have hX := RightHomotopyClass.postcompOfCofibrant_bijective_of_weakEquivalence (X := Z) qX
        have hY := RightHomotopyClass.postcompOfCofibrant_bijective_of_weakEquivalence (X := Z) qY
        have he (a : RightHomotopyClass Z X') :
            (a.postcompOfCofibrant f').postcompOfCofibrant qY =
              (a.postcompOfCofibrant qX).postcompOfCofibrant f := by
          induction a using Quot.inductionOn with
          | _ a =>
            change RightHomotopyClass.mk ((a ≫ f') ≫ qY) = RightHomotopyClass.mk ((a ≫ qX) ≫ f)
            apply congrArg RightHomotopyClass.mk
            exact (Category.assoc _ _ _).trans
              ((congrArg (fun t => a ≫ t) (CofibrantObject.HoCat.resolutionMap_fac f)).trans
                (Category.assoc _ _ _).symm)
        have hCombined := (h Z).comp hX
        constructor
        · intro a b hab
          apply hCombined.injective
          exact (he a).symm.trans ((congrArg (fun t => t.postcompOfCofibrant qY) hab).trans (he b))
        · intro b
          obtain ⟨a, ha⟩ := hCombined.surjective (b.postcompOfCofibrant qY)
          exact ⟨a, hY.injective ((he a).trans ha)⟩)
    exact (CofibrantObject.HoCat.weakEquivalence_resolutionMap_iff f).mp hf'

end HomotopicalAlgebra
