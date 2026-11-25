/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenRightMateWeak

/-!
# Genuine model weak recognition by right homotopy classes

Between bifibrant objects, precomposition on the actual model homotopy
classes detects weakness. The inverse is constructed from the original
class tests and the canonical model Whitehead argument; the existing
factorization/lifting weak-inverse theorem proves weakness.
-/

noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Original precomposition class tests at every genuine fibrant target detect weak maps between
bifibrant objects. -/
theorem weakEquivalence_iff_rightHomotopyClass_precomp_bijective
    {X Y : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence f ↔ ∀ (Z : C) [IsFibrant Z],
      Function.Bijective (fun g : RightHomotopyClass Y Z => g.precomp f) := by
  constructor
  · intro hf Z _
    let _ : WeakEquivalence f := hf
    exact RightHomotopyClass.precomp_bijective_of_weakEquivalence Z f
  · intro h
    obtain ⟨g, hg⟩ := (h X).surjective (RightHomotopyClass.mk (𝟙 X))
    obtain ⟨g, rfl⟩ := g.mk_surjective
    dsimp at hg
    have hfg : RightHomotopyRel (f ≫ g) (𝟙 X) := by
      rwa [← RightHomotopyClass.mk_eq_mk_iff]
    have hgf : RightHomotopyRel (g ≫ f) (𝟙 Y) := by
      rw [← RightHomotopyClass.mk_eq_mk_iff]
      apply (h Y).injective
      simp only [RightHomotopyClass.precomp_mk, Category.comp_id]
      rw [RightHomotopyClass.mk_eq_mk_iff, ← leftHomotopyRel_iff_rightHomotopyRel] at hg ⊢
      simpa using hg.postcomp f
    exact weakEquivalence_of_rightHomotopyInverse f g hfg hgf

end HomotopicalAlgebra
