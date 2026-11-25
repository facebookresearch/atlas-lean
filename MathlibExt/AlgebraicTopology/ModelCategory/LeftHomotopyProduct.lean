/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Actual left homotopies into an original binary product

Two homotopies on the same cylinder give their literal product lift.
For a cofibrant source, two arbitrary projected homotopies are combined
by varying one component at a time. This uses the original cylinder
projection and homotopy composition, without a Cartesian model axiom.
-/

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {X Y Z : C} [HasBinaryProduct Y Z]

/-- The literal product of two actual homotopies on the SAME original cylinder. -/
def Cylinder.LeftHomotopy.prod {P : Cylinder X} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : X ⟶ Z}
    (h : P.LeftHomotopy f₀ f₁) (k : P.LeftHomotopy g₀ g₁) :
    P.LeftHomotopy (prod.lift f₀ g₀) (prod.lift f₁ g₁) where
  h := prod.lift h.h k.h
  h₀ := by rw [prod.comp_lift, h.h₀, k.h₀]
  h₁ := by rw [prod.comp_lift, h.h₁, k.h₁]

/-- Both complete original projection legs of the SAME product homotopy are retained. -/
theorem Cylinder.LeftHomotopy.prod_fst {P : Cylinder X} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : X ⟶ Z}
    (h : P.LeftHomotopy f₀ f₁) (k : P.LeftHomotopy g₀ g₁) :
    (h.prod k).h ≫ prod.fst = h.h := prod.lift_fst _ _

/-- The complete second original projection of the SAME product homotopy is retained. -/
theorem Cylinder.LeftHomotopy.prod_snd {P : Cylinder X} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : X ⟶ Z}
    (h : P.LeftHomotopy f₀ f₁) (k : P.LeftHomotopy g₀ g₁) :
    (h.prod k).h ≫ prod.snd = k.h := prod.lift_snd _ _

/-- Arbitrary original component homotopies combine through actual constant components and
composition. -/
theorem LeftHomotopyRel.prod_lift [IsCofibrant X] {f₀ f₁ : X ⟶ Y} {g₀ g₁ : X ⟶ Z}
    (h : LeftHomotopyRel f₀ f₁) (k : LeftHomotopyRel g₀ g₁) :
    LeftHomotopyRel (prod.lift f₀ g₀) (prod.lift f₁ g₁) := by
  obtain ⟨P, ⟨h⟩⟩ := h
  obtain ⟨Q, ⟨k⟩⟩ := k
  exact (h.prod (Cylinder.LeftHomotopy.refl P g₀)).leftHomotopyRel.trans
    (((Cylinder.LeftHomotopy.refl Q f₁).prod k).leftHomotopyRel)

/-- At a genuine cofibrant source, the original product homotopy relation is exactly both original
projections. -/
theorem LeftHomotopyRel.prod_iff [IsCofibrant X] (f g : X ⟶ Y ⨯ Z) :
    LeftHomotopyRel f g ↔
      LeftHomotopyRel (f ≫ prod.fst) (g ≫ prod.fst) ∧
        LeftHomotopyRel (f ≫ prod.snd) (g ≫ prod.snd) := by
  constructor
  · intro h
    exact ⟨h.postcomp prod.fst, h.postcomp prod.snd⟩
  · rintro ⟨h, k⟩
    simpa only [← prod.comp_lift, prod.lift_fst_snd, Category.comp_id] using h.prod_lift k

end HomotopicalAlgebra
