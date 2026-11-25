/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralObject

/-! # Tests for the first-quadrant filtration spectral object -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

universe v u

namespace HomologicalComplex₂.FirstQuadrantSpectralObjectTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example : ℕ ⥤ CochainComplex C ℤ :=
  horizontalFiltrationCochainDiagram K

example : CategoryTheory.Triangulated.SpectralObject
    (HomotopyCategory C (ComplexShape.up ℤ)) ℕ :=
  horizontalFiltrationTriangulatedSpectralObject K

example {k l : ℕ} (h : k ≤ l) :
    (horizontalFiltrationTriangulatedSpectralObject K).ω₁.obj
        (ComposableArrows.mk₁ (homOfLE h)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone
          ((horizontalFiltrationCochainDiagram K).map (homOfLE h))) :=
  horizontalFiltrationTriangulatedSpectralObject_ω₁_obj K h

end HomologicalComplex₂.FirstQuadrantSpectralObjectTests

namespace HomologicalComplex₂.FirstQuadrantSpectralObjectTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example : CategoryTheory.Abelian.SpectralObject C ℕ :=
  horizontalFiltrationSpectralObject K

example {i j k : ℕ} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    ((horizontalFiltrationSpectralObject K).sc₂
      f g (f ≫ g) rfl n).Exact :=
  (horizontalFiltrationSpectralObject K).exact₂ f g (f ≫ g) rfl n

end HomologicalComplex₂.FirstQuadrantSpectralObjectTests

end
