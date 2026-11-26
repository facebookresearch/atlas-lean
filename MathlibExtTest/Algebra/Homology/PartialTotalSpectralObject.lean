/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalSpectralObject

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example : EInt ⥤ CochainComplex C ℤ :=
  B.partialTotalCochainFiltration

example : CategoryTheory.Abelian.SpectralObject C EInt :=
  B.partialTotalSpectralObject

example (q : ℕ) :
    ((B.partialTotalSpectralObject.H
      ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
        (0, q))).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE
          ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).le₁₂
            (0, q))))) ≅
      (CochainComplex.mappingCone
        (B.partialTotalCochainFiltration.map
          (homOfLE
            ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).le₁₂
              (0, q))))).homology
        ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
          (0, q)) :=
  B.partialTotalSpectralObjectHObjIso _ _

example (m q : ℕ) :
    ((B.partialTotalSpectralObject.H
      ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
        (m + 1, q))).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE
          ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).le₁₂
            (m + 1, q))))) ≅
      (CochainComplex.mappingCone
        (B.partialTotalCochainFiltration.map
          (homOfLE
            ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).le₁₂
              (m + 1, q))))).homology
        ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
          (m + 1, q)) :=
  B.partialTotalSpectralObjectHObjIso _ _

end HomologicalComplex₂

end
