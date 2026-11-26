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

public import MathlibExt.Algebra.Homology.HomotopyCategory.MappingConeCompShortComplex
public import MathlibExt.Algebra.Homology.PartialTotalConnectingDifferential
public import MathlibExt.Algebra.Homology.PartialTotalFirstPageDifferential

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

universe v u

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]

example (S : ShortComplex (CochainComplex C ℤ))
    {X : CochainComplex C ℤ} (g : S.X₂ ⟶ X) :
    (CochainComplex.mappingConeCompTriangle S.f g).mor₃ ≫
        (descShortComplex S)⟦(1 : ℤ)⟧' =
      (triangle g).mor₃ ≫ S.g⟦(1 : ℤ)⟧' :=
  mappingConeCompTriangle_mor₃_comp_descShortComplex_shift S g

end CochainComplex.mappingCone

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (m : ℕ) :
    let S := B.partialTotalStepCochainShortComplex m
    let g := (B.partialTotalAdjacentStepCochainIso m).inv ≫
      (B.partialTotalStepCochainShortComplex (m + 1)).f
    (CochainComplex.mappingConeCompTriangle S.f g).mor₃ ≫
        (CochainComplex.mappingCone.descShortComplex S)⟦(1 : ℤ)⟧' =
      (CochainComplex.mappingCone.triangle g).mor₃ ≫ S.g⟦(1 : ℤ)⟧' :=
  CochainComplex.mappingCone.mappingConeCompTriangle_mor₃_comp_descShortComplex_shift _ _

example (q : ℕ) (pq' : ℕ × ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).page 1).d
        (0, q) pq' = 0 :=
  B.partialTotalSpectralSequenceFirstPage_d_zero q pq'

end HomologicalComplex₂

end
