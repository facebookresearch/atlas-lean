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

public import MathlibExt.Algebra.Homology.HomotopyCategory.MappingConeCompHomology
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
    {X : CochainComplex C ℤ} (g : S.X₂ ⟶ X)
    (n n' : ℤ) (h : n + 1 = n') :
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh S.f g) n n' h ≫
      (HomotopyCategory.homologyFunctorFactors
        C (ComplexShape.up ℤ) n').hom.app (CochainComplex.mappingCone S.f) ≫
      HomologicalComplex.homologyMap (descShortComplex S) n' =
    (HomotopyCategory.homologyFunctorFactors
      C (ComplexShape.up ℤ) n).hom.app (CochainComplex.mappingCone g) ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (triangle g).mor₃ n n' (by omega) ≫
      HomologicalComplex.homologyMap S.g n' :=
  homologySequenceδ_mappingConeCompTriangleh_comp_descShortComplex S g n n' h

end CochainComplex.mappingCone

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (m q : ℕ) :
    (B.totalRow (m + 1)).homology (m + 1 + q) ⟶
      (B.totalRow m).homology (m + q) :=
  B.partialTotalE₁ConnectingDifferential m q

example (q : ℕ) (pq' : ℕ × ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).page 1).d
        (0, q) pq' = 0 :=
  B.partialTotalSpectralSequenceFirstPage_d_zero q pq'

end HomologicalComplex₂

end
