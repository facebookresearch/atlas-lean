/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.MappingConeCokernelConnecting

/-! # Tests for mapping-cone and cokernel connecting morphisms -/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CochainComplex.mappingCone.MappingConeCokernelConnectingTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B D : CochainComplex C ℤ}
  (f : A ⟶ B) (g : B ⟶ D)

example : mappingCone f ≅ mappingCone f :=
  isoOfHomEq rfl

example :
    compTriangleToCokernelCone f g ≫
        descShortComplex (CategoryTheory.cokernelCompShortComplex f g) =
      descShortComplex (ShortComplex.cokernelSequence g) :=
  compTriangleToCokernelCone_desc f g

example [Mono g] (n n' : ℤ) (h : n + 1 = n') :
    ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
          (mappingConeCompTriangle f g)) n n' h) ≫
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) n').hom.app (mappingCone f) ≫
      HomologicalComplex.homologyMap
        (descShortComplex (ShortComplex.cokernelSequence f)) n' =
    (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) n).hom.app (mappingCone g) ≫
      HomologicalComplex.homologyMap
        (descShortComplex (ShortComplex.cokernelSequence g)) n ≫
      (CategoryTheory.cokernelCompShortComplex_shortExact f g).δ n n' h :=
  homologySequenceδ_cokernelComp f g n n' h

end CochainComplex.mappingCone.MappingConeCokernelConnectingTests

end
