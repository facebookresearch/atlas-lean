/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentModelTransport

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
variable (E : C ≌ D) [E.functor.Additive]

example : SInverseS.ZeroComponent (C := C) ≌ SInverseS.ZeroComponent (C := D) :=
  SInverseS.zeroComponentEquivalence E

example :
    (SInverseS.zeroComponentEquivalence E).functor.obj
        (SInverseS.zeroComponentBaseObject (C := C)) ≅
      SInverseS.zeroComponentBaseObject (C := D) :=
  SInverseS.zeroComponentEquivalencePointIso E

example :
    (SInverseS.zeroComponentEquivalence E).functor ⋙
        (SInverseS.zeroComponentProperty (C := D)).ι ≅
      (SInverseS.zeroComponentProperty (C := C)).ι ⋙ (SInverseS.pairEquivalence E).functor :=
  SInverseS.zeroComponentEquivalenceInclusionIso E

end
